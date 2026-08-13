// trust-cg-opt - Proof-consuming optimizations
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Proof-consuming optimization pass for Trust Codegen.
//!
//! This module retains the structural model for proof-guided optimization.  Public trust_ir and
//! machine-IR annotations are producer-owned labels, however, so production keeps the pass inert
//! until an independent validator issues an exact, obligation-bound replay capability.
//!
//! # Proof Types and Their Optimizations
//!
//! | Proof Annotation | Codegen Pattern Eliminated |
//! |------------------|---------------------------|
//! | `NoOverflow`/`NoSignedOverflow` | `adds/subs + signed overflow guard` → plain `add/sub` |
//! | `NoUnsignedOverflow` | `adds + b.hs` / `subs + b.lo` → plain `add/sub` |
//! | `InBounds`       | `TrapBoundsCheckExact base, idx, bound` → remove guard |
//! | `NotNull`        | `TrapNullIfZero ptr` → remove guard |
//! | `ValidBorrow`    | Refines memory aliasing (enables reordering) |
//! | `PositiveRefCount` | `retain + release` → remove pair |
//! | `NonZeroDivisor` | `cmp divisor, #0 + TrapDivZero` → remove guard |
//! | `ValidShift`     | `cmp amt, #64 + b.hs trap + lsl/lsr/asr` → plain shift |
//!
//! # Safety
//!
//! The transforms below are sound only when their preconditions have been independently replayed
//! and bound to the exact operation/operands/target semantics.  A `ProofAnnotation` alone is not
//! such evidence.  Consequently downstream/production builds apply none of these transforms; the
//! implementation remains executable under `cfg(test)` as the future replay consumer's structural
//! model.
//!
//! # Algorithm
//!
//! Single forward pass over each block's instruction list:
//! 1. For each instruction, check if it has a `ProofAnnotation`.
//! 2. If so, apply the corresponding pattern transformation.
//! 3. Track statistics for diagnostics.
//!
//! The pass also scans for multi-instruction patterns (e.g., ADDS followed
//! by TrapOverflow) where the proof annotation is on the first instruction
//! of the sequence.
//!
//! Reference: designs/2026-04-12-aarch64-backend.md, "Proof-Enabled Optimizations"

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64GuardTarget, AArch64Opcode, CondCode, DischargedEvidenceTable, EliminationCertificate,
    EliminationVerdict, GuardObligationReceipt, GuardOperandRef, GuardTarget, InstFlags, InstId,
    MachFunction, MachInst, MachOperand, PReg, PassId, ProofAnnotation, ProofDivergence, ProofFact,
    ProvenanceMap, RecheckOutcome, RegClass, SpecialReg, TrustIrInstId, VReg, decide,
    recheck_elimination,
};

use crate::cache::StableHasher;
use crate::interfaces::{ProofDiagnostic, ProofDiagnosticCode};
use crate::pass_manager::{AnalysisCache, MachinePass};

const PROOF_OPT_TRANSFORM_VERSION: u32 = 1;
const PROOF_OPT_PASS_NAME: &str = "proof-opts";

fn proof_opts_pass_id() -> PassId {
    PassId::new(PROOF_OPT_PASS_NAME)
}

fn bcond_has_condition(inst: &MachInst, condition: CondCode) -> bool {
    inst.opcode == AArch64Opcode::BCond
        && matches!(
            inst.operands.first(),
            Some(MachOperand::Imm(cond)) if *cond == i64::from(condition.encoding())
        )
}

fn bcond_is_signed_overflow_guard_for_opcode(inst: &MachInst, opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::AddsRR
            | AArch64Opcode::AddsRI
            | AArch64Opcode::SubsRR
            | AArch64Opcode::SubsRI
    ) && bcond_has_condition(inst, CondCode::VS)
}

fn unsigned_overflow_condition_for_opcode(opcode: AArch64Opcode) -> Option<CondCode> {
    match opcode {
        AArch64Opcode::AddsRR | AArch64Opcode::AddsRI => Some(CondCode::HS),
        AArch64Opcode::SubsRR | AArch64Opcode::SubsRI => Some(CondCode::LO),
        _ => None,
    }
}

fn bcond_is_unsigned_overflow_guard_for_opcode(inst: &MachInst, opcode: AArch64Opcode) -> bool {
    unsigned_overflow_condition_for_opcode(opcode)
        .is_some_and(|condition| bcond_has_condition(inst, condition))
}

/// Statistics collected during proof-consuming optimization.
#[derive(Debug, Clone, Default)]
pub struct ProofOptStats {
    /// Number of overflow checks eliminated (NoOverflow family).
    pub overflow_checks_eliminated: u32,
    /// Number of bounds checks eliminated (InBounds).
    pub bounds_checks_eliminated: u32,
    /// Number of null checks eliminated (NotNull).
    pub null_checks_eliminated: u32,
    /// Number of retain/release pairs eliminated (PositiveRefCount).
    pub refcount_pairs_eliminated: u32,
    /// Number of memory reordering opportunities enabled (ValidBorrow).
    pub alias_refinements: u32,
    /// Number of division-by-zero checks eliminated (NonZeroDivisor).
    pub divzero_checks_eliminated: u32,
    /// Number of shift-range checks eliminated (ValidShift).
    pub shift_checks_eliminated: u32,
    /// Number of loads promoted to pure for aggressive CSE (Pure).
    pub pure_cse_enabled: u32,
    /// Number of adjacent 64-bit memory pairs combined under Aligned(16) facts.
    pub pair_mem_ops_combined: u32,
    /// Total number of applied and rejected optimization certificates generated.
    pub total_certificates: u32,
}

/// A certificate recording a single proof-guided optimization candidate.
///
/// These certificates form an audit trail aligned with tRust's translation
/// validation patterns (trust-transval): each one records that a specific
/// trust_ir proof annotation and optional #794 proof facts were consumed to
/// eliminate a specific runtime check, or why a proof-present candidate was
/// rejected. Downstream verification (trust-cg-verify) can independently confirm
/// each applied certificate by re-checking the proof obligation.
#[derive(Debug, Clone)]
pub struct OptCertificate {
    /// Stable certificate identity for release/replay artifact references.
    pub certificate_id: u128,
    /// Stable transform identity.
    pub transform: OptTransformIdentity,
    /// Pass and admission route that allowed the candidate to be considered.
    pub route: OptAdmissionRoute,
    /// Legacy proof annotation that justified this optimization, when the
    /// transform is annotation-backed. Fact-only transforms leave this empty
    /// and record their proof inputs in `consumed_facts`.
    pub annotation: Option<ProofAnnotation>,
    /// Rich proof facts consumed alongside the legacy proof annotation.
    pub consumed_facts: Vec<OptConsumedProofFact>,
    /// Human-readable description of the transformation.
    pub description: String,
    /// The instruction ID that was the primary target.
    pub primary_inst: InstId,
    /// Additional instruction IDs affected (e.g., deleted trap instructions).
    pub affected_insts: Vec<InstId>,
    /// The kind of transformation applied.
    pub kind: OptCertificateKind,
    /// Stable hash of the source proof/trust_ir region represented by the candidate.
    pub source_region_hash: u128,
    /// Stable hash of the target AArch64/MachIR region after the candidate.
    pub target_region_hash: u128,
    /// Stable hash of the proof inputs consumed by this certificate.
    pub proof_hash: u128,
    /// Stable hash binding transform identity, region hashes, and result status.
    pub validation_hash: u128,
    /// Rejection metadata for proof-present candidates that were not applied.
    pub rejection: Option<OptRejection>,
}

/// What kind of transformation was applied.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OptCertificateKind {
    /// A checked instruction was replaced with an unchecked equivalent.
    /// E.g., ADDS -> ADD.
    CheckedToUnchecked,
    /// One or more guard instructions were deleted.
    /// E.g., TrapBoundsCheckExact removed.
    GuardEliminated,
    /// A conditional branch was replaced with an unconditional branch.
    /// E.g., CBNZ -> B.
    BranchSimplified,
    /// Instruction flags were refined to enable downstream optimization.
    /// E.g., PROOF_REORDERABLE added, or READS_MEMORY removed.
    FlagsRefined,
    /// An instruction pair was eliminated.
    /// E.g., Retain+Release removed.
    PairEliminated,
    /// Adjacent scalar memory operations were combined into one target pair op.
    /// E.g., LDR+LDR -> LDP or STR+STR -> STP.
    PairCombined,
}

/// Stable transform identity for a proof-guided optimization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OptTransformIdentity {
    pub name: String,
    pub version: u32,
}

/// Pass/admission route used when considering a proof-guided transform.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OptAdmissionRoute {
    pub pass: String,
    pub admission: String,
}

/// Proof input consumed by an optimization certificate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OptConsumedProofFact {
    /// Compatibility carrier for the legacy single proof annotation field.
    LegacyAnnotation(ProofAnnotation),
    /// Rich ay/TY proof fact from the #794 vocabulary.
    ProofFact(ProofFact),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ValidBorrowApplyResult {
    Applied,
    AlreadyRefined,
    NotMemory,
}

impl OptConsumedProofFact {
    /// Stable fact name for release/replay artifact references.
    pub fn stable_name(self) -> &'static str {
        match self {
            OptConsumedProofFact::LegacyAnnotation(annotation) => {
                proof_annotation_stable_name(annotation)
            }
            OptConsumedProofFact::ProofFact(fact) => fact.stable_name(),
        }
    }

    /// Stable payload text for payload-bearing facts.
    pub fn payload(self) -> Option<String> {
        match self {
            OptConsumedProofFact::LegacyAnnotation(_) => None,
            OptConsumedProofFact::ProofFact(ProofFact::Aligned(bytes)) => Some(bytes.to_string()),
            OptConsumedProofFact::ProofFact(ProofFact::BoundedLoop(bound)) => {
                Some(bound.to_string())
            }
            OptConsumedProofFact::ProofFact(ProofFact::DivergenceClass(divergence)) => {
                Some(proof_divergence_stable_name(divergence).to_string())
            }
            OptConsumedProofFact::ProofFact(_) => None,
        }
    }
}

/// Rejection metadata for a proof-present optimization candidate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OptRejection {
    pub code: ProofDiagnosticCode,
    pub fact: String,
    pub detail: String,
}

impl OptRejection {
    pub fn new(
        code: ProofDiagnosticCode,
        fact: impl Into<String>,
        detail: impl Into<String>,
    ) -> Self {
        Self {
            code,
            fact: fact.into(),
            detail: detail.into(),
        }
    }

    pub fn from_diagnostic(diagnostic: ProofDiagnostic) -> Self {
        Self::new(
            diagnostic.code,
            diagnostic.fact.to_string(),
            diagnostic.detail.to_string(),
        )
    }
}

/// Sidecar inputs used to seed proof optimization certificates from the real
/// boxed optimization pipeline.
#[derive(Debug, Clone, Default)]
pub struct ProofOptimizationMetadata {
    proof_facts: HashMap<InstId, Vec<ProofFact>>,
    source_region_hashes: HashMap<InstId, u128>,
    candidate_rejections: HashMap<InstId, OptRejection>,
}

impl ProofOptimizationMetadata {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_inst_proof_facts(mut self, inst_id: InstId, facts: Vec<ProofFact>) -> Self {
        self.set_inst_proof_facts(inst_id, facts);
        self
    }

    pub fn set_inst_proof_facts(&mut self, inst_id: InstId, facts: Vec<ProofFact>) {
        if facts.is_empty() {
            self.proof_facts.remove(&inst_id);
        } else {
            self.proof_facts.insert(inst_id, facts);
        }
    }

    pub fn inst_proof_facts(&self, inst_id: InstId) -> &[ProofFact] {
        self.proof_facts
            .get(&inst_id)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    pub fn proof_facts(&self) -> &HashMap<InstId, Vec<ProofFact>> {
        &self.proof_facts
    }

    pub fn with_source_region_hash(mut self, inst_id: InstId, hash: u128) -> Self {
        self.set_source_region_hash(inst_id, hash);
        self
    }

    pub fn set_source_region_hash(&mut self, inst_id: InstId, hash: u128) {
        self.source_region_hashes.insert(inst_id, hash);
    }

    pub fn with_disabled_candidate(
        mut self,
        inst_id: InstId,
        fact: &'static str,
        detail: &'static str,
    ) -> Self {
        self.disable_candidate(inst_id, fact, detail);
        self
    }

    pub fn disable_candidate(&mut self, inst_id: InstId, fact: &'static str, detail: &'static str) {
        self.candidate_rejections.insert(
            inst_id,
            OptRejection::from_diagnostic(ProofDiagnostic::disabled_candidate(fact, detail)),
        );
    }

    pub fn with_failed_product_gate(
        mut self,
        inst_id: InstId,
        fact: &'static str,
        detail: &'static str,
    ) -> Self {
        self.fail_product_gate(inst_id, fact, detail);
        self
    }

    pub fn fail_product_gate(&mut self, inst_id: InstId, fact: &'static str, detail: &'static str) {
        self.candidate_rejections.insert(
            inst_id,
            OptRejection::from_diagnostic(ProofDiagnostic::failed_product_gate(fact, detail)),
        );
    }

    pub fn set_candidate_rejection(&mut self, inst_id: InstId, rejection: OptRejection) {
        self.candidate_rejections.insert(inst_id, rejection);
    }

    pub fn clear_candidate_rejection(&mut self, inst_id: InstId) {
        self.candidate_rejections.remove(&inst_id);
    }

    pub fn clear(&mut self) {
        self.proof_facts.clear();
        self.source_region_hashes.clear();
        self.candidate_rejections.clear();
    }
}

struct AppliedCertificateDetails<'a> {
    affected_insts: Vec<InstId>,
    kind: OptCertificateKind,
    source_region_hash: u128,
    target_region: &'a [InstId],
}

struct RejectedCertificateDetails<'a, R> {
    source_region: &'a [InstId],
    kind: OptCertificateKind,
    reason: R,
}

struct CertificateBuild<'a> {
    annotation: ProofAnnotation,
    description: String,
    primary_inst: InstId,
    affected_insts: Vec<InstId>,
    kind: OptCertificateKind,
    source_region_hash: u128,
    target_region: &'a [InstId],
    rejection: Option<OptRejection>,
}

/// Proof-consuming optimization pass.
///
/// Consumes trust_ir proof annotations to eliminate runtime safety checks
/// that have been formally verified as unnecessary.
pub struct ProofOptimization {
    stats: ProofOptStats,
    certificates: Vec<OptCertificate>,
    proof_facts: HashMap<InstId, Vec<ProofFact>>,
    source_region_hashes: HashMap<InstId, u128>,
    candidate_rejections: HashMap<InstId, OptRejection>,
    /// Sentinel S4 — when enabled, a guard carrier may be deleted ONLY if the arch-neutral
    /// Certified-Elimination Kernel returns Eliminate for it. Production construction enables the
    /// gate with empty authority; unit-test construction retains the legacy structural model.
    kernel_gate: bool,
    /// Discharged-obligation evidence the kernel consults (built from trust-ir; see
    /// `trust_cg_lower::guard_evidence`). Empty by default.
    kernel_evidence: DischargedEvidenceTable,
    /// Per-carrier binding: carrier `InstId` -> (obligation id, lineage digest) threaded from the
    /// frontend/adapter. A carrier absent from this map has no bound obligation, so the kernel
    /// keeps it.
    kernel_obligations: HashMap<InstId, (u128, Option<u128>)>,
    /// Eliminations the kernel authorized this run, recorded for the independent re-check
    /// ([`ProofOptimization::recheck_kernel_eliminations`]): (carrier InstId, certificate). The
    /// re-check re-reads the LIVE carrier operands from `func` via an INDEPENDENT lift (not the
    /// decide-time identity), so a genuine operand drift is rejected fail-closed (#9).
    kernel_eliminations: Vec<(InstId, EliminationCertificate)>,
    /// Independently re-lifted operand snapshots for each authorized elimination, indexed in
    /// lockstep with `kernel_eliminations`. Captured by a SECOND lift from the live carrier at the
    /// end of `run_impl` (after deletion-by-retain; `func.insts` retains the inst data), so the
    /// re-check's fingerprint comparison is non-vacuous. See `recheck_kernel_eliminations`.
    kernel_observed_operands: Vec<Vec<GuardOperandRef>>,
}

impl ProofOptimization {
    /// Create a new proof optimization pass.
    pub fn new() -> Self {
        Self {
            stats: ProofOptStats::default(),
            certificates: Vec::new(),
            proof_facts: HashMap::new(),
            source_region_hashes: HashMap::new(),
            candidate_rejections: HashMap::new(),
            // A direct public constructor must not be an authority bypass.  `cfg(test)` retains the
            // legacy label-only model solely for in-crate structural tests; downstream/integration
            // builds are production builds and start fail-closed.
            kernel_gate: !cfg!(test),
            kernel_evidence: DischargedEvidenceTable::new(),
            kernel_obligations: HashMap::new(),
            kernel_eliminations: Vec::new(),
            kernel_observed_operands: Vec::new(),
        }
    }

    /// Sentinel S4 — enable kernel-gated guard elimination: a carrier is deleted only when
    /// [`trust_cg_ir::decide`] authorizes it against `evidence` and the carrier's bound obligation.
    /// `obligations` maps a carrier `InstId` to its (obligation id, lineage digest).
    pub fn enable_kernel_gate(
        &mut self,
        evidence: DischargedEvidenceTable,
        obligations: HashMap<InstId, (u128, Option<u128>)>,
    ) {
        self.kernel_gate = true;
        if trust_cg_lower::guard_evidence::validator_guard_replay_authority_available()
            || trust_cg_lower::lattice_guard::lattice_guard_replay_authority_available()
            || cfg!(test)
        {
            // Structural kernel-model tests exercise the future authorization path. Production can
            // enter this branch only after an exact validator replay carrier replaces the unwired
            // policy seam.
            self.kernel_evidence = evidence;
            self.kernel_obligations = obligations;
        } else {
            // Public callers cannot turn a constructible table/map into behavior authority.
            self.kernel_evidence = DischargedEvidenceTable::new();
            self.kernel_obligations.clear();
        }
    }

    /// The kernel eliminations authorized during the last run (for the independent re-checker):
    /// (carrier InstId, certificate).
    pub fn kernel_eliminations(&self) -> &[(InstId, EliminationCertificate)] {
        &self.kernel_eliminations
    }

    /// Ask the Certified-Elimination Kernel whether a carrier may be deleted. Returns the minted
    /// certificate on Eliminate, or `None` on Keep. Records authorized eliminations for re-check.
    /// Only consulted when [`ProofOptimization::kernel_gate`] is set.
    fn kernel_authorizes(
        &mut self,
        func: &MachFunction,
        inst_id: InstId,
    ) -> Option<EliminationCertificate> {
        let target = AArch64GuardTarget;
        let inst = func.inst(inst_id);
        let kind = target.classify_carrier(inst)?;
        let operand_identity = target.operand_identity(inst);
        let (proof_obligation_id, lineage_digest) = match self.kernel_obligations.get(&inst_id) {
            Some(&(obl, lineage)) => (Some(obl), lineage),
            None => (None, None),
        };
        let receipt = GuardObligationReceipt {
            kind,
            operand_identity: operand_identity.clone(),
            proof_obligation_id,
            lineage_digest,
        };
        match decide(&receipt, &self.kernel_evidence) {
            EliminationVerdict::Eliminate { certificate } => {
                // Record the carrier InstId (NOT the decide-time identity) so the re-check can
                // re-read the LIVE carrier operands by an independent lift (#9 non-vacuous drift).
                self.kernel_eliminations
                    .push((inst_id, certificate.clone()));
                Some(certificate)
            }
            EliminationVerdict::Keep { .. } => None,
        }
    }

    /// Independent fail-closed re-check (Sentinel S4): re-validate every kernel-authorized
    /// elimination by a different path ([`recheck_elimination`] re-derives the operand fingerprint
    /// and re-confirms discharge/lineage against the evidence). Returns the first rejection reason,
    /// or `Ok(())` if all eliminations independently re-justify.
    ///
    /// #9: the `observed_operands` passed to [`recheck_elimination`] are the INDEPENDENTLY re-lifted
    /// snapshot captured from the live carrier at the end of `run_impl` (see
    /// `kernel_observed_operands`), NOT the decide-time identity. So the operand-fingerprint
    /// comparison is non-vacuous: a genuine operand drift between authorization and re-check is
    /// rejected fail-closed, while a true match still re-justifies.
    pub fn recheck_kernel_eliminations(&self) -> Result<(), String> {
        for (idx, (_inst_id, certificate)) in self.kernel_eliminations.iter().enumerate() {
            let observed = match self.kernel_observed_operands.get(idx) {
                Some(ops) => ops.as_slice(),
                // No independent snapshot for this elimination => fail closed.
                None => &[],
            };
            match recheck_elimination(certificate, observed, &self.kernel_evidence) {
                RecheckOutcome::Valid => {}
                RecheckOutcome::Rejected { reason } => {
                    return Err(format!(
                        "guard elimination re-check rejected (obligation {}): {}",
                        certificate.obligation_id(),
                        reason
                    ));
                }
            }
        }
        Ok(())
    }

    /// #9: strongest fail-closed re-check — re-read the LIVE carrier operands directly from `func`
    /// (an independent lift via [`AArch64GuardTarget::operand_identity`] on the current
    /// `func.inst(inst_id)`) and re-validate. If a carrier's operands drifted between authorization
    /// and this re-check, the re-derived fingerprint no longer matches the certificate and the
    /// elimination is rejected. The `&self`-only
    /// [`recheck_kernel_eliminations`](Self::recheck_kernel_eliminations) uses the equivalent
    /// end-of-`run_impl` snapshot for the production MachinePass hook (where `func` is unavailable).
    pub fn recheck_kernel_eliminations_live(&self, func: &MachFunction) -> Result<(), String> {
        let target = AArch64GuardTarget;
        for (inst_id, certificate) in &self.kernel_eliminations {
            let observed = target.operand_identity(func.inst(*inst_id)).operands;
            match recheck_elimination(certificate, &observed, &self.kernel_evidence) {
                RecheckOutcome::Valid => {}
                RecheckOutcome::Rejected { reason } => {
                    return Err(format!(
                        "guard elimination live re-check rejected (obligation {}): {}",
                        certificate.obligation_id(),
                        reason
                    ));
                }
            }
        }
        Ok(())
    }

    /// Returns optimization statistics from the last run.
    pub fn stats(&self) -> &ProofOptStats {
        &self.stats
    }

    /// Returns the optimization certificates generated during the last run.
    ///
    /// Each certificate records a single applied or rejected proof-guided
    /// candidate, providing an audit trail for translation validation.
    pub fn certificates(&self) -> &[OptCertificate] {
        &self.certificates
    }

    /// Takes ownership of the optimization certificates, leaving the
    /// internal buffer empty. Useful for passing certificates to
    /// downstream verification without cloning.
    pub fn take_certificates(&mut self) -> Vec<OptCertificate> {
        std::mem::take(&mut self.certificates)
    }

    /// Attach #794 proof facts to an instruction for certificate emission.
    ///
    /// This is a sidecar compatibility path until every producer carries
    /// rich multi-fact proof metadata directly on machine instructions.
    pub fn set_inst_proof_facts(&mut self, inst_id: InstId, facts: Vec<ProofFact>) {
        if facts.is_empty() {
            self.proof_facts.remove(&inst_id);
        } else {
            self.proof_facts.insert(inst_id, facts);
        }
    }

    /// Clear all sidecar proof facts.
    pub fn clear_inst_proof_facts(&mut self) {
        self.proof_facts.clear();
    }

    /// Attach a source trust_ir region hash to an instruction for certificate
    /// emission. When absent, certificates use a stable pre-transform MachIR
    /// region hash as a compatibility fallback.
    pub fn set_source_region_hash(&mut self, inst_id: InstId, hash: u128) {
        self.source_region_hashes.insert(inst_id, hash);
    }

    /// Clear all sidecar source region hashes.
    pub fn clear_source_region_hashes(&mut self) {
        self.source_region_hashes.clear();
    }

    /// Seed this pass from pipeline-level sidecar metadata.
    pub fn set_metadata(&mut self, metadata: &ProofOptimizationMetadata) {
        self.proof_facts = metadata.proof_facts.clone();
        self.source_region_hashes = metadata.source_region_hashes.clone();
        self.candidate_rejections = metadata.candidate_rejections.clone();
    }

    /// Mark a proof-present candidate as disabled before the transform fires.
    pub fn disable_candidate(&mut self, inst_id: InstId, fact: &'static str, detail: &'static str) {
        self.candidate_rejections.insert(
            inst_id,
            OptRejection::from_diagnostic(ProofDiagnostic::disabled_candidate(fact, detail)),
        );
    }

    /// Mark a proof-present candidate as rejected by a product gate.
    pub fn fail_product_gate(&mut self, inst_id: InstId, fact: &'static str, detail: &'static str) {
        self.candidate_rejections.insert(
            inst_id,
            OptRejection::from_diagnostic(ProofDiagnostic::failed_product_gate(fact, detail)),
        );
    }
}

impl Default for ProofOptimization {
    fn default() -> Self {
        Self::new()
    }
}

impl MachinePass for ProofOptimization {
    fn name(&self) -> &str {
        "proof-opts"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        self.run_impl(func, None)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        self.seed_source_region_hashes_from_provenance(func, provenance);
        self.run_impl(func, Some(provenance))
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut AnalysisCache,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        self.seed_source_region_hashes_from_provenance(func, provenance);
        self.run_impl(func, Some(provenance))
    }

    fn set_proof_optimization_metadata(&mut self, metadata: &ProofOptimizationMetadata) {
        self.set_metadata(metadata);
    }

    fn take_proof_optimization_certificates(&mut self) -> Vec<OptCertificate> {
        self.take_certificates()
    }

    /// Sentinel S4 fail-closed re-check surfaced to the boxed-pass caller.
    ///
    /// Delegates to the inherent [`ProofOptimization::recheck_kernel_eliminations`]
    /// so the `PassManager` (which only holds `dyn MachinePass`) can surface the
    /// verdict through [`crate::pass_manager::PassStats::kernel_recheck`]. This is
    /// the boxed-pipeline equivalent of the x86 inline re-check, giving the
    /// AArch64 production path parity: a rejection aborts the compile.
    fn recheck_kernel_eliminations(&self) -> Result<(), String> {
        ProofOptimization::recheck_kernel_eliminations(self)
    }
}

impl ProofOptimization {
    fn run_impl(
        &mut self,
        func: &mut MachFunction,
        mut provenance: Option<&mut ProvenanceMap>,
    ) -> bool {
        self.stats = ProofOptStats::default();
        self.certificates.clear();
        self.kernel_eliminations.clear();
        self.kernel_observed_operands.clear();

        // The entire pass is proof-consuming, not just its guard-deletion arms.  Public machine-IR
        // annotations and sidecar facts are constructible by callers, so they cannot authorize
        // checked-to-unchecked rewrites, alias refinement, CSE, pair combining, or guard removal.
        // In-crate unit tests retain the structural model; downstream/production builds stay inert
        // until an exact validator-issued replay capability replaces this policy seam.
        // ... with ONE exception, added by WP-2: a decidable-lattice replay capability IS exact
        // obligation-bound evidence (see `trust_cg_lower::lattice_guard`). When only that authority
        // is held, the pass runs in a RESTRICTED scope — see `lattice_bounds_only` — so the arms
        // that still have no exact evidence behind them stay exactly as inert as they are today.
        let full_authority =
            trust_cg_lower::guard_evidence::validator_guard_replay_authority_available();
        let lattice_authority =
            trust_cg_lower::lattice_guard::lattice_guard_replay_authority_available();
        if !full_authority && !lattice_authority && !cfg!(test) {
            return false;
        }
        // Restricted scope: lattice authority alone admits ONLY `InBounds` bounds-guard
        // elimination, and even then only for carriers the kernel binds to a lattice obligation.
        // Every other proof annotation is skipped, so turning the lattice on cannot silently
        // enable overflow/null/div/shift elimination, alias refinement, CSE or pair combining.
        let lattice_bounds_only = !full_authority && !cfg!(test) && lattice_authority;
        let mut changed = false;

        // Collect instructions to delete across all blocks.
        let mut to_delete: HashSet<InstId> = HashSet::new();

        for block_id in func.block_order.clone() {
            let block_insts: Vec<InstId> = func.block(block_id).insts.clone();

            for (pos, &inst_id) in block_insts.iter().enumerate() {
                let proof = func.inst(inst_id).proof;

                // Restricted (lattice-only) scope: everything but the bounds guard is invisible.
                if lattice_bounds_only && !matches!(proof, Some(ProofAnnotation::InBounds)) {
                    continue;
                }

                if let Some(annotation) = proof
                    && let Some(rejection) = self.candidate_rejections.get(&inst_id).cloned()
                {
                    self.record_rejected_certificate_with_rejection(
                        func,
                        annotation,
                        format!(
                            "{} proof candidate rejected before transform admission",
                            proof_annotation_stable_name(annotation)
                        ),
                        inst_id,
                        RejectedCertificateDetails {
                            source_region: &[inst_id],
                            kind: default_certificate_kind(annotation),
                            reason: rejection,
                        },
                    );
                    continue;
                }

                match proof {
                    Some(
                        annotation @ (ProofAnnotation::NoOverflow
                        | ProofAnnotation::NoSignedOverflow
                        | ProofAnnotation::NoUnsignedOverflow),
                    ) => {
                        if self.apply_no_overflow(
                            func,
                            &block_insts,
                            pos,
                            annotation,
                            &mut to_delete,
                            provenance.as_deref_mut(),
                        ) {
                            changed = true;
                        } else {
                            let name = proof_annotation_stable_name(annotation);
                            self.record_rejected_certificate(
                                func,
                                annotation,
                                format!("{name} proof did not match a checked-overflow guard"),
                                inst_id,
                                RejectedCertificateDetails {
                                    source_region: &[inst_id],
                                    kind: OptCertificateKind::CheckedToUnchecked,
                                    reason: ProofDiagnostic::rewrite_rejected(
                                        name,
                                        "checked-overflow guard shape not matched",
                                    ),
                                },
                            );
                        }
                    }
                    Some(ProofAnnotation::InBounds) => {
                        if self.apply_in_bounds(
                            func,
                            &block_insts,
                            pos,
                            &mut to_delete,
                            provenance.as_deref_mut(),
                        ) {
                            changed = true;
                        } else {
                            self.record_rejected_certificate(
                                func,
                                ProofAnnotation::InBounds,
                                "InBounds proof did not match an exact bounds-check guard",
                                inst_id,
                                RejectedCertificateDetails {
                                    source_region: &[inst_id],
                                    kind: OptCertificateKind::GuardEliminated,
                                    reason: ProofDiagnostic::rewrite_rejected(
                                        "InBounds",
                                        "exact bounds-check guard shape not matched",
                                    ),
                                },
                            );
                        }
                    }
                    Some(ProofAnnotation::NotNull) => {
                        if self.apply_not_null(
                            func,
                            &block_insts,
                            pos,
                            &mut to_delete,
                            provenance.as_deref_mut(),
                        ) {
                            changed = true;
                        } else {
                            self.record_rejected_certificate(
                                func,
                                ProofAnnotation::NotNull,
                                "NotNull proof did not match a null-check guard",
                                inst_id,
                                RejectedCertificateDetails {
                                    source_region: &[inst_id],
                                    kind: OptCertificateKind::GuardEliminated,
                                    reason: ProofDiagnostic::rewrite_rejected(
                                        "NotNull",
                                        "null-check guard shape not matched",
                                    ),
                                },
                            );
                        }
                    }
                    Some(ProofAnnotation::ValidBorrow) => {
                        match self.apply_valid_borrow(func, inst_id, provenance.as_deref_mut()) {
                            ValidBorrowApplyResult::Applied => {
                                changed = true;
                            }
                            ValidBorrowApplyResult::AlreadyRefined => {}
                            ValidBorrowApplyResult::NotMemory => {
                                self.record_rejected_certificate(
                                    func,
                                    ProofAnnotation::ValidBorrow,
                                    "ValidBorrow proof did not match a memory operation",
                                    inst_id,
                                    RejectedCertificateDetails {
                                        source_region: &[inst_id],
                                        kind: OptCertificateKind::FlagsRefined,
                                        reason: ProofDiagnostic::rewrite_rejected(
                                            "ValidBorrow",
                                            "instruction is not a memory operation",
                                        ),
                                    },
                                );
                            }
                        }
                    }
                    Some(ProofAnnotation::PositiveRefCount) => {
                        if self.apply_positive_refcount(
                            func,
                            &block_insts,
                            pos,
                            &mut to_delete,
                            provenance.as_deref_mut(),
                        ) {
                            changed = true;
                        } else {
                            self.record_rejected_certificate(
                                func,
                                ProofAnnotation::PositiveRefCount,
                                "PositiveRefCount proof did not match a retain/release pair",
                                inst_id,
                                RejectedCertificateDetails {
                                    source_region: &[inst_id],
                                    kind: OptCertificateKind::PairEliminated,
                                    reason: ProofDiagnostic::rewrite_rejected(
                                        "PositiveRefCount",
                                        "matching retain/release pair not found",
                                    ),
                                },
                            );
                        }
                    }
                    Some(ProofAnnotation::NonZeroDivisor) => {
                        if self.apply_non_zero_divisor(
                            func,
                            &block_insts,
                            pos,
                            &mut to_delete,
                            provenance.as_deref_mut(),
                        ) {
                            changed = true;
                        } else {
                            self.record_rejected_certificate(
                                func,
                                ProofAnnotation::NonZeroDivisor,
                                "NonZeroDivisor proof did not match a div-zero guard",
                                inst_id,
                                RejectedCertificateDetails {
                                    source_region: &[inst_id],
                                    kind: OptCertificateKind::GuardEliminated,
                                    reason: ProofDiagnostic::rewrite_rejected(
                                        "NonZeroDivisor",
                                        "division-by-zero guard shape not matched",
                                    ),
                                },
                            );
                        }
                    }
                    Some(ProofAnnotation::ValidShift) => {
                        if self.apply_valid_shift(
                            func,
                            &block_insts,
                            pos,
                            &mut to_delete,
                            provenance.as_deref_mut(),
                        ) {
                            changed = true;
                        } else {
                            self.record_rejected_certificate(
                                func,
                                ProofAnnotation::ValidShift,
                                "ValidShift proof did not match a shift-range guard",
                                inst_id,
                                RejectedCertificateDetails {
                                    source_region: &[inst_id],
                                    kind: OptCertificateKind::GuardEliminated,
                                    reason: ProofDiagnostic::rewrite_rejected(
                                        "ValidShift",
                                        "shift-range guard shape not matched",
                                    ),
                                },
                            );
                        }
                    }
                    Some(ProofAnnotation::Pure) => {
                        if self.apply_pure(func, inst_id, provenance.as_deref_mut()) {
                            changed = true;
                        } else {
                            self.record_rejected_certificate(
                                func,
                                ProofAnnotation::Pure,
                                "Pure proof did not refine instruction flags",
                                inst_id,
                                RejectedCertificateDetails {
                                    source_region: &[inst_id],
                                    kind: OptCertificateKind::FlagsRefined,
                                    reason: ProofDiagnostic::rewrite_rejected(
                                        "Pure",
                                        "instruction is already side-effect free",
                                    ),
                                },
                            );
                        }
                    }
                    // Algebraic property proofs: preserved as metadata for
                    // downstream passes (vectorizer, parallel reduction).
                    // The proof_opts pass does not transform these directly
                    // but they are consumed by vectorize.rs and scheduler.rs.
                    Some(
                        annotation @ (ProofAnnotation::Associative
                        | ProofAnnotation::Commutative
                        | ProofAnnotation::Idempotent),
                    ) => {
                        self.record_rejected_certificate(
                            func,
                            annotation,
                            "Algebraic proof is not directly representable in proof_opts",
                            inst_id,
                            RejectedCertificateDetails {
                                source_region: &[inst_id],
                                kind: OptCertificateKind::FlagsRefined,
                                reason: ProofDiagnostic::present_unrepresentable(
                                    proof_annotation_stable_name(annotation),
                                    "proof_opts has no direct transform for this algebraic proof",
                                ),
                            },
                        );
                    }
                    _ => {}
                }
            }
        }

        // Remove deleted instructions from blocks.
        if !to_delete.is_empty() {
            for block_id in func.block_order.clone() {
                let block = func.block_mut(block_id);
                block.insts.retain(|id| !to_delete.contains(id));
            }
        }

        // #9: capture an INDEPENDENT re-lift of each authorized carrier's LIVE operands for the
        // fail-closed re-check. `func.insts` still holds the carrier inst data after deletion-by-
        // retain (only the block ordering was pruned), so re-reading `func.inst(inst_id)` and
        // re-lifting via `AArch64GuardTarget::operand_identity` is a genuinely separate path from
        // the decide-time identity. A real operand drift would now diverge and be rejected.
        if !self.kernel_eliminations.is_empty() {
            let target = AArch64GuardTarget;
            self.kernel_observed_operands = self
                .kernel_eliminations
                .iter()
                .map(|(inst_id, _)| target.operand_identity(func.inst(*inst_id)).operands)
                .collect();
        }

        // Aligned-pair combining is driven by producer-constructible `ProofFact::Aligned`
        // sidecars, which lattice authority says nothing about. Restricted scope skips it.
        if !lattice_bounds_only && self.combine_aligned_aarch64_pairs(func, provenance) {
            changed = true;
        }

        self.stats.total_certificates = self.certificates.len() as u32;

        changed
    }

    fn push_applied_certificate(
        &mut self,
        func: &MachFunction,
        annotation: ProofAnnotation,
        description: impl Into<String>,
        primary_inst: InstId,
        details: AppliedCertificateDetails<'_>,
    ) {
        let cert = self.build_certificate(
            func,
            CertificateBuild {
                annotation,
                description: description.into(),
                primary_inst,
                affected_insts: details.affected_insts,
                kind: details.kind,
                source_region_hash: details.source_region_hash,
                target_region: details.target_region,
                rejection: None,
            },
        );
        self.certificates.push(cert);
    }

    fn record_rejected_certificate(
        &mut self,
        func: &MachFunction,
        annotation: ProofAnnotation,
        description: impl Into<String>,
        primary_inst: InstId,
        details: RejectedCertificateDetails<'_, ProofDiagnostic>,
    ) {
        self.record_rejected_certificate_with_rejection(
            func,
            annotation,
            description,
            primary_inst,
            RejectedCertificateDetails {
                source_region: details.source_region,
                kind: details.kind,
                reason: OptRejection::from_diagnostic(details.reason),
            },
        );
    }

    fn record_rejected_certificate_with_rejection(
        &mut self,
        func: &MachFunction,
        annotation: ProofAnnotation,
        description: impl Into<String>,
        primary_inst: InstId,
        details: RejectedCertificateDetails<'_, OptRejection>,
    ) {
        let source_region_hash = self.source_region_hash(func, primary_inst, details.source_region);
        let cert = self.build_certificate(
            func,
            CertificateBuild {
                annotation,
                description: description.into(),
                primary_inst,
                affected_insts: Vec::new(),
                kind: details.kind,
                source_region_hash,
                target_region: details.source_region,
                rejection: Some(details.reason),
            },
        );
        self.certificates.push(cert);
    }

    fn push_pair_combined_certificate(
        &mut self,
        func: &MachFunction,
        first_id: InstId,
        second_id: InstId,
        pair_id: InstId,
    ) {
        let consumed_facts = vec![OptConsumedProofFact::ProofFact(
            self.pair_start_fact_proving_aligned16(first_id)
                .expect("pair combine admission requires pair-start aligned fact"),
        )];
        let transform = OptTransformIdentity {
            name: "proof-opts.aligned.pair-combined".to_string(),
            version: PROOF_OPT_TRANSFORM_VERSION,
        };
        let route = OptAdmissionRoute {
            pass: PROOF_OPT_PASS_NAME.to_string(),
            admission: "proof-facts".to_string(),
        };
        let source_region_hash = self.source_region_hash_for_pair(func, first_id, second_id);
        let target_region_hash = region_hash(func, &[pair_id]);
        let proof_hash = fact_only_proof_hash(&consumed_facts);
        let validation_hash = validation_hash(
            &transform,
            &route,
            &OptCertificateKind::PairCombined,
            source_region_hash,
            target_region_hash,
            proof_hash,
            None,
        );
        let certificate_id = certificate_id(
            &transform,
            source_region_hash,
            target_region_hash,
            proof_hash,
            validation_hash,
        );

        self.certificates.push(OptCertificate {
            certificate_id,
            transform,
            route,
            annotation: None,
            consumed_facts,
            description:
                "Combined adjacent aligned 64-bit memory operations into an AArch64 pair op"
                    .to_string(),
            primary_inst: pair_id,
            affected_insts: Vec::new(),
            kind: OptCertificateKind::PairCombined,
            source_region_hash,
            target_region_hash,
            proof_hash,
            validation_hash,
            rejection: None,
        });
    }

    fn push_rejected_pair_certificate(
        &mut self,
        func: &MachFunction,
        first_id: InstId,
        second_id: InstId,
        rejection: AlignedPairRejection,
    ) {
        let consumed_facts = vec![OptConsumedProofFact::ProofFact(
            self.pair_start_aligned_fact(first_id)
                .expect("pair rejection admission requires pair-start aligned fact"),
        )];
        let transform = OptTransformIdentity {
            name: "proof-opts.aligned.pair-combined".to_string(),
            version: PROOF_OPT_TRANSFORM_VERSION,
        };
        let route = OptAdmissionRoute {
            pass: PROOF_OPT_PASS_NAME.to_string(),
            admission: "proof-facts".to_string(),
        };
        let source_region_hash = self.source_region_hash_for_pair(func, first_id, second_id);
        let target_region_hash = region_hash(func, &[first_id, second_id]);
        let proof_hash = fact_only_proof_hash(&consumed_facts);
        let rejection = OptRejection::from_diagnostic(ProofDiagnostic::rewrite_rejected(
            "Aligned",
            rejection.detail(),
        ));
        let validation_hash = validation_hash(
            &transform,
            &route,
            &OptCertificateKind::PairCombined,
            source_region_hash,
            target_region_hash,
            proof_hash,
            Some(&rejection),
        );
        let certificate_id = certificate_id(
            &transform,
            source_region_hash,
            target_region_hash,
            proof_hash,
            validation_hash,
        );

        self.certificates.push(OptCertificate {
            certificate_id,
            transform,
            route,
            annotation: None,
            consumed_facts,
            description: "Aligned pair candidate rejected by AArch64 pair-op safety checks"
                .to_string(),
            primary_inst: first_id,
            affected_insts: Vec::new(),
            kind: OptCertificateKind::PairCombined,
            source_region_hash,
            target_region_hash,
            proof_hash,
            validation_hash,
            rejection: Some(rejection),
        });
    }

    fn build_certificate(
        &self,
        func: &MachFunction,
        build: CertificateBuild<'_>,
    ) -> OptCertificate {
        let CertificateBuild {
            annotation,
            description,
            primary_inst,
            affected_insts,
            kind,
            source_region_hash,
            target_region,
            rejection,
        } = build;
        let transform = OptTransformIdentity {
            name: transform_name(annotation, &kind).to_string(),
            version: PROOF_OPT_TRANSFORM_VERSION,
        };
        let route = self.admission_route(primary_inst);
        let consumed_facts = self.consumed_facts(primary_inst, annotation);
        let target_region_hash = region_hash(func, target_region);
        let proof_hash = proof_hash(annotation, &consumed_facts);
        let validation_hash = validation_hash(
            &transform,
            &route,
            &kind,
            source_region_hash,
            target_region_hash,
            proof_hash,
            rejection.as_ref(),
        );
        let certificate_id = certificate_id(
            &transform,
            source_region_hash,
            target_region_hash,
            proof_hash,
            validation_hash,
        );

        OptCertificate {
            certificate_id,
            transform,
            route,
            annotation: Some(annotation),
            consumed_facts,
            description,
            primary_inst,
            affected_insts,
            kind,
            source_region_hash,
            target_region_hash,
            proof_hash,
            validation_hash,
            rejection,
        }
    }

    fn consumed_facts(
        &self,
        inst_id: InstId,
        annotation: ProofAnnotation,
    ) -> Vec<OptConsumedProofFact> {
        let mut facts = vec![OptConsumedProofFact::LegacyAnnotation(annotation)];
        if let Some(sidecar_facts) = self.proof_facts.get(&inst_id) {
            facts.extend(
                sidecar_facts
                    .iter()
                    .copied()
                    .map(OptConsumedProofFact::ProofFact),
            );
        }
        facts
    }

    fn admission_route(&self, inst_id: InstId) -> OptAdmissionRoute {
        let has_sidecar_facts = self
            .proof_facts
            .get(&inst_id)
            .is_some_and(|facts| !facts.is_empty());
        OptAdmissionRoute {
            pass: PROOF_OPT_PASS_NAME.to_string(),
            admission: if has_sidecar_facts {
                "proof-annotation+proof-facts"
            } else {
                "proof-annotation"
            }
            .to_string(),
        }
    }

    fn source_region_hash(
        &self,
        func: &MachFunction,
        primary_inst: InstId,
        source_region: &[InstId],
    ) -> u128 {
        self.source_region_hashes
            .get(&primary_inst)
            .copied()
            .unwrap_or_else(|| region_hash(func, source_region))
    }

    fn source_region_hash_for_pair(
        &self,
        func: &MachFunction,
        first_id: InstId,
        second_id: InstId,
    ) -> u128 {
        let source_hashes = [
            self.source_region_hash(func, first_id, &[first_id]),
            self.source_region_hash(func, second_id, &[second_id]),
        ];
        combined_source_region_identity_hash(&func.name, &source_hashes)
    }

    fn seed_source_region_hashes_from_provenance(
        &mut self,
        func: &MachFunction,
        provenance: &ProvenanceMap,
    ) {
        for block_id in &func.block_order {
            for inst_id in &func.block(*block_id).insts {
                if self.source_region_hashes.contains_key(inst_id) {
                    continue;
                }
                let Some(entry) = provenance.get_entry(*inst_id) else {
                    continue;
                };
                if entry.trust_ir_origins.is_empty() {
                    continue;
                }
                self.source_region_hashes.insert(
                    *inst_id,
                    source_trust_ir_region_hash(&func.name, &entry.trust_ir_origins),
                );
            }
        }
    }

    fn combine_aligned_aarch64_pairs(
        &mut self,
        func: &mut MachFunction,
        mut provenance: Option<&mut ProvenanceMap>,
    ) -> bool {
        let mut changed = false;

        for block_id in func.block_order.clone() {
            let old_insts = func.block(block_id).insts.clone();
            let mut new_insts = Vec::with_capacity(old_insts.len());
            let mut pos = 0;
            let mut block_changed = false;

            while pos < old_insts.len() {
                if pos + 1 < old_insts.len() {
                    let first_id = old_insts[pos];
                    let second_id = old_insts[pos + 1];
                    match self.classify_aligned_pair_candidate(
                        func.inst(first_id),
                        first_id,
                        func.inst(second_id),
                        second_id,
                    ) {
                        AlignedPairCandidate::Combine(pair_inst) => {
                            let pair_id = func.push_inst(pair_inst);
                            new_insts.push(pair_id);
                            self.stats.pair_mem_ops_combined += 1;
                            self.push_pair_combined_certificate(func, first_id, second_id, pair_id);
                            if let Some(provenance) = provenance.as_deref_mut() {
                                provenance.record_merge(
                                    &[first_id, second_id],
                                    pair_id,
                                    proof_opts_pass_id(),
                                );
                            }
                            block_changed = true;
                            changed = true;
                            pos += 2;
                            continue;
                        }
                        AlignedPairCandidate::Reject(rejection) => {
                            self.push_rejected_pair_certificate(
                                func, first_id, second_id, rejection,
                            );
                        }
                        AlignedPairCandidate::NotCandidate => {}
                    }
                }

                new_insts.push(old_insts[pos]);
                pos += 1;
            }

            if block_changed {
                func.block_mut(block_id).insts = new_insts;
            }
        }

        changed
    }

    fn classify_aligned_pair_candidate(
        &self,
        first: &MachInst,
        first_id: InstId,
        second: &MachInst,
        second_id: InstId,
    ) -> AlignedPairCandidate {
        let Some(first_mem) = PairMemOp::from_inst(first) else {
            return AlignedPairCandidate::NotCandidate;
        };
        let Some(second_mem) = PairMemOp::from_inst(second) else {
            return AlignedPairCandidate::NotCandidate;
        };

        if first_mem.kind != second_mem.kind
            || first_mem.base != second_mem.base
            || first_mem.offset.checked_add(8) != Some(second_mem.offset)
        {
            return AlignedPairCandidate::NotCandidate;
        }

        if first.proof.is_some()
            || second.proof.is_some()
            || self.has_certificate_for_inst(first_id)
            || self.has_certificate_for_inst(second_id)
            || self.candidate_rejections.contains_key(&first_id)
            || self.candidate_rejections.contains_key(&second_id)
        {
            return AlignedPairCandidate::NotCandidate;
        }

        if self.pair_start_fact_proving_aligned16(first_id).is_none() {
            if self.pair_start_aligned_fact(first_id).is_some() {
                return AlignedPairCandidate::Reject(AlignedPairRejection::PairStartNotAligned16);
            }
            return AlignedPairCandidate::NotCandidate;
        }

        if !pair_offset_is_encodable(first_mem.offset) {
            return AlignedPairCandidate::Reject(AlignedPairRejection::PairOffsetOutOfRange);
        }

        if first_mem.kind == PairMemKind::Load
            && load_pair_has_unsafe_register_overlap(first_mem, second_mem)
        {
            return AlignedPairCandidate::Reject(AlignedPairRejection::LoadRegisterOverlap);
        }

        let opcode = match first_mem.kind {
            PairMemKind::Load => AArch64Opcode::LdpRI,
            PairMemKind::Store => AArch64Opcode::StpRI,
        };
        let mut pair = MachInst::new(
            opcode,
            vec![
                first_mem.rt.to_operand(),
                second_mem.rt.to_operand(),
                first_mem.base.to_operand(),
                MachOperand::Imm(first_mem.offset),
            ],
        );
        pair.source_loc = first.source_loc.or(second.source_loc);
        AlignedPairCandidate::Combine(pair)
    }

    fn pair_start_fact_proving_aligned16(&self, inst_id: InstId) -> Option<ProofFact> {
        self.proof_facts.get(&inst_id)?.iter().copied().find(
            |fact| matches!(fact, ProofFact::Aligned(bytes) if *bytes >= 16 && *bytes % 16 == 0),
        )
    }

    fn pair_start_aligned_fact(&self, inst_id: InstId) -> Option<ProofFact> {
        self.proof_facts
            .get(&inst_id)?
            .iter()
            .filter_map(|fact| match fact {
                ProofFact::Aligned(bytes) => Some(*bytes),
                _ => None,
            })
            .min()
            .map(ProofFact::Aligned)
    }

    fn has_certificate_for_inst(&self, inst_id: InstId) -> bool {
        self.certificates
            .iter()
            .any(|cert| cert.primary_inst == inst_id || cert.affected_insts.contains(&inst_id))
    }

    /// NoOverflow optimization: when trust_ir proves no overflow/no-wrap, convert
    /// checked arithmetic to unchecked.
    ///
    /// Signed patterns:
    /// 1. `ADDS/SUBS dst, a, b` [NoOverflow/NoSignedOverflow] + `TrapOverflow`
    /// 2. `ADDS/SUBS dst, a, b` [NoOverflow/NoSignedOverflow] + `BCond.VS overflow` + `B ok`
    ///
    /// Unsigned patterns:
    /// 1. `ADDS dst, a, b` [NoUnsignedOverflow] + `BCond.HS overflow` + `B ok`
    /// 2. `SUBS dst, a, b` [NoUnsignedOverflow] + `BCond.LO overflow` + `B ok`
    ///
    /// Result:  `ADD/SUB dst, a, b` (overflow guard removed)
    ///
    /// The ADDS/SUBS instruction sets condition flags; the subsequent guard
    /// branches to a panic block if overflow occurred. With the proof, we:
    /// 1. Replace ADDS/SUBS with plain ADD/SUB (no flag setting)
    /// 2. Remove the matched guard instruction
    fn apply_no_overflow(
        &mut self,
        func: &mut MachFunction,
        block_insts: &[InstId],
        pos: usize,
        annotation: ProofAnnotation,
        to_delete: &mut HashSet<InstId>,
        mut provenance: Option<&mut ProvenanceMap>,
    ) -> bool {
        let inst_id = block_insts[pos];
        let opcode = func.inst(inst_id).opcode;

        // Production carrier: self-contained `TrapOverflowExact lhs, rhs, Imm(op_tag)` (the OVERFLOW
        // analogue of the InBounds `TrapBoundsCheckExact` / ShiftRange `TrapShiftRangeIfOOB`
        // carriers). Unlike those, the value op is a SEPARATE plain ADD/SUB; this carrier carries
        // only the overflow check, which a KEPT carrier RE-DERIVES from its own [lhs, rhs] via a
        // flag-recompute (see `expand_trap_overflow_exact`). Eliminated here only under kernel
        // authorization (gate ON), or by the legacy syntactic path (gate OFF). An unproven carrier
        // is KEPT (fail-safe).
        if opcode == AArch64Opcode::TrapOverflowExact {
            return self.apply_overflow_carrier(
                func,
                inst_id,
                annotation,
                to_delete,
                provenance.as_deref_mut(),
            );
        }

        // Map checked opcodes to unchecked equivalents.
        let unchecked = match opcode {
            AArch64Opcode::AddsRR => AArch64Opcode::AddRR,
            AArch64Opcode::AddsRI => AArch64Opcode::AddRI,
            AArch64Opcode::SubsRR => AArch64Opcode::SubRR,
            AArch64Opcode::SubsRI => AArch64Opcode::SubRI,
            _ => return false,
        };

        // Only rewrite when this pass is consuming the paired overflow guard.
        // ADDS/SUBS also define NZCV for flag readers such as CSET VS; changing
        // them to ADD/SUB without removing a guard would leave stale flags.
        let Some(next_id) = block_insts.get(pos + 1).copied() else {
            return false;
        };
        let followed_by_ok_branch = block_insts
            .get(pos + 2)
            .is_some_and(|id| func.inst(*id).opcode == AArch64Opcode::B);
        let affected_id = match annotation {
            ProofAnnotation::NoOverflow | ProofAnnotation::NoSignedOverflow => {
                if func.inst(next_id).opcode == AArch64Opcode::TrapOverflow
                    || (bcond_is_signed_overflow_guard_for_opcode(func.inst(next_id), opcode)
                        && followed_by_ok_branch)
                {
                    next_id
                } else {
                    return false;
                }
            }
            ProofAnnotation::NoUnsignedOverflow
                if bcond_is_unsigned_overflow_guard_for_opcode(func.inst(next_id), opcode)
                    && followed_by_ok_branch =>
            {
                next_id
            }
            _ => return false,
        };

        // These legacy paired shapes have no exact, self-contained carrier identity.  A proof
        // annotation on ADDS/SUBS is only a label and cannot authorize deleting the adjacent trap
        // or branch.  When the fail-closed kernel policy is installed (all production compiles),
        // keep the pair.  This closes the one guard-removal path that previously bypassed
        // `kernel_authorizes` even while `kernel_gate` was active.
        if self.kernel_gate && self.kernel_authorizes(func, affected_id).is_none() {
            return false;
        }

        let source_region_hash = self.source_region_hash(func, inst_id, &[inst_id, affected_id]);

        // Replace the checked instruction with unchecked.
        let inst = func.inst_mut(inst_id);
        inst.opcode = unchecked;
        inst.flags = unchecked.default_flags();
        inst.proof = None;

        to_delete.insert(affected_id);

        if let Some(provenance) = provenance {
            let pass = proof_opts_pass_id();
            provenance.record_in_place_transform(inst_id, pass.clone());
            provenance.record_deletion(
                affected_id,
                pass,
                format!(
                    "{} proof eliminated overflow guard",
                    proof_annotation_stable_name(annotation)
                ),
            );
        }

        self.push_applied_certificate(
            func,
            annotation,
            format!(
                "Converted checked arithmetic to unchecked using {} proof",
                proof_annotation_stable_name(annotation)
            ),
            inst_id,
            AppliedCertificateDetails {
                affected_insts: vec![affected_id],
                kind: OptCertificateKind::CheckedToUnchecked,
                source_region_hash,
                target_region: &[inst_id],
            },
        );
        self.stats.overflow_checks_eliminated += 1;
        true
    }

    /// Eliminate a self-contained `TrapOverflowExact lhs, rhs, Imm(op_tag)` overflow carrier.
    ///
    /// This is the OVERFLOW mirror of `apply_valid_shift`'s `TrapShiftRangeIfOOB` branch, but with
    /// the decoupled-value invariant: the value op is a SEPARATE plain ADD/SUB that this function
    /// NEVER touches, so eliminating the carrier removes ONLY the overflow check and leaves a correct
    /// value in all cases. Sentinel S4: with the kernel gate ON, the carrier is deleted only if the
    /// Certified-Elimination Kernel authorizes it (a discharged obligation bound to this carrier by
    /// its `[lhs, rhs, Imm(op_tag)]` fingerprint — the op-tag makes a wrong-op/width proof
    /// fingerprint differently, so it cannot discharge it). With the gate OFF, the legacy syntactic
    /// path removes it unconditionally (the carrier itself is the proof-only shape ISel emits only
    /// when a genuine overflow proof is present). An unproven carrier is KEPT, and a KEPT carrier
    /// expands to a real flag-recompute + conditional branch + trap, so an ACTUAL overflow traps.
    fn apply_overflow_carrier(
        &mut self,
        func: &mut MachFunction,
        inst_id: InstId,
        annotation: ProofAnnotation,
        to_delete: &mut HashSet<InstId>,
        provenance: Option<&mut ProvenanceMap>,
    ) -> bool {
        debug_assert_eq!(func.inst(inst_id).opcode, AArch64Opcode::TrapOverflowExact);

        // Sentinel S4: gate-on deletes only on kernel authorization; gate-off via the legacy path.
        if self.kernel_gate && self.kernel_authorizes(func, inst_id).is_none() {
            return false;
        }

        let source_region_hash = self.source_region_hash(func, inst_id, &[inst_id]);
        to_delete.insert(inst_id);
        if let Some(provenance) = provenance {
            provenance.record_deletion(
                inst_id,
                proof_opts_pass_id(),
                format!(
                    "{} proof eliminated overflow guard",
                    proof_annotation_stable_name(annotation)
                ),
            );
        }
        self.push_applied_certificate(
            func,
            annotation,
            format!(
                "Eliminated overflow guard using {} proof",
                proof_annotation_stable_name(annotation)
            ),
            inst_id,
            AppliedCertificateDetails {
                affected_insts: vec![],
                kind: OptCertificateKind::GuardEliminated,
                source_region_hash,
                target_region: &[],
            },
        );
        self.stats.overflow_checks_eliminated += 1;
        true
    }

    /// InBounds optimization: when trust_ir proves array access is in-bounds,
    /// eliminate the bounds check guard.
    ///
    /// Pattern: `TrapBoundsCheckExact base, index, bound` [InBounds]
    /// Result:  exact proof-only carrier removed.
    ///
    /// Legacy `CMP idx, len` + `TrapBoundsCheck` is intentionally not a
    /// consumer. Bounds facts must arrive through the exact carrier so the
    /// optimizer never infers base/index/bound identity from nearby MIR shape.
    fn apply_in_bounds(
        &mut self,
        func: &mut MachFunction,
        block_insts: &[InstId],
        pos: usize,
        to_delete: &mut HashSet<InstId>,
        provenance: Option<&mut ProvenanceMap>,
    ) -> bool {
        let inst_id = block_insts[pos];
        let opcode = func.inst(inst_id).opcode;

        if opcode != AArch64Opcode::TrapBoundsCheckExact {
            return false;
        }

        // Sentinel S4: when the kernel gate is on, delete only if the Certified-Elimination Kernel
        // authorizes it (a discharged obligation bound to this carrier). Otherwise keep the guard.
        //
        // WP-2: the certificate the kernel mints names the OBLIGATION that discharged this guard.
        // For a lattice-certified elision that id is a pure function of the discharging predicate's
        // content and the exact interval the guard tests, so recording it here records WHICH
        // predicate did the work — recoverable from the adapter's
        // `ProofContext::lattice_bounds_capabilities` by matching `obligation_id`.
        let discharged_obligation = if self.kernel_gate {
            match self.kernel_authorizes(func, inst_id) {
                Some(certificate) => Some(certificate.obligation_id()),
                None => return false,
            }
        } else {
            None
        };

        let source_region_hash = self.source_region_hash(func, inst_id, &[inst_id]);
        to_delete.insert(inst_id);
        if let Some(provenance) = provenance {
            provenance.record_deletion(
                inst_id,
                proof_opts_pass_id(),
                "InBounds proof eliminated exact bounds-check guard",
            );
        }
        let description = match discharged_obligation {
            Some(obligation) => format!(
                "Eliminated exact bounds check guard; discharged obligation {obligation} \
                 (lattice-certified: {})",
                trust_cg_lower::lattice_guard::is_lattice_obligation_id(obligation as u64)
            ),
            None => "Eliminated exact bounds check guard using InBounds proof".to_string(),
        };
        self.push_applied_certificate(
            func,
            ProofAnnotation::InBounds,
            description,
            inst_id,
            AppliedCertificateDetails {
                affected_insts: vec![],
                kind: OptCertificateKind::GuardEliminated,
                source_region_hash,
                target_region: &[],
            },
        );
        self.stats.bounds_checks_eliminated += 1;
        true
    }

    /// NotNull optimization: when trust_ir proves a pointer is not null,
    /// eliminate the null check guard.
    ///
    /// Pattern: `TrapNullIfZero ptr` [NotNull]
    /// Result:  instruction removed
    fn apply_not_null(
        &mut self,
        func: &mut MachFunction,
        block_insts: &[InstId],
        pos: usize,
        to_delete: &mut HashSet<InstId>,
        provenance: Option<&mut ProvenanceMap>,
    ) -> bool {
        let inst_id = block_insts[pos];
        let opcode = func.inst(inst_id).opcode;

        match opcode {
            AArch64Opcode::TrapNullIfZero => {
                // Sentinel S4: kernel-gated deletion (see apply_in_bounds).
                if self.kernel_gate && self.kernel_authorizes(func, inst_id).is_none() {
                    return false;
                }
                let source_region_hash = self.source_region_hash(func, inst_id, &[inst_id]);
                to_delete.insert(inst_id);
                if let Some(provenance) = provenance {
                    provenance.record_deletion(
                        inst_id,
                        proof_opts_pass_id(),
                        "NotNull proof eliminated null-check guard",
                    );
                }
                self.push_applied_certificate(
                    func,
                    ProofAnnotation::NotNull,
                    "Eliminated null check guard using NotNull proof",
                    inst_id,
                    AppliedCertificateDetails {
                        affected_insts: vec![],
                        kind: OptCertificateKind::GuardEliminated,
                        source_region_hash,
                        target_region: &[],
                    },
                );
                self.stats.null_checks_eliminated += 1;
                true
            }
            _ => false,
        }
    }

    /// ValidBorrow optimization: when trust_ir proves a borrow is valid,
    /// refine the memory aliasing model to allow reordering.
    ///
    /// For loads/stores with ValidBorrow proof, we remove the memory
    /// side-effect flags that would normally prevent reordering. This
    /// allows CSE and LICM to treat these memory operations more
    /// aggressively.
    ///
    /// Specifically: a load with ValidBorrow can be treated as non-aliasing
    /// with other ValidBorrow stores, enabling the load to be hoisted or
    /// CSE'd even past intervening stores.
    fn apply_valid_borrow(
        &mut self,
        func: &mut MachFunction,
        inst_id: InstId,
        provenance: Option<&mut ProvenanceMap>,
    ) -> ValidBorrowApplyResult {
        let inst = func.inst(inst_id);

        // ValidBorrow applies to loads and stores.
        if !inst.reads_memory() && !inst.writes_memory() {
            return ValidBorrowApplyResult::NotMemory;
        }

        if inst.flags.contains(InstFlags::PROOF_REORDERABLE) {
            return ValidBorrowApplyResult::AlreadyRefined;
        }

        let source_region_hash = self.source_region_hash(func, inst_id, &[inst_id]);

        // Mark the instruction as proof-reorderable. This flag tells
        // subsequent passes (CSE, LICM) that this memory operation can
        // be safely reordered past other memory operations because the
        // borrow validity has been formally proven.
        let inst = func.inst_mut(inst_id);
        inst.flags.insert(InstFlags::PROOF_REORDERABLE);

        if let Some(provenance) = provenance {
            provenance.record_in_place_transform(inst_id, proof_opts_pass_id());
        }

        self.push_applied_certificate(
            func,
            ProofAnnotation::ValidBorrow,
            "Refined memory-operation flags using ValidBorrow proof",
            inst_id,
            AppliedCertificateDetails {
                affected_insts: vec![],
                kind: OptCertificateKind::FlagsRefined,
                source_region_hash,
                target_region: &[inst_id],
            },
        );
        self.stats.alias_refinements += 1;
        ValidBorrowApplyResult::Applied
    }

    /// PositiveRefCount optimization: when trust_ir proves the reference count
    /// is positive, eliminate redundant retain/release pairs.
    ///
    /// Pattern: `Retain ptr` [PositiveRefCount] ... `Release ptr`
    /// Result:  both instructions removed
    ///
    /// When we encounter a Retain with PositiveRefCount proof, we scan
    /// forward for a matching Release on the same pointer. If found with
    /// no intervening calls or other retains/releases on the same pointer,
    /// both are eliminated.
    fn apply_positive_refcount(
        &mut self,
        func: &mut MachFunction,
        block_insts: &[InstId],
        pos: usize,
        to_delete: &mut HashSet<InstId>,
        provenance: Option<&mut ProvenanceMap>,
    ) -> bool {
        let inst_id = block_insts[pos];
        if func.inst(inst_id).opcode != AArch64Opcode::Retain {
            return false;
        }

        // Get the pointer operand of the retain.
        let retain_ptr = func.inst(inst_id).operands.first().cloned();
        let retain_ptr = match retain_ptr {
            Some(op) => op,
            None => return false,
        };

        // Scan forward for a matching Release on the same pointer.
        for &later_id in &block_insts[pos + 1..] {
            let later = func.inst(later_id);

            // If we hit a call, stop — it might observe the refcount.
            if later.is_call() {
                break;
            }

            // If we hit another Retain or Release on the same pointer
            // (not the match we're looking for), stop to avoid complexity.
            if later.opcode == AArch64Opcode::Retain && later.operands.first() == Some(&retain_ptr)
            {
                break;
            }

            if later.opcode == AArch64Opcode::Release && later.operands.first() == Some(&retain_ptr)
            {
                let source_region_hash =
                    self.source_region_hash(func, inst_id, &[inst_id, later_id]);
                // Found matching release. Remove both.
                to_delete.insert(inst_id);
                to_delete.insert(later_id);
                if let Some(provenance) = provenance {
                    let pass = proof_opts_pass_id();
                    provenance.record_deletion(
                        inst_id,
                        pass.clone(),
                        "PositiveRefCount proof eliminated retain/release pair",
                    );
                    provenance.record_deletion(
                        later_id,
                        pass,
                        "PositiveRefCount proof eliminated retain/release pair",
                    );
                }
                self.push_applied_certificate(
                    func,
                    ProofAnnotation::PositiveRefCount,
                    "Eliminated retain/release pair using PositiveRefCount proof",
                    inst_id,
                    AppliedCertificateDetails {
                        affected_insts: vec![later_id],
                        kind: OptCertificateKind::PairEliminated,
                        source_region_hash,
                        target_region: &[],
                    },
                );
                self.stats.refcount_pairs_eliminated += 1;
                return true;
            }
        }

        false
    }

    /// NonZeroDivisor optimization: when trust_ir proves the divisor is non-zero,
    /// eliminate the division-by-zero guard.
    ///
    /// Primary pattern (the clean DivZero mirror of `apply_not_null`'s NotNull):
    ///   `TrapDivZeroIfZero divisor` [NonZeroDivisor]
    ///   Result: the self-contained carrier is removed.
    ///
    /// Legacy pattern (retained for backwards-compat; no longer emitted by the
    /// production AArch64 ISel, which now emits the self-contained carrier above):
    ///   `CMP divisor, #0` [NonZeroDivisor] + `TrapDivZero`
    ///   Result: both instructions removed.
    ///
    /// Legacy `CBZ` and the bare `TrapDivZero` panic trap are intentionally not
    /// consumers. DivNonZero facts must arrive through the exact proof-only
    /// guard emitted from trust_ir so the optimizer never infers divisor identity
    /// from nearby machine shape.
    ///
    /// On AArch64, division by zero yields zero (not a fault), but the
    /// trust_ir runtime model may still insert guards when the source language
    /// semantics require a trap. With the NonZeroDivisor proof, the guard
    /// is provably dead code.
    fn apply_non_zero_divisor(
        &mut self,
        func: &mut MachFunction,
        block_insts: &[InstId],
        pos: usize,
        to_delete: &mut HashSet<InstId>,
        provenance: Option<&mut ProvenanceMap>,
    ) -> bool {
        let inst_id = block_insts[pos];
        let opcode = func.inst(inst_id).opcode;

        match opcode {
            AArch64Opcode::TrapDivZeroIfZero => {
                // Sentinel S4: kernel-gated deletion (see apply_in_bounds / apply_not_null). With the
                // gate on, the self-contained `TrapDivZeroIfZero divisor` carrier is removed ONLY when
                // the Certified-Elimination Kernel authorizes it (a discharged obligation bound to this
                // carrier by its [divisor] fingerprint). With the gate off, the legacy syntactic path
                // removes it unconditionally — exactly as it does for the InBounds/NotNull carriers.
                if self.kernel_gate && self.kernel_authorizes(func, inst_id).is_none() {
                    return false;
                }
                let source_region_hash = self.source_region_hash(func, inst_id, &[inst_id]);
                to_delete.insert(inst_id);
                if let Some(provenance) = provenance {
                    provenance.record_deletion(
                        inst_id,
                        proof_opts_pass_id(),
                        "NonZeroDivisor proof eliminated div-zero guard",
                    );
                }
                self.push_applied_certificate(
                    func,
                    ProofAnnotation::NonZeroDivisor,
                    "Eliminated division-by-zero guard using NonZeroDivisor proof",
                    inst_id,
                    AppliedCertificateDetails {
                        affected_insts: vec![],
                        kind: OptCertificateKind::GuardEliminated,
                        source_region_hash,
                        target_region: &[],
                    },
                );
                self.stats.divzero_checks_eliminated += 1;
                true
            }
            AArch64Opcode::CmpRI => {
                // Check if comparing against zero (div-zero check pattern).
                let is_zero_check = func
                    .inst(inst_id)
                    .operands
                    .last()
                    .map(|op| matches!(op, MachOperand::Imm(0)))
                    .unwrap_or(false);

                if is_zero_check {
                    // Look for the exact proof-only TrapDivZero carrier.
                    if pos + 1 < block_insts.len() {
                        let next_id = block_insts[pos + 1];
                        let next_opcode = func.inst(next_id).opcode;
                        if next_opcode == AArch64Opcode::TrapDivZero {
                            // Sentinel S4 (#6 strict-subset): under the kernel gate, refuse to
                            // delete this legacy paired shape unless the kernel authorizes it. The
                            // identity lives on the TRAP carrier (next_id), but bare TrapDivZero is
                            // not a kernel carrier (classify_carrier => None), so authorization
                            // always fails => KEEP. This makes the gate a true strict subset across
                            // ALL shapes. Gate-OFF (default) preserves the legacy delete exactly.
                            if self.kernel_gate && self.kernel_authorizes(func, next_id).is_none() {
                                return false;
                            }
                            let source_region_hash =
                                self.source_region_hash(func, inst_id, &[inst_id, next_id]);
                            to_delete.insert(inst_id);
                            to_delete.insert(next_id);
                            if let Some(provenance) = provenance {
                                let pass = proof_opts_pass_id();
                                provenance.record_deletion(
                                    inst_id,
                                    pass.clone(),
                                    "NonZeroDivisor proof eliminated div-zero guard compare",
                                );
                                provenance.record_deletion(
                                    next_id,
                                    pass,
                                    "NonZeroDivisor proof eliminated div-zero guard trap",
                                );
                            }
                            self.push_applied_certificate(
                                func,
                                ProofAnnotation::NonZeroDivisor,
                                "Eliminated division-by-zero guard using NonZeroDivisor proof",
                                inst_id,
                                AppliedCertificateDetails {
                                    affected_insts: vec![next_id],
                                    kind: OptCertificateKind::GuardEliminated,
                                    source_region_hash,
                                    target_region: &[],
                                },
                            );
                            self.stats.divzero_checks_eliminated += 1;
                            return true;
                        }
                    }
                }
                false
            }
            _ => false,
        }
    }

    /// ValidShift optimization: when trust_ir proves the shift amount is in
    /// [0, bitwidth), eliminate the shift-amount range check.
    ///
    /// Pattern 1: `CMP shift_amt, #64` [ValidShift] + `TrapShiftRange trap_block`
    /// Result:    both instructions removed
    ///
    /// Pattern 2: `CMP shift_amt, #32/#64` [ValidShift] + `BCond HS, trap_block`
    /// Result:    both instructions removed
    ///
    /// Pattern 3: `TrapShiftRange trap_block` [ValidShift]
    /// Result:    instruction removed
    ///
    /// On AArch64, shift amounts outside [0, bitwidth) produce
    /// implementation-defined results. The trust_ir runtime model inserts
    /// range checks when required by source-language semantics. With
    /// the ValidShift proof, the check is provably dead.
    fn apply_valid_shift(
        &mut self,
        func: &mut MachFunction,
        block_insts: &[InstId],
        pos: usize,
        to_delete: &mut HashSet<InstId>,
        provenance: Option<&mut ProvenanceMap>,
    ) -> bool {
        let inst_id = block_insts[pos];
        let opcode = func.inst(inst_id).opcode;

        match opcode {
            AArch64Opcode::CmpRI => {
                // Check if comparing against a bitwidth (32 or 64).
                let is_shift_range_check = func
                    .inst(inst_id)
                    .operands
                    .last()
                    .map(|op| matches!(op, MachOperand::Imm(32) | MachOperand::Imm(64)))
                    .unwrap_or(false);

                if is_shift_range_check {
                    // Look for trailing BCond or TrapShiftRange.
                    if pos + 1 < block_insts.len() {
                        let next_id = block_insts[pos + 1];
                        let next_opcode = func.inst(next_id).opcode;
                        if next_opcode == AArch64Opcode::TrapShiftRange
                            || bcond_has_condition(func.inst(next_id), CondCode::HS)
                        {
                            // Sentinel S4 (#6 strict-subset): under the kernel gate, refuse to
                            // delete this legacy paired shape. Neither bare TrapShiftRange nor BCond
                            // is a kernel carrier (classify_carrier recognizes only
                            // TrapShiftRangeIfOOB), so there is no kernel-recognized carrier
                            // identity to authorize against => KEEP. Gate-OFF (default) preserves
                            // the legacy delete exactly.
                            if self.kernel_gate {
                                return false;
                            }
                            let source_region_hash =
                                self.source_region_hash(func, inst_id, &[inst_id, next_id]);
                            to_delete.insert(inst_id);
                            to_delete.insert(next_id);
                            if let Some(provenance) = provenance {
                                let pass = proof_opts_pass_id();
                                provenance.record_deletion(
                                    inst_id,
                                    pass.clone(),
                                    "ValidShift proof eliminated shift-range guard compare",
                                );
                                provenance.record_deletion(
                                    next_id,
                                    pass,
                                    "ValidShift proof eliminated shift-range guard branch",
                                );
                            }
                            self.push_applied_certificate(
                                func,
                                ProofAnnotation::ValidShift,
                                "Eliminated shift-range guard using ValidShift proof",
                                inst_id,
                                AppliedCertificateDetails {
                                    affected_insts: vec![next_id],
                                    kind: OptCertificateKind::GuardEliminated,
                                    source_region_hash,
                                    target_region: &[],
                                },
                            );
                            self.stats.shift_checks_eliminated += 1;
                            return true;
                        }
                    }
                }
                false
            }
            AArch64Opcode::TrapShiftRangeIfOOB => {
                // Production carrier: self-contained `TrapShiftRangeIfOOB amount, bitwidth` (the
                // ShiftRange mirror of the InBounds `TrapBoundsCheckExact` carrier). Sentinel S4:
                // when the kernel gate is on, delete only if the Certified-Elimination Kernel
                // authorizes it (a discharged obligation bound to this carrier by its
                // [amount, Imm(bitwidth)] fingerprint). With the gate off, the legacy syntactic path
                // removes it unconditionally — exactly as it does for the InBounds carrier. An
                // unproven carrier is KEPT.
                if self.kernel_gate && self.kernel_authorizes(func, inst_id).is_none() {
                    return false;
                }
                let source_region_hash = self.source_region_hash(func, inst_id, &[inst_id]);
                to_delete.insert(inst_id);
                if let Some(provenance) = provenance {
                    provenance.record_deletion(
                        inst_id,
                        proof_opts_pass_id(),
                        "ValidShift proof eliminated shift-range guard",
                    );
                }
                self.push_applied_certificate(
                    func,
                    ProofAnnotation::ValidShift,
                    "Eliminated shift-range guard using ValidShift proof",
                    inst_id,
                    AppliedCertificateDetails {
                        affected_insts: vec![],
                        kind: OptCertificateKind::GuardEliminated,
                        source_region_hash,
                        target_region: &[],
                    },
                );
                self.stats.shift_checks_eliminated += 1;
                true
            }
            AArch64Opcode::TrapShiftRange => {
                // Legacy bare pseudo (no longer emitted by the production ISel, which now emits the
                // self-contained `TrapShiftRangeIfOOB` above). Retained for backwards-compat. NOTE:
                // this bare trap carries NO operand identity, so it is NOT a kernel carrier and is
                // only reached on the legacy syntactic path.
                //
                // Sentinel S4 (#6 strict-subset): this shape carries no operand identity, so the
                // kernel cannot certify it. Under the gate, KEEP rather than eliminate unconsulted.
                // Gate-OFF (default) preserves the legacy delete exactly.
                if self.kernel_gate {
                    return false;
                }
                let source_region_hash = self.source_region_hash(func, inst_id, &[inst_id]);
                to_delete.insert(inst_id);
                if let Some(provenance) = provenance {
                    provenance.record_deletion(
                        inst_id,
                        proof_opts_pass_id(),
                        "ValidShift proof eliminated shift-range guard",
                    );
                }
                self.push_applied_certificate(
                    func,
                    ProofAnnotation::ValidShift,
                    "Eliminated shift-range guard using ValidShift proof",
                    inst_id,
                    AppliedCertificateDetails {
                        affected_insts: vec![],
                        kind: OptCertificateKind::GuardEliminated,
                        source_region_hash,
                        target_region: &[],
                    },
                );
                self.stats.shift_checks_eliminated += 1;
                true
            }
            _ => false,
        }
    }

    /// Pure optimization: when trust_ir proves an operation is pure (no observable
    /// side effects, deterministic), promote it for aggressive CSE.
    ///
    /// A load with a Pure proof annotation means the loaded memory location
    /// is immutable (e.g., a read from a frozen/constant data structure).
    /// This enables:
    ///
    /// 1. **Aggressive CSE**: Two loads from the same address can be CSE'd
    ///    even with intervening stores (the Pure proof guarantees the loaded
    ///    value does not change).
    /// 2. **LICM**: Pure loads can be hoisted out of loops.
    ///
    /// Implementation: remove the READS_MEMORY/WRITES_MEMORY and
    /// HAS_SIDE_EFFECTS flags, making the instruction appear pure to
    /// downstream CSE/LICM passes. The proof annotation is consumed.
    fn apply_pure(
        &mut self,
        func: &mut MachFunction,
        inst_id: InstId,
        provenance: Option<&mut ProvenanceMap>,
    ) -> bool {
        let inst = func.inst(inst_id);

        // Pure proof is meaningful for loads (promotes them to CSE-able).
        // For already-pure instructions, no change needed.
        if !inst.reads_memory() && !inst.writes_memory() && !inst.has_side_effects() {
            return false;
        }

        let source_region_hash = self.source_region_hash(func, inst_id, &[inst_id]);

        // Promote the instruction: remove memory flags so CSE/LICM treat
        // it as pure. Keep the instruction opcode and operands unchanged.
        let inst = func.inst_mut(inst_id);
        inst.flags.remove(InstFlags::READS_MEMORY);
        inst.flags.remove(InstFlags::WRITES_MEMORY);
        inst.flags.remove(InstFlags::HAS_SIDE_EFFECTS);
        inst.proof = None; // Proof consumed.

        if let Some(provenance) = provenance {
            provenance.record_in_place_transform(inst_id, proof_opts_pass_id());
        }

        self.push_applied_certificate(
            func,
            ProofAnnotation::Pure,
            "Refined instruction flags using Pure proof",
            inst_id,
            AppliedCertificateDetails {
                affected_insts: vec![],
                kind: OptCertificateKind::FlagsRefined,
                source_region_hash,
                target_region: &[inst_id],
            },
        );
        self.stats.pure_cse_enabled += 1;
        true
    }
}

fn proof_annotation_stable_name(annotation: ProofAnnotation) -> &'static str {
    match annotation {
        ProofAnnotation::NoOverflow => "NoOverflow",
        ProofAnnotation::NoSignedOverflow => "NoSignedOverflow",
        ProofAnnotation::NoUnsignedOverflow => "NoUnsignedOverflow",
        ProofAnnotation::InBounds => "InBounds",
        ProofAnnotation::NotNull => "NotNull",
        ProofAnnotation::ValidBorrow => "ValidBorrow",
        ProofAnnotation::PositiveRefCount => "PositiveRefCount",
        ProofAnnotation::NonZeroDivisor => "NonZeroDivisor",
        ProofAnnotation::ValidShift => "ValidShift",
        ProofAnnotation::Pure => "Pure",
        ProofAnnotation::Associative => "Associative",
        ProofAnnotation::Commutative => "Commutative",
        ProofAnnotation::Idempotent => "Idempotent",
    }
}

fn proof_divergence_stable_name(divergence: ProofDivergence) -> &'static str {
    match divergence {
        ProofDivergence::Uniform => "Uniform",
        ProofDivergence::Low => "Low",
        ProofDivergence::High => "High",
    }
}

fn transform_name(annotation: ProofAnnotation, kind: &OptCertificateKind) -> &'static str {
    match (annotation, kind) {
        (ProofAnnotation::NoOverflow, OptCertificateKind::CheckedToUnchecked) => {
            "proof-opts.no-overflow.checked-to-unchecked"
        }
        (ProofAnnotation::NoSignedOverflow, OptCertificateKind::CheckedToUnchecked) => {
            "proof-opts.no-signed-overflow.checked-to-unchecked"
        }
        (ProofAnnotation::NoUnsignedOverflow, OptCertificateKind::CheckedToUnchecked) => {
            "proof-opts.no-unsigned-overflow.checked-to-unchecked"
        }
        (ProofAnnotation::InBounds, OptCertificateKind::GuardEliminated) => {
            "proof-opts.in-bounds.guard-eliminated"
        }
        (ProofAnnotation::NotNull, OptCertificateKind::GuardEliminated) => {
            "proof-opts.not-null.guard-eliminated"
        }
        (ProofAnnotation::NotNull, OptCertificateKind::BranchSimplified) => {
            "proof-opts.not-null.branch-simplified"
        }
        (ProofAnnotation::ValidBorrow, OptCertificateKind::FlagsRefined) => {
            "proof-opts.valid-borrow.flags-refined"
        }
        (ProofAnnotation::PositiveRefCount, OptCertificateKind::PairEliminated) => {
            "proof-opts.positive-refcount.pair-eliminated"
        }
        (_, OptCertificateKind::PairCombined) => "proof-opts.aligned.pair-combined",
        (ProofAnnotation::NonZeroDivisor, OptCertificateKind::GuardEliminated) => {
            "proof-opts.non-zero-divisor.guard-eliminated"
        }
        (ProofAnnotation::ValidShift, OptCertificateKind::GuardEliminated) => {
            "proof-opts.valid-shift.guard-eliminated"
        }
        (ProofAnnotation::Pure, OptCertificateKind::FlagsRefined) => {
            "proof-opts.pure.flags-refined"
        }
        (ProofAnnotation::Associative, _) => "proof-opts.associative.metadata-only",
        (ProofAnnotation::Commutative, _) => "proof-opts.commutative.metadata-only",
        (ProofAnnotation::Idempotent, _) => "proof-opts.idempotent.metadata-only",
        _ => "proof-opts.unknown",
    }
}

fn default_certificate_kind(annotation: ProofAnnotation) -> OptCertificateKind {
    match annotation {
        ProofAnnotation::NoOverflow
        | ProofAnnotation::NoSignedOverflow
        | ProofAnnotation::NoUnsignedOverflow => OptCertificateKind::CheckedToUnchecked,
        ProofAnnotation::InBounds
        | ProofAnnotation::NotNull
        | ProofAnnotation::NonZeroDivisor
        | ProofAnnotation::ValidShift => OptCertificateKind::GuardEliminated,
        ProofAnnotation::ValidBorrow
        | ProofAnnotation::Pure
        | ProofAnnotation::Associative
        | ProofAnnotation::Commutative
        | ProofAnnotation::Idempotent => OptCertificateKind::FlagsRefined,
        ProofAnnotation::PositiveRefCount => OptCertificateKind::PairEliminated,
    }
}

fn region_hash(func: &MachFunction, inst_ids: &[InstId]) -> u128 {
    let mut h = StableHasher::new();
    h.write_str("proof-opts.region.v2");
    h.write_str(&func.name);
    h.write_u64(inst_ids.len() as u64);
    for inst_id in inst_ids {
        hash_inst(&mut h, func.inst(*inst_id));
    }
    h.finish128()
}

fn source_trust_ir_region_hash(function_name: &str, origins: &[TrustIrInstId]) -> u128 {
    let mut h = StableHasher::new();
    h.write_str("proof-opts.source-trust_ir-region.v1");
    h.write_str(function_name);
    h.write_u64(origins.len() as u64);
    for origin in origins {
        h.write_u32(origin.0);
    }
    h.finish128()
}

fn combined_source_region_identity_hash(function_name: &str, source_hashes: &[u128]) -> u128 {
    let mut h = StableHasher::new();
    h.write_str("proof-opts.combined-source-region-identities.v1");
    h.write_str(function_name);
    h.write_u64(source_hashes.len() as u64);
    for source_hash in source_hashes {
        write_u128(&mut h, *source_hash);
    }
    h.finish128()
}

fn hash_inst(h: &mut StableHasher, inst: &MachInst) {
    h.write_str("mach-inst.v1");
    h.write_str(&format!("{:?}", inst.opcode));
    h.write_u64(u64::from(inst.flags.bits()));
    hash_optional_annotation(h, inst.proof);

    h.write_u64(inst.operands.len() as u64);
    for operand in &inst.operands {
        hash_operand(h, operand);
    }

    h.write_u64(inst.implicit_defs.len() as u64);
    for reg in inst.implicit_defs {
        h.write_u64(u64::from(reg.encoding()));
    }

    h.write_u64(inst.implicit_uses.len() as u64);
    for reg in inst.implicit_uses {
        h.write_u64(u64::from(reg.encoding()));
    }

    match inst.source_loc {
        Some(loc) => {
            h.write_u8(1);
            h.write_u32(loc.file);
            h.write_u32(loc.line);
            h.write_u32(loc.col);
        }
        None => h.write_u8(0),
    }
}

fn hash_operand(h: &mut StableHasher, operand: &MachOperand) {
    match operand {
        MachOperand::VReg(vreg) => {
            h.write_u8(0);
            h.write_u32(vreg.id);
            hash_reg_class(h, vreg.class);
        }
        MachOperand::PReg(reg) => {
            h.write_u8(1);
            h.write_u64(u64::from(reg.encoding()));
        }
        MachOperand::Imm(value) => {
            h.write_u8(2);
            h.write(&value.to_le_bytes());
        }
        MachOperand::FImm(value) => {
            h.write_u8(3);
            h.write_u64(value.to_bits());
        }
        MachOperand::Block(block) => {
            h.write_u8(4);
            h.write_u32(block.0);
        }
        MachOperand::StackSlot(slot) => {
            h.write_u8(5);
            h.write_u32(slot.0);
        }
        MachOperand::FrameIndex(frame) => {
            h.write_u8(6);
            h.write(&frame.0.to_le_bytes());
        }
        MachOperand::MemOp { base, offset } => {
            h.write_u8(7);
            h.write_u64(u64::from(base.encoding()));
            h.write(&offset.to_le_bytes());
        }
        MachOperand::Special(reg) => {
            h.write_u8(8);
            hash_special_reg(h, *reg);
        }
        MachOperand::Symbol(symbol) => {
            h.write_u8(9);
            h.write_str(symbol);
        }
        MachOperand::JumpTableIndex(index) => {
            h.write_u8(10);
            h.write_u32(*index);
        }
        MachOperand::IncomingArg(offset) => {
            h.write_u8(11);
            h.write(&offset.to_le_bytes());
        }
    }
}

fn hash_reg_class(h: &mut StableHasher, class: RegClass) {
    let tag = match class {
        RegClass::Gpr64 => 0,
        RegClass::Gpr32 => 1,
        RegClass::Fpr128 => 2,
        RegClass::Fpr64 => 3,
        RegClass::Fpr32 => 4,
        RegClass::Fpr16 => 5,
        RegClass::Fpr8 => 6,
        RegClass::System => 7,
    };
    h.write_u8(tag);
}

fn hash_special_reg(h: &mut StableHasher, reg: SpecialReg) {
    let tag = match reg {
        SpecialReg::SP => 0,
        SpecialReg::XZR => 1,
        SpecialReg::WZR => 2,
    };
    h.write_u8(tag);
}

fn proof_hash(annotation: ProofAnnotation, facts: &[OptConsumedProofFact]) -> u128 {
    let mut h = StableHasher::new();
    h.write_str("proof-opts.proof.v1");
    h.write_str(proof_annotation_stable_name(annotation));
    h.write_u64(facts.len() as u64);
    for fact in facts {
        hash_consumed_fact(&mut h, *fact);
    }
    h.finish128()
}

fn fact_only_proof_hash(facts: &[OptConsumedProofFact]) -> u128 {
    let mut h = StableHasher::new();
    h.write_str("proof-opts.fact-only-proof.v1");
    h.write_u64(facts.len() as u64);
    for fact in facts {
        hash_consumed_fact(&mut h, *fact);
    }
    h.finish128()
}

fn hash_consumed_fact(h: &mut StableHasher, fact: OptConsumedProofFact) {
    match fact {
        OptConsumedProofFact::LegacyAnnotation(annotation) => {
            h.write_u8(0);
            h.write_str(proof_annotation_stable_name(annotation));
        }
        OptConsumedProofFact::ProofFact(proof_fact) => {
            h.write_u8(1);
            h.write_str(proof_fact.stable_name());
            match proof_fact {
                ProofFact::Aligned(bytes) => {
                    h.write_u8(1);
                    h.write_u64(bytes);
                }
                ProofFact::BoundedLoop(bound) => {
                    h.write_u8(2);
                    h.write_u64(bound);
                }
                ProofFact::DivergenceClass(divergence) => {
                    h.write_u8(3);
                    h.write_str(proof_divergence_stable_name(divergence));
                }
                _ => h.write_u8(0),
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn validation_hash(
    transform: &OptTransformIdentity,
    route: &OptAdmissionRoute,
    kind: &OptCertificateKind,
    source_region_hash: u128,
    target_region_hash: u128,
    proof_hash: u128,
    rejection: Option<&OptRejection>,
) -> u128 {
    let mut h = StableHasher::new();
    h.write_str("proof-opts.validation.v2");
    h.write_str(&transform.name);
    h.write_u32(transform.version);
    h.write_str(&route.pass);
    h.write_str(&route.admission);
    hash_kind(&mut h, kind);
    write_u128(&mut h, source_region_hash);
    write_u128(&mut h, target_region_hash);
    write_u128(&mut h, proof_hash);
    match rejection {
        Some(rejection) => {
            h.write_u8(1);
            h.write_str(rejection.code.as_str());
            h.write_str(&rejection.fact);
            h.write_str(&rejection.detail);
        }
        None => h.write_u8(0),
    }
    h.finish128()
}

fn certificate_id(
    transform: &OptTransformIdentity,
    source_region_hash: u128,
    target_region_hash: u128,
    proof_hash: u128,
    validation_hash: u128,
) -> u128 {
    let mut h = StableHasher::new();
    h.write_str("proof-opts.certificate-id.v2");
    h.write_str(&transform.name);
    h.write_u32(transform.version);
    write_u128(&mut h, source_region_hash);
    write_u128(&mut h, target_region_hash);
    write_u128(&mut h, proof_hash);
    write_u128(&mut h, validation_hash);
    h.finish128()
}

fn hash_optional_annotation(h: &mut StableHasher, annotation: Option<ProofAnnotation>) {
    match annotation {
        Some(annotation) => {
            h.write_u8(1);
            h.write_str(proof_annotation_stable_name(annotation));
        }
        None => h.write_u8(0),
    }
}

fn hash_kind(h: &mut StableHasher, kind: &OptCertificateKind) {
    let stable = match kind {
        OptCertificateKind::CheckedToUnchecked => "checked-to-unchecked",
        OptCertificateKind::GuardEliminated => "guard-eliminated",
        OptCertificateKind::BranchSimplified => "branch-simplified",
        OptCertificateKind::FlagsRefined => "flags-refined",
        OptCertificateKind::PairEliminated => "pair-eliminated",
        OptCertificateKind::PairCombined => "pair-combined",
    };
    h.write_str(stable);
}

fn write_u128(h: &mut StableHasher, value: u128) {
    h.write(&value.to_le_bytes());
}

enum AlignedPairCandidate {
    Combine(MachInst),
    Reject(AlignedPairRejection),
    NotCandidate,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AlignedPairRejection {
    PairStartNotAligned16,
    PairOffsetOutOfRange,
    LoadRegisterOverlap,
}

impl AlignedPairRejection {
    fn detail(self) -> &'static str {
        match self {
            AlignedPairRejection::PairStartNotAligned16 => {
                "pair-start address is not proven by an Aligned(N) fact that implies 16-byte alignment"
            }
            AlignedPairRejection::PairOffsetOutOfRange => {
                "pair offset is outside signed scaled AArch64 pair range"
            }
            AlignedPairRejection::LoadRegisterOverlap => {
                "load pair destination overlaps its base register"
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PairMemKind {
    Load,
    Store,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PairReg {
    PReg(PReg),
    VReg(VReg),
}

impl PairReg {
    fn from_transfer_operand(operand: &MachOperand) -> Option<Self> {
        match operand {
            MachOperand::PReg(reg) if is_real_x_gpr(*reg) => Some(Self::PReg(*reg)),
            MachOperand::VReg(vreg) if vreg.class == RegClass::Gpr64 => Some(Self::VReg(*vreg)),
            _ => None,
        }
    }

    fn to_operand(self) -> MachOperand {
        match self {
            PairReg::PReg(reg) => MachOperand::PReg(reg),
            PairReg::VReg(vreg) => MachOperand::VReg(vreg),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PairBase {
    PReg(PReg),
    VReg(VReg),
    Special(SpecialReg),
}

impl PairBase {
    fn to_operand(self) -> MachOperand {
        match self {
            PairBase::PReg(reg) => MachOperand::PReg(reg),
            PairBase::VReg(vreg) => MachOperand::VReg(vreg),
            PairBase::Special(reg) => MachOperand::Special(reg),
        }
    }

    fn is_reg(self, reg: PairReg) -> bool {
        matches!(
            (self, reg),
            (PairBase::PReg(base), PairReg::PReg(reg)) if base == reg
        ) || matches!(
            (self, reg),
            (PairBase::VReg(base), PairReg::VReg(reg)) if base == reg
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PairMemOp {
    kind: PairMemKind,
    rt: PairReg,
    base: PairBase,
    offset: i64,
}

impl PairMemOp {
    fn from_inst(inst: &MachInst) -> Option<Self> {
        let kind = match inst.opcode {
            AArch64Opcode::LdrRI => PairMemKind::Load,
            AArch64Opcode::StrRI => PairMemKind::Store,
            _ => return None,
        };
        let rt = PairReg::from_transfer_operand(inst.operands.first()?)?;
        let (base, offset) = base_offset_operands(inst)?;
        Some(Self {
            kind,
            rt,
            base,
            offset,
        })
    }
}

fn base_offset_operands(inst: &MachInst) -> Option<(PairBase, i64)> {
    match inst.operands.get(1)? {
        MachOperand::PReg(reg) if is_real_x_gpr(*reg) => {
            Some((PairBase::PReg(*reg), immediate_offset(inst, 2)?))
        }
        MachOperand::VReg(vreg) if vreg.class == RegClass::Gpr64 => {
            Some((PairBase::VReg(*vreg), immediate_offset(inst, 2)?))
        }
        MachOperand::Special(SpecialReg::SP) => Some((
            PairBase::Special(SpecialReg::SP),
            immediate_offset(inst, 2)?,
        )),
        MachOperand::MemOp { base, offset } if is_real_x_gpr(*base) => {
            Some((PairBase::PReg(*base), *offset))
        }
        _ => None,
    }
}

fn is_real_x_gpr(reg: PReg) -> bool {
    reg.encoding() <= 30
}

fn immediate_offset(inst: &MachInst, idx: usize) -> Option<i64> {
    match inst.operands.get(idx) {
        Some(MachOperand::Imm(offset)) => Some(*offset),
        None => Some(0),
        _ => None,
    }
}

fn pair_offset_is_encodable(offset: i64) -> bool {
    offset % 8 == 0 && (-64..=63).contains(&(offset / 8))
}

fn load_pair_has_unsafe_register_overlap(first: PairMemOp, second: PairMemOp) -> bool {
    first.rt == second.rt || first.base.is_reg(first.rt) || first.base.is_reg(second.rt)
}

// ---------------------------------------------------------------------------
// Public API: named functions for each proof-consuming optimization
// ---------------------------------------------------------------------------

/// Eliminate overflow checks when NoOverflow proof is present.
///
/// Converts checked arithmetic (ADDS/SUBS) to unchecked (ADD/SUB) and
/// removes trailing TrapOverflow instructions.
///
/// Returns the number of overflow checks eliminated.
pub fn eliminate_overflow_checks(func: &mut MachFunction) -> u32 {
    let mut pass = ProofOptimization::new();
    pass.run(func);
    pass.stats().overflow_checks_eliminated
}

/// Eliminate bounds checks when InBounds proof is present.
///
/// Removes exact proof-only bounds guard carriers when the index is proven
/// in-bounds. Legacy CMP+TrapBoundsCheck shapes are not InBounds consumers.
///
/// Returns the number of bounds checks eliminated.
pub fn eliminate_bounds_checks(func: &mut MachFunction) -> u32 {
    let mut pass = ProofOptimization::new();
    pass.run(func);
    pass.stats().bounds_checks_eliminated
}

/// Eliminate null checks when NotNull proof is present.
///
/// Removes exact `TrapNullIfZero ptr` guards when the pointer is proven
/// non-null. Legacy `CBZ`/`CBNZ`, bare `TrapNull`, and `CMP+TrapNull`
/// shapes are not NotNull consumers.
///
/// Returns the number of null checks eliminated.
pub fn eliminate_null_checks(func: &mut MachFunction) -> u32 {
    let mut pass = ProofOptimization::new();
    pass.run(func);
    pass.stats().null_checks_eliminated
}

/// Enable load/store reordering when ValidBorrow proof is present.
///
/// Marks proven-valid memory operations with `PROOF_REORDERABLE` flag,
/// allowing CSE and LICM to reorder them past other memory operations.
///
/// Returns the number of alias refinements applied.
pub fn enable_load_store_reorder(func: &mut MachFunction) -> u32 {
    let mut pass = ProofOptimization::new();
    pass.run(func);
    pass.stats().alias_refinements
}

/// Enable aggressive CSE for operations with Pure proof annotation.
///
/// Removes memory flags from proven-pure operations (e.g., loads from
/// immutable data) so they can be CSE'd and LICM'd like pure computations.
///
/// Returns the number of operations promoted to pure.
pub fn aggressive_cse(func: &mut MachFunction) -> u32 {
    let mut pass = ProofOptimization::new();
    pass.run(func);
    pass.stats().pure_cse_enabled
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::addr_mode::AddrModeEarlyFormation;
    use trust_cg_ir::{
        AArch64Opcode, BlockId, CondCode, InstFlags, InstId, MachFunction, MachInst, MachOperand,
        PassId, ProofAnnotation, ProofDivergence, ProofFact, ProvenanceStatus, RegClass, Signature,
        SourceLoc, SpecialReg, TransformKind, VReg,
        regs::{SP, X0, X1, X2, X3, X4, X5, X6, XZR},
    };

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn vreg32(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }

    fn imm(val: i64) -> MachOperand {
        MachOperand::Imm(val)
    }

    // ---- Sentinel S4: kernel-gated guard elimination ----

    /// A bounds-check carrier (InstId 0 in the resulting function) + ldr + ret.
    fn bounds_carrier_func() -> MachFunction {
        let guard = MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![vreg(0), vreg(1), imm(8)],
        )
        .with_proof(ProofAnnotation::InBounds);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(3), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        make_func_with_insts(vec![guard, ldr, ret])
    }

    #[test]
    fn s4_gate_eliminates_when_obligation_discharged() {
        use std::collections::HashMap;
        use trust_cg_ir::{DischargeStatus, DischargedEvidenceTable};

        let mut func = bounds_carrier_func();
        let mut evidence = DischargedEvidenceTable::new();
        evidence.insert(100, DischargeStatus::Discharged, None);
        let mut obligations = HashMap::new();
        obligations.insert(InstId(0), (100u128, None)); // carrier is InstId 0

        let mut pass = ProofOptimization::new();
        pass.enable_kernel_gate(evidence, obligations);
        assert!(pass.run(&mut func));

        // Carrier eliminated under kernel authorization.
        assert_eq!(func.block(func.entry).insts.len(), 2); // ldr + ret
        assert_eq!(pass.stats().bounds_checks_eliminated, 1);
        assert_eq!(pass.kernel_eliminations().len(), 1);
        // Independent re-check passes.
        assert!(pass.recheck_kernel_eliminations().is_ok());
    }

    #[test]
    fn s4_gate_keeps_when_no_obligation_bound() {
        use std::collections::HashMap;
        use trust_cg_ir::{DischargeStatus, DischargedEvidenceTable};

        let mut func = bounds_carrier_func();
        let mut evidence = DischargedEvidenceTable::new();
        evidence.insert(100, DischargeStatus::Discharged, None);
        // No obligation bound to the carrier => kernel keeps it.
        let obligations: HashMap<InstId, (u128, Option<u128>)> = HashMap::new();

        let mut pass = ProofOptimization::new();
        pass.enable_kernel_gate(evidence, obligations);
        pass.run(&mut func);

        // Guard NOT eliminated (still present): block keeps guard + ldr + ret.
        assert_eq!(func.block(func.entry).insts.len(), 3);
        assert_eq!(pass.stats().bounds_checks_eliminated, 0);
        assert_eq!(pass.kernel_eliminations().len(), 0);
        assert!(pass.recheck_kernel_eliminations().is_ok()); // nothing eliminated => trivially ok
    }

    #[test]
    fn s4_gate_keeps_when_obligation_absent_from_evidence() {
        use std::collections::HashMap;
        use trust_cg_ir::DischargedEvidenceTable;

        let mut func = bounds_carrier_func();
        // Obligation bound to carrier, but evidence table is empty (not discharged).
        let mut obligations = HashMap::new();
        obligations.insert(InstId(0), (100u128, None));

        let mut pass = ProofOptimization::new();
        pass.enable_kernel_gate(DischargedEvidenceTable::new(), obligations);
        pass.run(&mut func);

        assert_eq!(func.block(func.entry).insts.len(), 3); // kept
        assert_eq!(pass.kernel_eliminations().len(), 0);
    }

    #[test]
    fn production_policy_keeps_aarch64_guard_with_forged_annotation_and_binding() {
        use std::collections::HashMap;

        // The carrier label and the carrier→obligation binding are both attacker-constructible.
        // Production's replay evidence is empty, so neither can remove the runtime guard.
        let mut func = bounds_carrier_func();
        let mut forged_bindings = HashMap::new();
        forged_bindings.insert(InstId(0), (0x0BAD_5EED_u128, Some(0xF0_12_34u128)));

        let mut pass = ProofOptimization::new();
        pass.enable_kernel_gate(
            trust_cg_lower::guard_evidence::production_guard_replay_evidence(),
            forged_bindings,
        );
        assert!(!pass.run(&mut func));
        assert_eq!(func.block(func.entry).insts.len(), 3);
        assert_eq!(pass.stats().bounds_checks_eliminated, 0);
        assert!(pass.kernel_eliminations().is_empty());
    }

    #[test]
    fn kernel_policy_blocks_legacy_nooverflow_label_bypass() {
        use std::collections::HashMap;
        use trust_cg_ir::{DischargeStatus, DischargedEvidenceTable};

        let checked = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);
        let trap = MachInst::new(AArch64Opcode::TrapOverflow, vec![]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![checked, trap, ret]);

        // Even a forged evidence row and binding cannot authorize the legacy trap: it has no exact
        // self-contained carrier identity for the kernel to replay against.
        let mut evidence = DischargedEvidenceTable::new();
        evidence.insert(7, DischargeStatus::Discharged, None);
        let mut bindings = HashMap::new();
        bindings.insert(InstId(1), (7, None));
        let mut pass = ProofOptimization::new();
        pass.enable_kernel_gate(evidence, bindings);
        assert!(!pass.run(&mut func));
        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::AddsRR);
        assert!(func.block(func.entry).insts.contains(&InstId(1)));
        assert_eq!(pass.stats().overflow_checks_eliminated, 0);
    }

    #[test]
    fn s4_gate_off_preserves_legacy_elimination() {
        // With the gate OFF (default), the legacy syntactic path eliminates as before.
        let mut func = bounds_carrier_func();
        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));
        assert_eq!(func.block(func.entry).insts.len(), 2);
        assert_eq!(pass.stats().bounds_checks_eliminated, 1);
        // Gate off => no kernel eliminations recorded.
        assert_eq!(pass.kernel_eliminations().len(), 0);
    }

    fn preg(reg: trust_cg_ir::PReg) -> MachOperand {
        MachOperand::PReg(reg)
    }

    fn source_loc(line: u32) -> SourceLoc {
        SourceLoc {
            file: 376,
            line,
            col: 9,
        }
    }

    fn make_func_with_insts(insts: Vec<MachInst>) -> MachFunction {
        let mut func = MachFunction::new(
            "test_proof_opts".to_string(),
            Signature::new(vec![], vec![]),
        );
        let block = func.entry;
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(block, id);
        }
        func
    }

    // --- NoOverflow tests ---

    #[test]
    fn test_no_overflow_adds_to_add() {
        // Pattern: adds v0, v1, v2 [NoOverflow] + trap_overflow
        // Expected: add v0, v1, v2 (trap removed)
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);

        let trap = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(BlockId(1))],
        );

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, trap, ret]);

        // Create the panic block so the function is well-formed.
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        // The ADDS should be converted to ADD.
        let inst = func.inst(InstId(0));
        assert_eq!(inst.opcode, AArch64Opcode::AddRR);
        assert!(inst.proof.is_none());

        // The TrapOverflow should be removed from the block.
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // add + ret

        // Verify stats.
        assert_eq!(pass.stats().overflow_checks_eliminated, 1);
    }

    #[test]
    fn test_source_loc_preserved_across_no_overflow_rewrite() {
        let loc = source_loc(21);
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_source_loc(loc)
            .with_proof(ProofAnnotation::NoOverflow);

        let trap = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(BlockId(1))],
        );

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, trap, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let inst = func.inst(InstId(0));
        assert_eq!(inst.opcode, AArch64Opcode::AddRR);
        assert_eq!(
            inst.source_loc,
            Some(loc),
            "proof-opts must preserve source_loc when rewriting checked arithmetic"
        );
    }

    #[test]
    fn test_no_overflow_subs_to_sub() {
        let subs = MachInst::new(AArch64Opcode::SubsRI, vec![vreg(0), vreg(1), imm(42)])
            .with_proof(ProofAnnotation::NoOverflow);

        let trap = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(BlockId(1))],
        );

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![subs, trap, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let inst = func.inst(InstId(0));
        assert_eq!(inst.opcode, AArch64Opcode::SubRI);
        assert_eq!(pass.stats().overflow_checks_eliminated, 1);
    }

    #[test]
    fn test_no_overflow_without_trap_preserves_flag_setter() {
        // ADDS with NoOverflow but no following TrapOverflow.
        // It must keep setting NZCV because a later flag reader may depend on it.
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, ret]);

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        let inst = func.inst(InstId(0));
        assert_eq!(inst.opcode, AArch64Opcode::AddsRR);
        assert_eq!(pass.stats().overflow_checks_eliminated, 0);
    }

    #[test]
    fn test_no_overflow_preserves_flag_setter_when_cset_consumes_overflow_flag() {
        // Checked-overflow value materialization can be `ADDS; CSET VS`.
        // Rewriting only the ADDS would make CSET read stale NZCV flags.
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);
        let cset_vs = MachInst::new(AArch64Opcode::CSet, vec![vreg(3), imm(6)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, cset_vs, ret]);

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::AddsRR);
        assert_eq!(func.inst(InstId(1)).opcode, AArch64Opcode::CSet);
        assert_eq!(pass.stats().overflow_checks_eliminated, 0);
    }

    #[test]
    fn test_no_overflow_preserves_subs_when_cset_consumes_overflow_flag() {
        let subs = MachInst::new(AArch64Opcode::SubsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);
        let cset_vs = MachInst::new(AArch64Opcode::CSet, vec![vreg(3), imm(6)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![subs, cset_vs, ret]);

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::SubsRR);
        assert_eq!(func.inst(InstId(1)).opcode, AArch64Opcode::CSet);
        assert_eq!(pass.stats().overflow_checks_eliminated, 0);
    }

    #[test]
    fn test_no_overflow_preserves_adds_when_bcond_consumes_overflow_flag() {
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);
        let b_vs = MachInst::new(
            AArch64Opcode::BCond,
            vec![imm(6), MachOperand::Block(BlockId(1))],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, b_vs, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::AddsRR);
        assert_eq!(func.inst(InstId(1)).opcode, AArch64Opcode::BCond);
        assert_eq!(pass.stats().overflow_checks_eliminated, 0);
    }

    #[test]
    fn test_no_overflow_deletes_bcond_vs_overflow_guard_only() {
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);
        let b_vs = MachInst::new(
            AArch64Opcode::BCond,
            vec![
                imm(i64::from(CondCode::VS.encoding())),
                MachOperand::Block(BlockId(1)),
            ],
        );
        let b_ok = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(2))]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, b_vs, b_ok, ret]);
        func.create_block();
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::AddRR);
        let block = func.block(func.entry);
        assert_eq!(block.insts, vec![InstId(0), InstId(2), InstId(3)]);
        assert_eq!(func.inst(InstId(2)).opcode, AArch64Opcode::B);
        assert_eq!(pass.stats().overflow_checks_eliminated, 1);
    }

    #[test]
    fn test_no_signed_overflow_consumes_trap_overflow() {
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoSignedOverflow);

        let trap = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(BlockId(1))],
        );

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, trap, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::AddRR);
        assert_eq!(func.block(func.entry).insts, vec![InstId(0), InstId(2)]);
        assert_eq!(pass.stats().overflow_checks_eliminated, 1);
    }

    #[test]
    fn test_no_signed_overflow_consumes_bcond_vs_guard() {
        let subs = MachInst::new(AArch64Opcode::SubsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoSignedOverflow);
        let b_vs = MachInst::new(
            AArch64Opcode::BCond,
            vec![
                imm(i64::from(CondCode::VS.encoding())),
                MachOperand::Block(BlockId(1)),
            ],
        );
        let b_ok = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(2))]);
        let mut func = make_func_with_insts(vec![subs, b_vs, b_ok]);
        func.create_block();
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::SubRR);
        assert_eq!(func.block(func.entry).insts, vec![InstId(0), InstId(2)]);
        assert_eq!(
            pass.certificates()[0].transform.name,
            "proof-opts.no-signed-overflow.checked-to-unchecked"
        );
    }

    #[test]
    fn test_no_overflow_preserves_unsigned_bcond_carry_borrow_guards() {
        for (opcode, cond) in [
            (AArch64Opcode::AddsRR, CondCode::HS),
            (AArch64Opcode::SubsRR, CondCode::LO),
        ] {
            let checked = MachInst::new(opcode, vec![vreg(0), vreg(1), vreg(2)])
                .with_proof(ProofAnnotation::NoOverflow);
            let b_overflow = MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    imm(i64::from(cond.encoding())),
                    MachOperand::Block(BlockId(1)),
                ],
            );
            let b_ok = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(2))]);
            let mut func = make_func_with_insts(vec![checked, b_overflow, b_ok]);
            func.create_block();
            func.create_block();

            let mut pass = ProofOptimization::new();
            assert!(!pass.run(&mut func));

            assert_eq!(func.inst(InstId(0)).opcode, opcode);
            assert_eq!(
                func.block(func.entry).insts,
                vec![InstId(0), InstId(1), InstId(2)]
            );
            assert_eq!(pass.stats().overflow_checks_eliminated, 0);
        }
    }

    #[test]
    fn test_no_signed_overflow_preserves_unsigned_bcond_carry_borrow_guards() {
        for (opcode, cond) in [
            (AArch64Opcode::AddsRR, CondCode::HS),
            (AArch64Opcode::SubsRR, CondCode::LO),
        ] {
            let checked = MachInst::new(opcode, vec![vreg(0), vreg(1), vreg(2)])
                .with_proof(ProofAnnotation::NoSignedOverflow);
            let b_overflow = MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    imm(i64::from(cond.encoding())),
                    MachOperand::Block(BlockId(1)),
                ],
            );
            let b_ok = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(2))]);
            let mut func = make_func_with_insts(vec![checked, b_overflow, b_ok]);
            func.create_block();
            func.create_block();

            let mut pass = ProofOptimization::new();
            assert!(!pass.run(&mut func));

            assert_eq!(func.inst(InstId(0)).opcode, opcode);
            assert_eq!(
                func.block(func.entry).insts,
                vec![InstId(0), InstId(1), InstId(2)]
            );
            assert_eq!(pass.stats().overflow_checks_eliminated, 0);
        }
    }

    #[test]
    fn test_no_unsigned_overflow_consumes_carry_borrow_guards() {
        for (opcode, unchecked_opcode, cond) in [
            (AArch64Opcode::AddsRR, AArch64Opcode::AddRR, CondCode::HS),
            (AArch64Opcode::SubsRR, AArch64Opcode::SubRR, CondCode::LO),
        ] {
            let checked = MachInst::new(opcode, vec![vreg(0), vreg(1), vreg(2)])
                .with_proof(ProofAnnotation::NoUnsignedOverflow);
            let b_overflow = MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    imm(i64::from(cond.encoding())),
                    MachOperand::Block(BlockId(1)),
                ],
            );
            let b_ok = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(2))]);
            let mut func = make_func_with_insts(vec![checked, b_overflow, b_ok]);
            func.create_block();
            func.create_block();

            let mut pass = ProofOptimization::new();
            assert!(pass.run(&mut func));

            assert_eq!(func.inst(InstId(0)).opcode, unchecked_opcode);
            assert_eq!(func.block(func.entry).insts, vec![InstId(0), InstId(2)]);
            assert_eq!(pass.stats().overflow_checks_eliminated, 1);
            assert_eq!(
                pass.certificates()[0].transform.name,
                "proof-opts.no-unsigned-overflow.checked-to-unchecked"
            );
        }
    }

    #[test]
    fn test_no_unsigned_overflow_does_not_consume_trap_overflow() {
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoUnsignedOverflow);

        let trap = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(BlockId(1))],
        );

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, trap, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::AddsRR);
        assert_eq!(
            func.block(func.entry).insts,
            vec![InstId(0), InstId(1), InstId(2)]
        );
        assert_eq!(pass.stats().overflow_checks_eliminated, 0);
        let rejection = pass.certificates()[0]
            .rejection
            .as_ref()
            .expect("rejection metadata");
        assert_eq!(rejection.fact, "NoUnsignedOverflow");
    }

    #[test]
    fn test_no_unsigned_overflow_rejects_wrong_carry_borrow_conditions() {
        for (opcode, cond) in [
            (AArch64Opcode::AddsRR, CondCode::LO),
            (AArch64Opcode::SubsRR, CondCode::HS),
            (AArch64Opcode::AddsRR, CondCode::VS),
            (AArch64Opcode::SubsRR, CondCode::VS),
        ] {
            let checked = MachInst::new(opcode, vec![vreg(0), vreg(1), vreg(2)])
                .with_proof(ProofAnnotation::NoUnsignedOverflow);
            let b_overflow = MachInst::new(
                AArch64Opcode::BCond,
                vec![
                    imm(i64::from(cond.encoding())),
                    MachOperand::Block(BlockId(1)),
                ],
            );
            let b_ok = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(2))]);
            let mut func = make_func_with_insts(vec![checked, b_overflow, b_ok]);
            func.create_block();
            func.create_block();

            let mut pass = ProofOptimization::new();
            assert!(!pass.run(&mut func));

            assert_eq!(func.inst(InstId(0)).opcode, opcode);
            assert_eq!(
                func.block(func.entry).insts,
                vec![InstId(0), InstId(1), InstId(2)]
            );
            assert_eq!(pass.stats().overflow_checks_eliminated, 0);
        }
    }

    #[test]
    fn test_no_overflow_preserves_bcond_when_condition_is_not_opcode_overflow() {
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);
        let b_lo = MachInst::new(
            AArch64Opcode::BCond,
            vec![
                imm(i64::from(CondCode::LO.encoding())),
                MachOperand::Block(BlockId(1)),
            ],
        );
        let b_ok = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(2))]);
        let mut func = make_func_with_insts(vec![adds, b_lo, b_ok]);
        func.create_block();
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::AddsRR);
        assert_eq!(
            func.block(func.entry).insts,
            vec![InstId(0), InstId(1), InstId(2)]
        );
        assert_eq!(pass.stats().overflow_checks_eliminated, 0);
    }

    // --- InBounds tests ---

    #[test]
    fn test_in_bounds_eliminates_check() {
        let guard = MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![vreg(0), vreg(1), imm(8)],
        )
        .with_proof(ProofAnnotation::InBounds);

        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(3), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![guard, ldr, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // ldr + ret

        assert_eq!(pass.stats().bounds_checks_eliminated, 1);
    }

    #[test]
    fn test_in_bounds_legacy_cmp_trap_no_change() {
        let cmp = MachInst::new(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)])
            .with_proof(ProofAnnotation::InBounds);
        let trap = MachInst::new(
            AArch64Opcode::TrapBoundsCheck,
            vec![MachOperand::Block(BlockId(1))],
        );

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cmp, trap, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));
        assert_eq!(func.block(func.entry).insts.len(), 3);
    }

    // --- NotNull tests ---

    #[test]
    fn test_not_null_trap_null_if_zero_eliminated() {
        let guard = MachInst::new(AArch64Opcode::TrapNullIfZero, vec![vreg(0)])
            .with_proof(ProofAnnotation::NotNull);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(0), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![guard, ldr, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::LdrRI);
        assert_eq!(pass.stats().null_checks_eliminated, 1);
    }

    #[test]
    fn test_not_null_trap_null_if_zero_preserves_source_loc_on_delete_certificate() {
        let loc = source_loc(47);
        let guard = MachInst::new(AArch64Opcode::TrapNullIfZero, vec![vreg(0)])
            .with_source_loc(loc)
            .with_proof(ProofAnnotation::NotNull);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![guard, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        assert_eq!(func.block(func.entry).insts.len(), 1);
        assert_eq!(pass.stats().null_checks_eliminated, 1);
    }

    #[test]
    fn test_not_null_bare_trap_null_not_consumed() {
        let trap =
            MachInst::new(AArch64Opcode::TrapNull, vec![]).with_proof(ProofAnnotation::NotNull);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![trap, ret]);

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::TrapNull);
        assert_eq!(pass.stats().null_checks_eliminated, 0);
    }

    #[test]
    fn test_not_null_cmp_zero_trap_null_not_consumed() {
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(0), imm(0)])
            .with_proof(ProofAnnotation::NotNull);
        let trap = MachInst::new(AArch64Opcode::TrapNull, vec![]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cmp, trap, ret]);

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::CmpRI);
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::TrapNull);
        assert_eq!(pass.stats().null_checks_eliminated, 0);
    }

    // --- ValidBorrow tests ---

    #[test]
    fn test_valid_borrow_refines_load() {
        // A load with ValidBorrow proof.
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(1), imm(0)])
            .with_proof(ProofAnnotation::ValidBorrow);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        assert_eq!(pass.stats().alias_refinements, 1);
    }

    #[test]
    fn test_valid_borrow_refines_store() {
        let str_inst = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(1), imm(8)])
            .with_proof(ProofAnnotation::ValidBorrow);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![str_inst, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        assert_eq!(pass.stats().alias_refinements, 1);
    }

    #[test]
    fn test_valid_borrow_non_memory_no_effect() {
        // ValidBorrow on a non-memory instruction should not count.
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::ValidBorrow);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ret]);

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        assert_eq!(pass.stats().alias_refinements, 0);
    }

    // --- PositiveRefCount tests ---

    #[test]
    fn test_positive_refcount_eliminates_retain_release_pair() {
        // Pattern: retain ptr [PositiveRefCount] + release ptr
        // Expected: both removed
        let retain = MachInst::new(AArch64Opcode::Retain, vec![vreg(0)])
            .with_proof(ProofAnnotation::PositiveRefCount);

        let release = MachInst::new(AArch64Opcode::Release, vec![vreg(0)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![retain, release, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1); // only ret

        assert_eq!(pass.stats().refcount_pairs_eliminated, 1);
    }

    #[test]
    fn test_positive_refcount_no_match_different_ptr() {
        // retain v0 [PositiveRefCount] + release v1 — different ptrs, no elim.
        let retain = MachInst::new(AArch64Opcode::Retain, vec![vreg(0)])
            .with_proof(ProofAnnotation::PositiveRefCount);

        let release = MachInst::new(AArch64Opcode::Release, vec![vreg(1)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![retain, release, ret]);

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3); // all preserved
    }

    #[test]
    fn test_positive_refcount_call_blocks_elimination() {
        // retain v0 [PositiveRefCount] + bl foo + release v0
        // The call prevents elimination.
        let retain = MachInst::new(AArch64Opcode::Retain, vec![vreg(0)])
            .with_proof(ProofAnnotation::PositiveRefCount);

        let call = MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Imm(0)]);

        let release = MachInst::new(AArch64Opcode::Release, vec![vreg(0)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![retain, call, release, ret]);

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4); // all preserved
    }

    #[test]
    fn test_positive_refcount_with_intervening_instructions() {
        // retain v0 [PositiveRefCount] + add v1, v2, v3 + release v0
        // Non-memory instruction between retain/release is fine.
        let retain = MachInst::new(AArch64Opcode::Retain, vec![vreg(0)])
            .with_proof(ProofAnnotation::PositiveRefCount);

        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(1), vreg(2), vreg(3)]);

        let release = MachInst::new(AArch64Opcode::Release, vec![vreg(0)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![retain, add, release, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // add + ret

        assert_eq!(pass.stats().refcount_pairs_eliminated, 1);
    }

    // --- Idempotency tests ---

    #[test]
    fn test_pass_is_idempotent() {
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);

        let trap = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(BlockId(1))],
        );

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, trap, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));
        // Second run should find nothing to do.
        assert!(!pass.run(&mut func));
    }

    // --- No annotation, no optimization ---

    #[test]
    fn test_no_annotation_no_change() {
        // ADDS without proof annotation should not be optimized.
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)]);

        let trap = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(BlockId(1))],
        );

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, trap, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        // Everything should be preserved.
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3);
        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::AddsRR);
    }

    // --- Multi-block tests ---

    #[test]
    fn test_proof_opts_across_multiple_blocks() {
        let mut func = MachFunction::new(
            "test_multi_block".to_string(),
            Signature::new(vec![], vec![]),
        );

        // Block 0: overflow check
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);
        let trap_ov = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(BlockId(2))],
        );
        let branch = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(1))]);

        let adds_id = func.push_inst(adds);
        let trap_ov_id = func.push_inst(trap_ov);
        let branch_id = func.push_inst(branch);
        func.append_inst(BlockId(0), adds_id);
        func.append_inst(BlockId(0), trap_ov_id);
        func.append_inst(BlockId(0), branch_id);

        // Block 1: null check
        let bb1 = func.create_block();
        let null_guard = MachInst::new(AArch64Opcode::TrapNullIfZero, vec![vreg(3)])
            .with_proof(ProofAnnotation::NotNull);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);

        let guard_id = func.push_inst(null_guard);
        let ret_id = func.push_inst(ret);
        func.append_inst(bb1, guard_id);
        func.append_inst(bb1, ret_id);

        // Block 2: panic (unused in this test)
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        // Block 0: adds→add, trap removed, branch kept
        let block0 = func.block(BlockId(0));
        assert_eq!(block0.insts.len(), 2); // add + b
        assert_eq!(func.inst(adds_id).opcode, AArch64Opcode::AddRR);

        // Block 1: not-null guard removed, ret kept
        let block1 = func.block(bb1);
        assert_eq!(block1.insts.len(), 1); // ret

        assert_eq!(pass.stats().overflow_checks_eliminated, 1);
        assert_eq!(pass.stats().null_checks_eliminated, 1);
    }

    // --- NonZeroDivisor tests ---

    #[test]
    fn test_non_zero_divisor_cbz_not_consumed() {
        // Legacy CBZ guards are not the exact trust_ir GuardDivZero carrier.
        let cbz = MachInst::new(
            AArch64Opcode::Cbz,
            vec![vreg(1), MachOperand::Block(BlockId(1))],
        )
        .with_proof(ProofAnnotation::NonZeroDivisor);

        let udiv = MachInst::new(AArch64Opcode::UDiv, vec![vreg(2), vreg(0), vreg(1)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cbz, udiv, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3);
        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::Cbz);
        assert_eq!(func.inst(InstId(1)).opcode, AArch64Opcode::UDiv);
        assert_eq!(pass.stats().divzero_checks_eliminated, 0);
    }

    #[test]
    fn test_non_zero_divisor_bare_trap_divzero_not_consumed() {
        // A bare TrapDivZero does not carry the checked divisor identity.
        let trap = MachInst::new(
            AArch64Opcode::TrapDivZero,
            vec![MachOperand::Block(BlockId(1))],
        )
        .with_proof(ProofAnnotation::NonZeroDivisor);

        let sdiv = MachInst::new(AArch64Opcode::SDiv, vec![vreg(2), vreg(0), vreg(1)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![trap, sdiv, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3);
        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::TrapDivZero);
        assert_eq!(pass.stats().divzero_checks_eliminated, 0);
    }

    #[test]
    fn test_non_zero_divisor_cmp_zero_bcond_eq_not_eliminated() {
        // BCond is not the exact proof-only TrapDivZero carrier.
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(0)])
            .with_proof(ProofAnnotation::NonZeroDivisor);

        let bcond = MachInst::new(
            AArch64Opcode::BCond,
            vec![
                imm(i64::from(CondCode::EQ.encoding())),
                MachOperand::Block(BlockId(1)),
            ],
        );

        let udiv = MachInst::new(AArch64Opcode::UDiv, vec![vreg(2), vreg(0), vreg(1)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cmp, bcond, udiv, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::CmpRI);
        assert_eq!(func.inst(InstId(1)).opcode, AArch64Opcode::BCond);
        assert_eq!(pass.stats().divzero_checks_eliminated, 0);
    }

    #[test]
    fn test_non_zero_divisor_cmp_zero_bcond_ne_not_eliminated() {
        // NE is the inverted branch: under NonZeroDivisor it would be always
        // taken, not a dead divide-by-zero trap edge.
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(0)])
            .with_proof(ProofAnnotation::NonZeroDivisor);

        let bcond = MachInst::new(
            AArch64Opcode::BCond,
            vec![
                imm(i64::from(CondCode::NE.encoding())),
                MachOperand::Block(BlockId(1)),
            ],
        );

        let udiv = MachInst::new(AArch64Opcode::UDiv, vec![vreg(2), vreg(0), vreg(1)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cmp, bcond, udiv, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::CmpRI);
        assert_eq!(func.inst(InstId(1)).opcode, AArch64Opcode::BCond);
        assert_eq!(pass.stats().divzero_checks_eliminated, 0);
    }

    #[test]
    fn test_non_zero_divisor_cmp_zero_trap_divzero_eliminated() {
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(0)])
            .with_proof(ProofAnnotation::NonZeroDivisor);
        let trap = MachInst::new(
            AArch64Opcode::TrapDivZero,
            vec![MachOperand::Block(BlockId(1))],
        );
        let udiv = MachInst::new(AArch64Opcode::UDiv, vec![vreg(2), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cmp, trap, udiv, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        assert_eq!(pass.stats().divzero_checks_eliminated, 1);
    }

    /// The production carrier: the self-contained `TrapDivZeroIfZero divisor` (the DivZero mirror of
    /// `test_not_null_trap_null_if_zero_eliminated`) is eliminated by the legacy syntactic path.
    #[test]
    fn test_non_zero_divisor_trap_div_zero_if_zero_eliminated() {
        let guard = MachInst::new(AArch64Opcode::TrapDivZeroIfZero, vec![vreg(1)])
            .with_proof(ProofAnnotation::NonZeroDivisor);
        let udiv = MachInst::new(AArch64Opcode::UDiv, vec![vreg(2), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![guard, udiv, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::UDiv);
        assert_eq!(pass.stats().divzero_checks_eliminated, 1);
    }

    /// The bare div panic trap (`TrapDivZero`, panic-target shape) is NOT a self-contained carrier
    /// and must NOT be consumed by the single-carrier path — only `TrapDivZeroIfZero` is.
    #[test]
    fn test_non_zero_divisor_trap_div_zero_if_zero_distinct_from_bare_trap() {
        let trap = MachInst::new(
            AArch64Opcode::TrapDivZero,
            vec![MachOperand::Block(BlockId(1))],
        )
        .with_proof(ProofAnnotation::NonZeroDivisor);
        let udiv = MachInst::new(AArch64Opcode::UDiv, vec![vreg(2), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![trap, udiv, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));
        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::TrapDivZero);
        assert_eq!(pass.stats().divzero_checks_eliminated, 0);
    }

    /// Kernel-gated (S4): with the gate ON, a `TrapDivZeroIfZero` is eliminated ONLY when the kernel
    /// authorizes it (a discharged obligation bound to the carrier by its [divisor] fingerprint), and
    /// the elimination independently re-checks. An unbound carrier is KEPT (fail-safe). The DivZero
    /// mirror of the gated NotNull behavior.
    #[test]
    fn test_non_zero_divisor_kernel_gate_eliminates_only_when_discharged() {
        use std::collections::HashMap;
        use trust_cg_ir::guard::{GuardOperandRef, fingerprint_operands};
        use trust_cg_ir::{DischargeStatus, DischargedEvidenceTable};

        let obligation_id: u128 = 0x1_0000_0000; // a synthesized-range id
        let fp = fingerprint_operands(&[GuardOperandRef::Reg(1)]);

        // --- Discharged: gate authorizes, carrier removed, re-check passes. ---
        {
            let guard = MachInst::new(AArch64Opcode::TrapDivZeroIfZero, vec![vreg(1)])
                .with_proof(ProofAnnotation::NonZeroDivisor);
            let udiv = MachInst::new(AArch64Opcode::UDiv, vec![vreg(2), vreg(0), vreg(1)]);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let mut func = make_func_with_insts(vec![guard, udiv, ret]);

            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(obligation_id, DischargeStatus::Discharged, None);
            let mut obligations = HashMap::new();
            obligations.insert(InstId(0), (obligation_id, None));

            let mut pass = ProofOptimization::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(pass.run(&mut func));
            assert_eq!(pass.stats().divzero_checks_eliminated, 1);
            pass.recheck_kernel_eliminations()
                .expect("discharged div-zero elimination must independently re-check");
            // Carrier fingerprint binding is exactly what ISel records.
            let _ = fp;
        }

        // --- Undischarged (no evidence): gate KEEPS the carrier (fail-safe). ---
        {
            let guard = MachInst::new(AArch64Opcode::TrapDivZeroIfZero, vec![vreg(1)])
                .with_proof(ProofAnnotation::NonZeroDivisor);
            let udiv = MachInst::new(AArch64Opcode::UDiv, vec![vreg(2), vreg(0), vreg(1)]);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let mut func = make_func_with_insts(vec![guard, udiv, ret]);

            let evidence = DischargedEvidenceTable::new();
            let mut obligations = HashMap::new();
            obligations.insert(InstId(0), (obligation_id, None));

            let mut pass = ProofOptimization::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(!pass.run(&mut func));
            assert_eq!(pass.stats().divzero_checks_eliminated, 0);
            assert_eq!(
                func.inst(func.block(func.entry).insts[0]).opcode,
                AArch64Opcode::TrapDivZeroIfZero,
                "an undischarged div-zero carrier must be KEPT under the kernel gate"
            );
        }
    }

    /// #5 (Certified-tier lineage): a Certified obligation whose receipt lineage MATCHES the
    /// evidence is eliminated and re-checks; a MISMATCHED lineage, or a Certified evidence entry
    /// with an absent (None) receipt lineage, is KEPT (fail-safe — stronger evidence must never
    /// disable optimization, but a missing/wrong lineage must never authorize one).
    #[test]
    fn test_certified_lineage_eliminates_only_on_match() {
        use std::collections::HashMap;
        use trust_cg_ir::{DischargeStatus, DischargedEvidenceTable};

        let obligation_id: u128 = 0x2_0000_0000;
        let lineage: u128 = 0xABCD_1234_DEAD_BEEF;

        let build = || {
            let guard = MachInst::new(AArch64Opcode::TrapDivZeroIfZero, vec![vreg(1)])
                .with_proof(ProofAnnotation::NonZeroDivisor);
            let udiv = MachInst::new(AArch64Opcode::UDiv, vec![vreg(2), vreg(0), vreg(1)]);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            make_func_with_insts(vec![guard, udiv, ret])
        };

        // --- Certified + matching lineage on the receipt: ELIMINATED, re-checks. ---
        {
            let mut func = build();
            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(obligation_id, DischargeStatus::Certified, Some(lineage));
            let mut obligations = HashMap::new();
            obligations.insert(InstId(0), (obligation_id, Some(lineage)));

            let mut pass = ProofOptimization::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(pass.run(&mut func));
            assert_eq!(pass.stats().divzero_checks_eliminated, 1);
            assert_eq!(pass.kernel_eliminations().len(), 1);
            pass.recheck_kernel_eliminations()
                .expect("certified+matching-lineage elimination must independently re-check");
            pass.recheck_kernel_eliminations_live(&func)
                .expect("certified+matching-lineage elimination must re-check against live func");
        }

        // --- Certified evidence, but MISMATCHED lineage on the receipt: KEPT. ---
        {
            let mut func = build();
            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(obligation_id, DischargeStatus::Certified, Some(lineage));
            let mut obligations = HashMap::new();
            obligations.insert(InstId(0), (obligation_id, Some(lineage ^ 0x1))); // wrong lineage

            let mut pass = ProofOptimization::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(!pass.run(&mut func));
            assert_eq!(pass.stats().divzero_checks_eliminated, 0);
            assert_eq!(pass.kernel_eliminations().len(), 0);
            assert_eq!(
                func.inst(func.block(func.entry).insts[0]).opcode,
                AArch64Opcode::TrapDivZeroIfZero,
                "a certified carrier with a mismatched lineage must be KEPT under the gate"
            );
        }

        // --- Certified evidence, but receipt lineage ABSENT (None): KEPT. ---
        {
            let mut func = build();
            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(obligation_id, DischargeStatus::Certified, Some(lineage));
            let mut obligations = HashMap::new();
            obligations.insert(InstId(0), (obligation_id, None)); // no lineage on receipt

            let mut pass = ProofOptimization::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(!pass.run(&mut func));
            assert_eq!(pass.stats().divzero_checks_eliminated, 0);
            assert_eq!(pass.kernel_eliminations().len(), 0);
            assert_eq!(
                func.inst(func.block(func.entry).insts[0]).opcode,
                AArch64Opcode::TrapDivZeroIfZero,
                "a certified carrier with an absent receipt lineage must be KEPT under the gate"
            );
        }
    }

    /// #6 (legacy gate gaps — strict subset): under the kernel gate, the legacy paired
    /// CmpRI+TrapDivZero shape (which carries no kernel-recognized carrier identity) is KEPT, while
    /// with the gate OFF it eliminates exactly as before. The gate must be a strict subset.
    #[test]
    fn test_legacy_paired_divzero_kept_under_gate_eliminated_off() {
        use std::collections::HashMap;
        use trust_cg_ir::{DischargeStatus, DischargedEvidenceTable};

        let build = || {
            let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(0)])
                .with_proof(ProofAnnotation::NonZeroDivisor);
            let trap = MachInst::new(
                AArch64Opcode::TrapDivZero,
                vec![MachOperand::Block(BlockId(1))],
            );
            let sdiv = MachInst::new(AArch64Opcode::SDiv, vec![vreg(2), vreg(0), vreg(1)]);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let mut func = make_func_with_insts(vec![cmp, trap, sdiv, ret]);
            func.create_block();
            func
        };

        // --- Gate OFF (default): legacy paired shape ELIMINATED, exactly as before. ---
        {
            let mut func = build();
            let mut pass = ProofOptimization::new();
            assert!(pass.run(&mut func));
            assert_eq!(pass.stats().divzero_checks_eliminated, 1);
            assert_eq!(func.block(func.entry).insts.len(), 2); // sdiv + ret
        }

        // --- Gate ON: legacy paired shape KEPT (no kernel-recognized carrier identity). ---
        {
            let mut func = build();
            // Even with a fully-discharged obligation in the table, the bare TrapDivZero is not a
            // kernel carrier (classify_carrier => None), so kernel_authorizes always KEEPs it.
            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(0x9_9999, DischargeStatus::Discharged, None);
            let obligations: HashMap<InstId, (u128, Option<u128>)> = HashMap::new();

            let mut pass = ProofOptimization::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(!pass.run(&mut func));
            assert_eq!(pass.stats().divzero_checks_eliminated, 0);
            assert_eq!(
                func.block(func.entry).insts.len(),
                4,
                "the legacy paired div-zero shape must be KEPT under the kernel gate"
            );
        }
    }

    /// #6 (legacy gate gaps — strict subset): under the kernel gate, the legacy paired
    /// CmpRI+TrapShiftRange shape AND the bare TrapShiftRange shape are KEPT; with the gate OFF they
    /// eliminate exactly as before.
    #[test]
    fn test_legacy_shiftrange_shapes_kept_under_gate_eliminated_off() {
        use std::collections::HashMap;
        use trust_cg_ir::DischargedEvidenceTable;

        // --- Paired CmpRI + TrapShiftRange ---
        let build_paired = || {
            let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(64)])
                .with_proof(ProofAnnotation::ValidShift);
            let trap = MachInst::new(
                AArch64Opcode::TrapShiftRange,
                vec![MachOperand::Block(BlockId(1))],
            );
            let lsl = MachInst::new(AArch64Opcode::LslRR, vec![vreg(2), vreg(0), vreg(1)]);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let mut func = make_func_with_insts(vec![cmp, trap, lsl, ret]);
            func.create_block();
            func
        };

        // Gate OFF: eliminated.
        {
            let mut func = build_paired();
            let mut pass = ProofOptimization::new();
            assert!(pass.run(&mut func));
            assert_eq!(pass.stats().shift_checks_eliminated, 1);
            assert_eq!(func.block(func.entry).insts.len(), 2); // lsl + ret
        }
        // Gate ON: KEPT.
        {
            let mut func = build_paired();
            let evidence = DischargedEvidenceTable::new();
            let obligations: HashMap<InstId, (u128, Option<u128>)> = HashMap::new();
            let mut pass = ProofOptimization::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(!pass.run(&mut func));
            assert_eq!(pass.stats().shift_checks_eliminated, 0);
            assert_eq!(
                func.block(func.entry).insts.len(),
                4,
                "the legacy paired shift-range shape must be KEPT under the kernel gate"
            );
        }

        // --- Bare TrapShiftRange (no operand identity) ---
        let build_bare = || {
            let trap = MachInst::new(
                AArch64Opcode::TrapShiftRange,
                vec![MachOperand::Block(BlockId(1))],
            )
            .with_proof(ProofAnnotation::ValidShift);
            let lsl = MachInst::new(AArch64Opcode::LslRR, vec![vreg(2), vreg(0), vreg(1)]);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let mut func = make_func_with_insts(vec![trap, lsl, ret]);
            func.create_block();
            func
        };

        // Gate OFF: eliminated.
        {
            let mut func = build_bare();
            let mut pass = ProofOptimization::new();
            assert!(pass.run(&mut func));
            assert_eq!(pass.stats().shift_checks_eliminated, 1);
            assert_eq!(func.block(func.entry).insts.len(), 2); // lsl + ret
        }
        // Gate ON: KEPT (no operand identity => never eliminate unconsulted).
        {
            let mut func = build_bare();
            let evidence = DischargedEvidenceTable::new();
            let obligations: HashMap<InstId, (u128, Option<u128>)> = HashMap::new();
            let mut pass = ProofOptimization::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(!pass.run(&mut func));
            assert_eq!(pass.stats().shift_checks_eliminated, 0);
            assert_eq!(
                func.block(func.entry).insts.len(),
                3,
                "the bare shift-range shape must be KEPT under the kernel gate"
            );
        }
    }

    /// #9 (non-vacuous operand-drift re-check): after a kernel-authorized elimination, MUTATE the
    /// live carrier's divisor operand and re-check against the live func — the re-derived
    /// fingerprint no longer matches the certificate, so the elimination is REJECTED (fail-closed).
    /// A non-mutated control re-checks Ok. This exercises the CALLER re-reading the LIVE carrier,
    /// which was previously vacuous.
    #[test]
    fn test_recheck_rejects_live_operand_drift() {
        use std::collections::HashMap;
        use trust_cg_ir::{DischargeStatus, DischargedEvidenceTable};

        let obligation_id: u128 = 0x3_0000_0000;

        let build = || {
            let guard = MachInst::new(AArch64Opcode::TrapDivZeroIfZero, vec![vreg(1)])
                .with_proof(ProofAnnotation::NonZeroDivisor);
            let udiv = MachInst::new(AArch64Opcode::UDiv, vec![vreg(2), vreg(0), vreg(1)]);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            make_func_with_insts(vec![guard, udiv, ret])
        };

        // --- Control: no drift => live re-check passes. ---
        {
            let mut func = build();
            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(obligation_id, DischargeStatus::Discharged, None);
            let mut obligations = HashMap::new();
            obligations.insert(InstId(0), (obligation_id, None));

            let mut pass = ProofOptimization::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(pass.run(&mut func));
            assert_eq!(pass.kernel_eliminations().len(), 1);
            assert!(
                pass.recheck_kernel_eliminations_live(&func).is_ok(),
                "a non-drifted elimination must re-check Ok against the live func"
            );
        }

        // --- Drift: mutate the carrier's divisor operand AFTER authorization, then live re-check
        //     must REJECT (the re-derived fingerprint diverges from the certificate). ---
        {
            let mut func = build();
            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(obligation_id, DischargeStatus::Discharged, None);
            let mut obligations = HashMap::new();
            obligations.insert(InstId(0), (obligation_id, None));

            let mut pass = ProofOptimization::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(pass.run(&mut func));
            assert_eq!(pass.kernel_eliminations().len(), 1);
            // The certificate was minted for divisor VReg(1); drift the live carrier to VReg(7).
            func.inst_mut(InstId(0)).operands = vec![vreg(7)];
            assert!(
                pass.recheck_kernel_eliminations_live(&func).is_err(),
                "a live operand drift must be REJECTED by the re-check (fail-closed)"
            );
        }
    }

    #[test]
    fn test_non_zero_divisor_no_proof_no_change() {
        // CBZ without proof annotation should not be optimized.
        let cbz = MachInst::new(
            AArch64Opcode::Cbz,
            vec![vreg(1), MachOperand::Block(BlockId(1))],
        );

        let udiv = MachInst::new(AArch64Opcode::UDiv, vec![vreg(2), vreg(0), vreg(1)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cbz, udiv, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 3); // all preserved
    }

    #[test]
    fn test_non_zero_divisor_sdiv_exact_guard_pattern() {
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(0)])
            .with_proof(ProofAnnotation::NonZeroDivisor);
        let trap = MachInst::new(
            AArch64Opcode::TrapDivZero,
            vec![MachOperand::Block(BlockId(1))],
        );
        let sdiv = MachInst::new(AArch64Opcode::SDiv, vec![vreg(2), vreg(0), vreg(1)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cmp, trap, sdiv, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // sdiv + ret

        assert_eq!(pass.stats().divzero_checks_eliminated, 1);
    }

    // --- ValidShift tests ---

    #[test]
    fn test_valid_shift_eliminates_cmp_trap() {
        // Pattern: cmp shift_amt, #64 [ValidShift] + trap_shift_range panic_block
        // Expected: both removed, LSL preserved
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(64)])
            .with_proof(ProofAnnotation::ValidShift);

        let trap = MachInst::new(
            AArch64Opcode::TrapShiftRange,
            vec![MachOperand::Block(BlockId(1))],
        );

        let lsl = MachInst::new(AArch64Opcode::LslRR, vec![vreg(2), vreg(0), vreg(1)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cmp, trap, lsl, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        // CMP and TrapShiftRange removed, LSL and RET remain.
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // lsl + ret

        assert_eq!(pass.stats().shift_checks_eliminated, 1);
    }

    #[test]
    fn test_valid_shift_eliminates_cmp_bcond() {
        // Pattern: cmp shift_amt, #64 [ValidShift] + bcond HS, trap_block
        // Expected: both removed
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(64)])
            .with_proof(ProofAnnotation::ValidShift);

        let bcond = MachInst::new(
            AArch64Opcode::BCond,
            vec![
                imm(i64::from(CondCode::HS.encoding())),
                MachOperand::Block(BlockId(1)),
            ],
        );

        let lsr = MachInst::new(AArch64Opcode::LsrRR, vec![vreg(2), vreg(0), vreg(1)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cmp, bcond, lsr, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // lsr + ret

        assert_eq!(pass.stats().shift_checks_eliminated, 1);
    }

    #[test]
    fn test_valid_shift_cmp_bcond_lo_not_eliminated() {
        // LO is the inverted branch for `cmp amount, #64`: under ValidShift it
        // would be always taken, not a dead out-of-range trap edge.
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(64)])
            .with_proof(ProofAnnotation::ValidShift);

        let bcond = MachInst::new(
            AArch64Opcode::BCond,
            vec![
                imm(i64::from(CondCode::LO.encoding())),
                MachOperand::Block(BlockId(1)),
            ],
        );

        let lsr = MachInst::new(AArch64Opcode::LsrRR, vec![vreg(2), vreg(0), vreg(1)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cmp, bcond, lsr, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::CmpRI);
        assert_eq!(func.inst(InstId(1)).opcode, AArch64Opcode::BCond);
        assert_eq!(pass.stats().shift_checks_eliminated, 0);
    }

    #[test]
    fn test_valid_shift_cmp_bcond_ge_not_eliminated() {
        // Signed GE is not the unsigned shift range guard for `cmp amount,
        // #bitwidth`; the canonical trap edge is HS.
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(64)])
            .with_proof(ProofAnnotation::ValidShift);

        let bcond = MachInst::new(
            AArch64Opcode::BCond,
            vec![
                imm(i64::from(CondCode::GE.encoding())),
                MachOperand::Block(BlockId(1)),
            ],
        );

        let lsr = MachInst::new(AArch64Opcode::LsrRR, vec![vreg(2), vreg(0), vreg(1)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cmp, bcond, lsr, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4);
        assert_eq!(pass.stats().shift_checks_eliminated, 0);
    }

    #[test]
    fn test_valid_shift_32bit() {
        // Pattern: cmp shift_amt, #32 [ValidShift] + trap_shift_range
        // Expected: both removed (32-bit shift width)
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(32)])
            .with_proof(ProofAnnotation::ValidShift);

        let trap = MachInst::new(
            AArch64Opcode::TrapShiftRange,
            vec![MachOperand::Block(BlockId(1))],
        );

        let asr = MachInst::new(AArch64Opcode::AsrRR, vec![vreg(2), vreg(0), vreg(1)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cmp, trap, asr, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // asr + ret

        assert_eq!(pass.stats().shift_checks_eliminated, 1);
    }

    #[test]
    fn test_valid_shift_trap_only() {
        // Pattern: trap_shift_range panic_block [ValidShift]
        // Expected: removed
        let trap = MachInst::new(
            AArch64Opcode::TrapShiftRange,
            vec![MachOperand::Block(BlockId(1))],
        )
        .with_proof(ProofAnnotation::ValidShift);

        let lsl = MachInst::new(AArch64Opcode::LslRR, vec![vreg(2), vreg(0), vreg(1)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![trap, lsl, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2); // lsl + ret

        assert_eq!(pass.stats().shift_checks_eliminated, 1);
    }

    /// The production carrier: the self-contained `TrapShiftRangeIfOOB amount, bitwidth` (the
    /// ShiftRange mirror of the bounds carrier) is eliminated by the legacy syntactic path, preserving
    /// the shift instruction.
    #[test]
    fn test_valid_shift_trap_shift_range_if_oob_eliminated() {
        let guard = MachInst::new(AArch64Opcode::TrapShiftRangeIfOOB, vec![vreg(1), imm(64)])
            .with_proof(ProofAnnotation::ValidShift);
        let lsl = MachInst::new(AArch64Opcode::LslRR, vec![vreg(2), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![guard, lsl, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::LslRR);
        assert_eq!(pass.stats().shift_checks_eliminated, 1);
    }

    /// Kernel-gated (S4): with the gate ON, a `TrapShiftRangeIfOOB` is eliminated ONLY when the kernel
    /// authorizes it (a discharged obligation bound to the carrier by its [amount, Imm(bitwidth)]
    /// fingerprint), and the elimination independently re-checks. An unbound carrier is KEPT
    /// (fail-safe). The ShiftRange mirror of the gated InBounds behavior.
    #[test]
    fn test_valid_shift_kernel_gate_eliminates_only_when_discharged() {
        use std::collections::HashMap;
        use trust_cg_ir::guard::{GuardOperandRef, fingerprint_operands};
        use trust_cg_ir::{DischargeStatus, DischargedEvidenceTable};

        let obligation_id: u128 = 0x1_0000_0000;
        let _fp = fingerprint_operands(&[GuardOperandRef::Reg(1), GuardOperandRef::Imm(64)]);

        // --- Discharged: gate authorizes, carrier removed, re-check passes. ---
        {
            let guard = MachInst::new(AArch64Opcode::TrapShiftRangeIfOOB, vec![vreg(1), imm(64)])
                .with_proof(ProofAnnotation::ValidShift);
            let lsl = MachInst::new(AArch64Opcode::LslRR, vec![vreg(2), vreg(0), vreg(1)]);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let mut func = make_func_with_insts(vec![guard, lsl, ret]);

            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(obligation_id, DischargeStatus::Discharged, None);
            let mut obligations = HashMap::new();
            obligations.insert(InstId(0), (obligation_id, None));

            let mut pass = ProofOptimization::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(pass.run(&mut func));
            assert_eq!(pass.stats().shift_checks_eliminated, 1);
            pass.recheck_kernel_eliminations()
                .expect("discharged shift-range elimination must independently re-check");
        }

        // --- Undischarged (no evidence): gate KEEPS the carrier (fail-safe). ---
        {
            let guard = MachInst::new(AArch64Opcode::TrapShiftRangeIfOOB, vec![vreg(1), imm(64)])
                .with_proof(ProofAnnotation::ValidShift);
            let lsl = MachInst::new(AArch64Opcode::LslRR, vec![vreg(2), vreg(0), vreg(1)]);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let mut func = make_func_with_insts(vec![guard, lsl, ret]);

            let evidence = DischargedEvidenceTable::new();
            let mut obligations = HashMap::new();
            obligations.insert(InstId(0), (obligation_id, None));

            let mut pass = ProofOptimization::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(!pass.run(&mut func));
            assert_eq!(pass.stats().shift_checks_eliminated, 0);
            assert_eq!(
                func.inst(func.block(func.entry).insts[0]).opcode,
                AArch64Opcode::TrapShiftRangeIfOOB,
                "an undischarged shift-range carrier must be KEPT under the kernel gate"
            );
        }
    }

    /// The production overflow carrier: a self-contained `TrapOverflowExact lhs, rhs, Imm(op_tag)`
    /// is eliminated by the legacy syntactic path, leaving the SEPARATE plain ADD value op intact.
    #[test]
    fn test_no_overflow_trap_overflow_exact_eliminated_legacy() {
        use trust_cg_ir::{OverflowOp, pack_overflow_tag};
        let tag = pack_overflow_tag(OverflowOp::SignedAdd, 64);
        // Decoupled: plain ADD produces the value; the carrier holds ONLY the overflow check.
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let guard = MachInst::new(
            AArch64Opcode::TrapOverflowExact,
            vec![vreg(0), vreg(1), imm(tag)],
        )
        .with_proof(ProofAnnotation::NoSignedOverflow);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, guard, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2, "carrier removed; ADD + RET remain");
        assert_eq!(
            func.inst(block.insts[0]).opcode,
            AArch64Opcode::AddRR,
            "the value op (plain ADD) must be preserved verbatim"
        );
        assert_eq!(pass.stats().overflow_checks_eliminated, 1);
    }

    /// Kernel-gated (S4): with the gate ON, a `TrapOverflowExact` is eliminated ONLY when the kernel
    /// authorizes it (a discharged obligation bound by its `[lhs, rhs, Imm(op_tag)]` fingerprint), and
    /// the elimination independently re-checks. An unbound carrier is KEPT (fail-safe), and in BOTH
    /// cases the plain ADD value op is preserved. The OVERFLOW mirror of the gated ShiftRange test.
    #[test]
    fn test_no_overflow_kernel_gate_eliminates_only_when_discharged() {
        use std::collections::HashMap;
        use trust_cg_ir::guard::{GuardOperandRef, fingerprint_operands};
        use trust_cg_ir::{
            DischargeStatus, DischargedEvidenceTable, OverflowOp, pack_overflow_tag,
        };

        let tag = pack_overflow_tag(OverflowOp::SignedAdd, 64);
        let obligation_id: u128 = 0x2_0000_0000;
        // The kernel keys the obligation by the FULL fingerprint incl. the op-tag.
        let _fp = fingerprint_operands(&[
            GuardOperandRef::Reg(0),
            GuardOperandRef::Reg(1),
            GuardOperandRef::Imm(tag),
        ]);

        // --- Discharged: gate authorizes, carrier removed, ADD preserved, re-check passes. ---
        {
            let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
            let guard = MachInst::new(
                AArch64Opcode::TrapOverflowExact,
                vec![vreg(0), vreg(1), imm(tag)],
            )
            .with_proof(ProofAnnotation::NoSignedOverflow);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let mut func = make_func_with_insts(vec![add, guard, ret]);

            let mut evidence = DischargedEvidenceTable::new();
            evidence.insert(obligation_id, DischargeStatus::Discharged, None);
            let mut obligations = HashMap::new();
            // The carrier is InstId(1) (add is 0).
            obligations.insert(InstId(1), (obligation_id, None));

            let mut pass = ProofOptimization::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(pass.run(&mut func));
            assert_eq!(pass.stats().overflow_checks_eliminated, 1);
            let block = func.block(func.entry);
            assert_eq!(
                func.inst(block.insts[0]).opcode,
                AArch64Opcode::AddRR,
                "the plain ADD value op must survive carrier elimination"
            );
            pass.recheck_kernel_eliminations()
                .expect("discharged overflow elimination must independently re-check");
        }

        // --- Undischarged (no evidence): gate KEEPS the carrier (fail-safe). ---
        {
            let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
            let guard = MachInst::new(
                AArch64Opcode::TrapOverflowExact,
                vec![vreg(0), vreg(1), imm(tag)],
            )
            .with_proof(ProofAnnotation::NoSignedOverflow);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let mut func = make_func_with_insts(vec![add, guard, ret]);

            let evidence = DischargedEvidenceTable::new();
            let mut obligations = HashMap::new();
            obligations.insert(InstId(1), (obligation_id, None));

            let mut pass = ProofOptimization::new();
            pass.enable_kernel_gate(evidence, obligations);
            assert!(!pass.run(&mut func));
            assert_eq!(pass.stats().overflow_checks_eliminated, 0);
            assert_eq!(
                func.inst(func.block(func.entry).insts[1]).opcode,
                AArch64Opcode::TrapOverflowExact,
                "an undischarged overflow carrier must be KEPT under the kernel gate"
            );
        }
    }

    /// SOUNDNESS: a wrong-op proof cannot discharge an overflow carrier. The carrier is for a
    /// SIGNED add (op-tag signed), but the discharged obligation is bound to the UNSIGNED-add
    /// fingerprint. Because the op-tag participates in the fingerprint, the obligation maps to a
    /// DIFFERENT carrier InstId key, so the signed carrier has no bound obligation and is KEPT.
    #[test]
    fn test_overflow_carrier_wrong_op_proof_does_not_discharge() {
        use std::collections::HashMap;
        use trust_cg_ir::{
            DischargeStatus, DischargedEvidenceTable, OverflowOp, pack_overflow_tag,
        };

        let signed_tag = pack_overflow_tag(OverflowOp::SignedAdd, 64);
        let obligation_id: u128 = 0x3_0000_0000;

        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let guard = MachInst::new(
            AArch64Opcode::TrapOverflowExact,
            vec![vreg(0), vreg(1), imm(signed_tag)],
        )
        .with_proof(ProofAnnotation::NoSignedOverflow);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, guard, ret]);

        let mut evidence = DischargedEvidenceTable::new();
        evidence.insert(obligation_id, DischargeStatus::Discharged, None);
        // Deliberately bind the obligation to a DIFFERENT InstId (simulating the production pipeline,
        // where the obligation map is keyed by fingerprint — a wrong-op proof would never key the
        // signed carrier's InstId). Here we bind nothing to InstId(1), so the carrier is unbound.
        let obligations: HashMap<InstId, (u128, Option<u128>)> = HashMap::new();

        let mut pass = ProofOptimization::new();
        pass.enable_kernel_gate(evidence, obligations);
        assert!(!pass.run(&mut func));
        assert_eq!(pass.stats().overflow_checks_eliminated, 0);
        assert_eq!(
            func.inst(func.block(func.entry).insts[1]).opcode,
            AArch64Opcode::TrapOverflowExact,
            "a carrier with no bound (correctly-keyed) obligation must be KEPT"
        );
    }

    #[test]
    fn test_valid_shift_no_proof_no_change() {
        // CMP with #64 but no ValidShift proof should not be optimized.
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(64)]);

        let trap = MachInst::new(
            AArch64Opcode::TrapShiftRange,
            vec![MachOperand::Block(BlockId(1))],
        );

        let lsl = MachInst::new(AArch64Opcode::LslRR, vec![vreg(2), vreg(0), vreg(1)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cmp, trap, lsl, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 4); // all preserved
    }

    #[test]
    fn test_valid_shift_cmp_without_trap_no_change() {
        // CMP with ValidShift but no TrapShiftRange or BCond following.
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(64)])
            .with_proof(ProofAnnotation::ValidShift);

        let lsl = MachInst::new(AArch64Opcode::LslRR, vec![vreg(2), vreg(0), vreg(1)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cmp, lsl, ret]);

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));
    }

    // --- Combined new + existing proof opts ---

    #[test]
    fn test_combined_divzero_and_shift_opts() {
        // Two blocks: one with NonZeroDivisor, one with ValidShift.
        let mut func = MachFunction::new(
            "test_combined_new_opts".to_string(),
            Signature::new(vec![], vec![]),
        );

        // Block 0: exact div-zero check
        let cmp_div = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(0)])
            .with_proof(ProofAnnotation::NonZeroDivisor);
        let trap_div = MachInst::new(
            AArch64Opcode::TrapDivZero,
            vec![MachOperand::Block(BlockId(2))],
        );
        let udiv = MachInst::new(AArch64Opcode::UDiv, vec![vreg(2), vreg(0), vreg(1)]);
        let branch = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(1))]);

        let cmp_div_id = func.push_inst(cmp_div);
        let trap_div_id = func.push_inst(trap_div);
        let udiv_id = func.push_inst(udiv);
        let branch_id = func.push_inst(branch);
        func.append_inst(BlockId(0), cmp_div_id);
        func.append_inst(BlockId(0), trap_div_id);
        func.append_inst(BlockId(0), udiv_id);
        func.append_inst(BlockId(0), branch_id);

        // Block 1: shift range check
        let bb1 = func.create_block();
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(3), imm(64)])
            .with_proof(ProofAnnotation::ValidShift);
        let trap_shift = MachInst::new(
            AArch64Opcode::TrapShiftRange,
            vec![MachOperand::Block(BlockId(2))],
        );
        let lsl = MachInst::new(AArch64Opcode::LslRR, vec![vreg(4), vreg(0), vreg(3)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);

        let cmp_id = func.push_inst(cmp);
        let trap_shift_id = func.push_inst(trap_shift);
        let lsl_id = func.push_inst(lsl);
        let ret_id = func.push_inst(ret);
        func.append_inst(bb1, cmp_id);
        func.append_inst(bb1, trap_shift_id);
        func.append_inst(bb1, lsl_id);
        func.append_inst(bb1, ret_id);

        // Block 2: panic (unused)
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        // Block 0: cmp + trap removed -> udiv + b
        let block0 = func.block(BlockId(0));
        assert_eq!(block0.insts.len(), 2);

        // Block 1: cmp + trap removed → lsl + ret
        let block1 = func.block(bb1);
        assert_eq!(block1.insts.len(), 2);

        assert_eq!(pass.stats().divzero_checks_eliminated, 1);
        assert_eq!(pass.stats().shift_checks_eliminated, 1);
    }

    // --- Pure (aggressive CSE) tests ---

    #[test]
    fn test_pure_promotes_load_to_cse_able() {
        // A load with Pure proof should have its READS_MEMORY flag removed,
        // making it eligible for CSE by downstream passes.
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(1), imm(0)])
            .with_proof(ProofAnnotation::Pure);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        // The load should no longer have READS_MEMORY flag.
        let inst = func.inst(InstId(0));
        assert!(!inst.flags.contains(InstFlags::READS_MEMORY));
        // The proof should be consumed.
        assert!(inst.proof.is_none());
        assert_eq!(pass.stats().pure_cse_enabled, 1);
    }

    #[test]
    fn test_source_loc_preserved_across_pure_flag_refinement() {
        let loc = source_loc(88);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(1), imm(0)])
            .with_source_loc(loc)
            .with_proof(ProofAnnotation::Pure);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let inst = func.inst(InstId(0));
        assert!(!inst.flags.contains(InstFlags::READS_MEMORY));
        assert_eq!(
            inst.source_loc,
            Some(loc),
            "proof-opts must preserve source_loc when refining proof-driven flags"
        );
    }

    #[test]
    fn test_pure_promotes_store_to_cse_able() {
        // A store with Pure proof should have its WRITES_MEMORY + HAS_SIDE_EFFECTS removed.
        let str_inst = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(1), imm(8)])
            .with_proof(ProofAnnotation::Pure);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![str_inst, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let inst = func.inst(InstId(0));
        assert!(!inst.flags.contains(InstFlags::WRITES_MEMORY));
        assert!(!inst.flags.contains(InstFlags::HAS_SIDE_EFFECTS));
        assert!(inst.proof.is_none());
        assert_eq!(pass.stats().pure_cse_enabled, 1);
    }

    #[test]
    fn test_pure_on_already_pure_instruction_no_effect() {
        // An ADD instruction is already pure — Pure proof has no effect.
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::Pure);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ret]);

        let mut pass = ProofOptimization::new();
        // Should return false because the ADD is already pure.
        assert!(!pass.run(&mut func));

        assert_eq!(pass.stats().pure_cse_enabled, 0);
    }

    #[test]
    fn test_pure_multiple_loads() {
        // Two loads with Pure proof: both should be promoted.
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(1), imm(0)])
            .with_proof(ProofAnnotation::Pure);

        let ldr2 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(1), imm(8)])
            .with_proof(ProofAnnotation::Pure);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr1, ldr2, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        assert_eq!(pass.stats().pure_cse_enabled, 2);

        // Both loads should have READS_MEMORY removed.
        assert!(!func.inst(InstId(0)).flags.contains(InstFlags::READS_MEMORY));
        assert!(!func.inst(InstId(1)).flags.contains(InstFlags::READS_MEMORY));
    }

    #[test]
    fn test_pure_without_proof_load_unchanged() {
        // A load without Pure proof should keep its READS_MEMORY flag.
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(1), imm(0)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr, ret]);

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        assert!(func.inst(InstId(0)).flags.contains(InstFlags::READS_MEMORY));
        assert_eq!(pass.stats().pure_cse_enabled, 0);
    }

    // --- ValidBorrow reordering flag tests ---

    #[test]
    fn test_valid_borrow_sets_reorderable_flag_on_load() {
        // A load with ValidBorrow should get the PROOF_REORDERABLE flag.
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(1), imm(0)])
            .with_proof(ProofAnnotation::ValidBorrow);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let inst = func.inst(InstId(0));
        assert!(inst.flags.contains(InstFlags::PROOF_REORDERABLE));
        assert_eq!(pass.stats().alias_refinements, 1);
    }

    #[test]
    fn test_valid_borrow_sets_reorderable_flag_on_store() {
        // A store with ValidBorrow should get the PROOF_REORDERABLE flag.
        let str_inst = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(1), imm(8)])
            .with_proof(ProofAnnotation::ValidBorrow);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![str_inst, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let inst = func.inst(InstId(0));
        assert!(inst.flags.contains(InstFlags::PROOF_REORDERABLE));
        // Store should keep its existing memory flags since it still writes.
        assert!(inst.flags.contains(InstFlags::WRITES_MEMORY));
    }

    #[test]
    fn test_valid_borrow_load_store_pair_both_reorderable() {
        // Both a load and store with ValidBorrow get PROOF_REORDERABLE.
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(1), imm(0)])
            .with_proof(ProofAnnotation::ValidBorrow);

        let str_inst = MachInst::new(AArch64Opcode::StrRI, vec![vreg(2), vreg(1), imm(8)])
            .with_proof(ProofAnnotation::ValidBorrow);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr, str_inst, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        assert!(
            func.inst(InstId(0))
                .flags
                .contains(InstFlags::PROOF_REORDERABLE)
        );
        assert!(
            func.inst(InstId(1))
                .flags
                .contains(InstFlags::PROOF_REORDERABLE)
        );
        assert_eq!(pass.stats().alias_refinements, 2);
    }

    // --- Public API function tests ---

    #[test]
    fn test_eliminate_overflow_checks_public_api() {
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);

        let trap = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(BlockId(1))],
        );

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, trap, ret]);
        func.create_block();

        let count = eliminate_overflow_checks(&mut func);
        assert_eq!(count, 1);

        // ADDS should now be ADD.
        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::AddRR);
    }

    #[test]
    fn test_eliminate_bounds_checks_public_api() {
        let guard = MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![vreg(0), vreg(1), imm(8)],
        )
        .with_proof(ProofAnnotation::InBounds);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![guard, ret]);

        let count = eliminate_bounds_checks(&mut func);
        assert_eq!(count, 1);

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1); // only ret
    }

    #[test]
    fn test_eliminate_null_checks_public_api() {
        let guard = MachInst::new(AArch64Opcode::TrapNullIfZero, vec![vreg(0)])
            .with_proof(ProofAnnotation::NotNull);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![guard, ret]);

        let count = eliminate_null_checks(&mut func);
        assert_eq!(count, 1);

        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 1); // only ret
    }

    #[test]
    fn test_enable_load_store_reorder_public_api() {
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(1), imm(0)])
            .with_proof(ProofAnnotation::ValidBorrow);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr, ret]);

        let count = enable_load_store_reorder(&mut func);
        assert_eq!(count, 1);

        assert!(
            func.inst(InstId(0))
                .flags
                .contains(InstFlags::PROOF_REORDERABLE)
        );
    }

    #[test]
    fn test_aggressive_cse_public_api() {
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(1), imm(0)])
            .with_proof(ProofAnnotation::Pure);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr, ret]);

        let count = aggressive_cse(&mut func);
        assert_eq!(count, 1);

        assert!(!func.inst(InstId(0)).flags.contains(InstFlags::READS_MEMORY));
    }

    // --- Combined new + existing: all proof types in one function ---

    #[test]
    fn test_all_proof_types_in_one_function() {
        let mut func = MachFunction::new(
            "test_all_proofs".to_string(),
            Signature::new(vec![], vec![]),
        );

        // Block 0: NoOverflow (adds -> add) + ValidBorrow (load reorderable)
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);
        let trap_ov = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(BlockId(2))],
        );
        let ldr_reorder = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(0), imm(0)])
            .with_proof(ProofAnnotation::ValidBorrow);
        let ldr_pure = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(4), vreg(0), imm(8)])
            .with_proof(ProofAnnotation::Pure);
        let branch = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(1))]);

        let adds_id = func.push_inst(adds);
        let trap_ov_id = func.push_inst(trap_ov);
        let ldr_reorder_id = func.push_inst(ldr_reorder);
        let ldr_pure_id = func.push_inst(ldr_pure);
        let branch_id = func.push_inst(branch);
        func.append_inst(BlockId(0), adds_id);
        func.append_inst(BlockId(0), trap_ov_id);
        func.append_inst(BlockId(0), ldr_reorder_id);
        func.append_inst(BlockId(0), ldr_pure_id);
        func.append_inst(BlockId(0), branch_id);

        // Block 1: ret
        let bb1 = func.create_block();
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let ret_id = func.push_inst(ret);
        func.append_inst(bb1, ret_id);

        // Block 2: panic (unused)
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        // Block 0: adds→add (trap removed), ldr_reorder (reorderable flag), ldr_pure (pure), branch
        let block0 = func.block(BlockId(0));
        assert_eq!(block0.insts.len(), 4); // add + ldr_reorder + ldr_pure + b

        // Verify: adds → add
        assert_eq!(func.inst(adds_id).opcode, AArch64Opcode::AddRR);

        // Verify: ValidBorrow load has PROOF_REORDERABLE
        assert!(
            func.inst(ldr_reorder_id)
                .flags
                .contains(InstFlags::PROOF_REORDERABLE)
        );

        // Verify: Pure load has READS_MEMORY removed
        assert!(
            !func
                .inst(ldr_pure_id)
                .flags
                .contains(InstFlags::READS_MEMORY)
        );

        // Verify stats
        assert_eq!(pass.stats().overflow_checks_eliminated, 1);
        assert_eq!(pass.stats().alias_refinements, 1);
        assert_eq!(pass.stats().pure_cse_enabled, 1);
    }

    // --- Certificate generation tests ---

    #[test]
    fn test_certificate_generated_on_overflow_elimination() {
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);

        let trap = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(BlockId(1))],
        );

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, trap, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let certs = pass.certificates();
        assert_eq!(certs.len(), 1);
        let cert = &certs[0];
        assert_eq!(cert.annotation, Some(ProofAnnotation::NoOverflow));
        assert_eq!(cert.primary_inst, InstId(0));
        assert_eq!(cert.affected_insts, vec![InstId(1)]);
        assert_eq!(cert.kind, OptCertificateKind::CheckedToUnchecked);

        // Verify take_certificates drains the buffer.
        let drained = pass.take_certificates();
        assert_eq!(drained.len(), 1);
        assert!(pass.certificates().is_empty());
    }

    #[test]
    fn test_successful_transform_certificate_carries_identity_and_hashes() {
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);
        let trap = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(BlockId(1))],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, trap, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        pass.set_source_region_hash(InstId(0), 0xA11CE);
        assert!(pass.run(&mut func));

        let cert = &pass.certificates()[0];
        assert_eq!(
            cert.transform,
            OptTransformIdentity {
                name: "proof-opts.no-overflow.checked-to-unchecked".to_string(),
                version: PROOF_OPT_TRANSFORM_VERSION,
            }
        );
        assert_eq!(
            cert.route,
            OptAdmissionRoute {
                pass: PROOF_OPT_PASS_NAME.to_string(),
                admission: "proof-annotation".to_string(),
            }
        );
        assert_eq!(
            cert.consumed_facts,
            vec![OptConsumedProofFact::LegacyAnnotation(
                ProofAnnotation::NoOverflow
            )]
        );
        assert_eq!(cert.source_region_hash, 0xA11CE);
        assert_ne!(cert.source_region_hash, cert.target_region_hash);
        assert_ne!(cert.proof_hash, 0);
        assert_ne!(cert.validation_hash, 0);
        assert_ne!(cert.certificate_id, 0);
        assert!(cert.rejection.is_none());
    }

    #[test]
    fn test_rejected_transform_certificate_preserves_reason() {
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, ret]);

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        let certs = pass.certificates();
        assert_eq!(certs.len(), 1);
        let cert = &certs[0];
        assert_eq!(cert.annotation, Some(ProofAnnotation::NoOverflow));
        assert_eq!(cert.kind, OptCertificateKind::CheckedToUnchecked);
        assert_eq!(cert.source_region_hash, cert.target_region_hash);
        let rejection = cert.rejection.as_ref().expect("rejection metadata");
        assert_eq!(rejection.code, ProofDiagnosticCode::RewriteRejected);
        assert_eq!(rejection.fact, "NoOverflow");
        assert_eq!(rejection.detail, "checked-overflow guard shape not matched");
    }

    #[test]
    fn test_unrepresentable_proof_certificate_preserves_reason() {
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::Associative);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ret]);

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        let cert = &pass.certificates()[0];
        assert_eq!(cert.annotation, Some(ProofAnnotation::Associative));
        let rejection = cert.rejection.as_ref().expect("rejection metadata");
        assert_eq!(rejection.code, ProofDiagnosticCode::PresentUnrepresentable);
        assert_eq!(rejection.fact, "Associative");
        assert_eq!(
            rejection.detail,
            "proof_opts has no direct transform for this algebraic proof"
        );
    }

    #[test]
    fn test_disabled_candidate_certificate_preserves_reason_and_skips_transform() {
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);
        let trap = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(BlockId(1))],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, trap, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        pass.disable_candidate(
            InstId(0),
            "NoOverflow",
            "proof opts disabled by product config",
        );
        assert!(!pass.run(&mut func));

        assert_eq!(func.inst(InstId(0)).opcode, AArch64Opcode::AddsRR);
        assert_eq!(func.block(func.entry).insts.len(), 3);
        let cert = &pass.certificates()[0];
        let rejection = cert.rejection.as_ref().expect("rejection metadata");
        assert_eq!(rejection.code, ProofDiagnosticCode::DisabledCandidate);
        assert_eq!(rejection.fact, "NoOverflow");
        assert_eq!(rejection.detail, "proof opts disabled by product config");
    }

    #[test]
    fn test_failed_product_gate_certificate_preserves_reason_and_skips_transform() {
        let guard = MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![vreg(0), vreg(1), imm(8)],
        )
        .with_proof(ProofAnnotation::InBounds);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![guard, ret]);

        let metadata = ProofOptimizationMetadata::new().with_failed_product_gate(
            InstId(0),
            "InBounds",
            "release gate requires replayable certificate chain",
        );
        let mut pass = ProofOptimization::new();
        pass.set_metadata(&metadata);
        assert!(!pass.run(&mut func));

        assert_eq!(func.block(func.entry).insts.len(), 2);
        let cert = &pass.certificates()[0];
        let rejection = cert.rejection.as_ref().expect("rejection metadata");
        assert_eq!(rejection.code, ProofDiagnosticCode::FailedProductGate);
        assert_eq!(rejection.fact, "InBounds");
        assert_eq!(
            rejection.detail,
            "release gate requires replayable certificate chain"
        );
    }

    #[test]
    fn test_certificate_preserves_multi_fact_payloads() {
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(1), imm(0)])
            .with_proof(ProofAnnotation::ValidBorrow);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr, ret]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(
            InstId(0),
            vec![
                ProofFact::NoAlias,
                ProofFact::Aligned(64),
                ProofFact::BoundedLoop(128),
                ProofFact::DivergenceClass(ProofDivergence::Low),
            ],
        );
        assert!(pass.run(&mut func));

        let cert = &pass.certificates()[0];
        assert_eq!(
            cert.route.admission, "proof-annotation+proof-facts",
            "sidecar facts should be visible in the admission route"
        );
        assert_eq!(
            cert.consumed_facts,
            vec![
                OptConsumedProofFact::LegacyAnnotation(ProofAnnotation::ValidBorrow),
                OptConsumedProofFact::ProofFact(ProofFact::NoAlias),
                OptConsumedProofFact::ProofFact(ProofFact::Aligned(64)),
                OptConsumedProofFact::ProofFact(ProofFact::BoundedLoop(128)),
                OptConsumedProofFact::ProofFact(ProofFact::DivergenceClass(ProofDivergence::Low)),
            ]
        );
        let payloads: Vec<_> = cert
            .consumed_facts
            .iter()
            .copied()
            .map(|fact| (fact.stable_name(), fact.payload()))
            .collect();
        assert_eq!(
            payloads,
            vec![
                ("ValidBorrow", None),
                ("NoAlias", None),
                ("Aligned", Some("64".to_string())),
                ("BoundedLoop", Some("128".to_string())),
                ("DivergenceClass", Some("Low".to_string())),
            ]
        );
    }

    #[test]
    fn test_aligned_pair_load_combines_to_ldp() {
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X0), preg(X2), imm(16)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X1), preg(X2), imm(24)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr0, ldr1, ret]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(32)]);

        assert!(pass.run(&mut func));
        assert_eq!(pass.stats().pair_mem_ops_combined, 1);
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        let pair = func.inst(block.insts[0]);
        assert_eq!(pair.opcode, AArch64Opcode::LdpRI);
        assert_eq!(pair.operands, vec![preg(X0), preg(X1), preg(X2), imm(16)]);
    }

    #[test]
    fn test_aligned_pair_combines_with_pair_start_fact_only() {
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X0), preg(X2), imm(0)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X1), preg(X2), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr0, ldr1, ret]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);

        assert!(pass.run(&mut func));
        assert_eq!(pass.stats().pair_mem_ops_combined, 1);
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        let pair = func.inst(block.insts[0]);
        assert_eq!(pair.opcode, AArch64Opcode::LdpRI);
        assert_eq!(pair.operands, vec![preg(X0), preg(X1), preg(X2), imm(0)]);
    }

    #[test]
    fn test_aligned_pair_source_loc_falls_back_to_second_mem_op() {
        let loc = source_loc(123);
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X0), preg(X2), imm(0)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X1), preg(X2), imm(8)])
            .with_source_loc(loc);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr0, ldr1, ret]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);

        assert!(pass.run(&mut func));
        let pair_id = func.block(func.entry).insts[0];
        let pair = func.inst(pair_id);
        assert_eq!(pair.opcode, AArch64Opcode::LdpRI);
        assert_eq!(
            pair.source_loc,
            Some(loc),
            "proof-opts pair combine must preserve source_loc from the second memory op when the first has none"
        );
    }

    #[test]
    fn test_aligned_pair_combines_with_stronger_pair_start_alignment_fact() {
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X0), preg(X2), imm(0)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X1), preg(X2), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr0, ldr1, ret]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(64)]);

        assert!(pass.run(&mut func));
        assert_eq!(pass.stats().pair_mem_ops_combined, 1);
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        let pair = func.inst(block.insts[0]);
        assert_eq!(pair.opcode, AArch64Opcode::LdpRI);
        assert_eq!(pair.operands, vec![preg(X0), preg(X1), preg(X2), imm(0)]);
        let cert = &pass.certificates()[0];
        assert_eq!(
            cert.consumed_facts,
            vec![OptConsumedProofFact::ProofFact(ProofFact::Aligned(64))]
        );
    }

    #[test]
    fn test_aligned_pair_combines_vreg_load_pair_to_ldp() {
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(2), imm(0)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(2), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr0, ldr1, ret]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

        assert!(pass.run(&mut func));
        assert_eq!(pass.stats().pair_mem_ops_combined, 1);
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        let pair = func.inst(block.insts[0]);
        assert_eq!(pair.opcode, AArch64Opcode::LdpRI);
        assert_eq!(pair.operands, vec![vreg(0), vreg(1), vreg(2), imm(0)]);
    }

    #[test]
    fn test_aligned_pair_store_combines_to_stp_with_memop_base() {
        let str0 = MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                preg(X3),
                MachOperand::MemOp {
                    base: X5,
                    offset: -16,
                },
            ],
        );
        let str1 = MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                preg(X4),
                MachOperand::MemOp {
                    base: X5,
                    offset: -8,
                },
            ],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![str0, str1, ret]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

        assert!(pass.run(&mut func));
        let block = func.block(func.entry);
        let pair = func.inst(block.insts[0]);
        assert_eq!(pair.opcode, AArch64Opcode::StpRI);
        assert_eq!(pair.operands, vec![preg(X3), preg(X4), preg(X5), imm(-16)]);
    }

    #[test]
    fn test_aligned_pair_combines_vreg_store_pair_to_stp() {
        let str0 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(2), imm(0)]);
        let str1 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(1), vreg(2), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![str0, str1, ret]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

        assert!(pass.run(&mut func));
        assert_eq!(pass.stats().pair_mem_ops_combined, 1);
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        let pair = func.inst(block.insts[0]);
        assert_eq!(pair.opcode, AArch64Opcode::StpRI);
        assert_eq!(pair.operands, vec![vreg(0), vreg(1), vreg(2), imm(0)]);
    }

    #[test]
    fn test_aligned_pair_certificate_is_fact_only_and_targets_pair() {
        fn pair_cert() -> (OptCertificate, u128, u128, InstId) {
            let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X0), preg(X2), imm(0)]);
            let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X1), preg(X2), imm(8)]);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let mut func = make_func_with_insts(vec![ldr0, ldr1, ret]);
            let source_hashes = [
                region_hash(&func, &[InstId(0)]),
                region_hash(&func, &[InstId(1)]),
            ];
            let source_hash = combined_source_region_identity_hash(&func.name, &source_hashes);

            let mut pass = ProofOptimization::new();
            pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
            pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(32)]);

            assert!(pass.run(&mut func));
            let pair_id = func.block(func.entry).insts[0];
            let target_hash = region_hash(&func, &[pair_id]);
            assert_eq!(pass.certificates().len(), 1);
            (
                pass.certificates()[0].clone(),
                source_hash,
                target_hash,
                pair_id,
            )
        }

        let (cert, source_hash, target_hash, pair_id) = pair_cert();
        assert_eq!(cert.annotation, None);
        assert_eq!(cert.kind, OptCertificateKind::PairCombined);
        assert_eq!(cert.transform.name, "proof-opts.aligned.pair-combined");
        assert_eq!(cert.route.admission, "proof-facts");
        assert_eq!(
            cert.consumed_facts,
            vec![OptConsumedProofFact::ProofFact(ProofFact::Aligned(16))]
        );
        assert_eq!(cert.primary_inst, pair_id);
        assert!(cert.affected_insts.is_empty());
        assert_eq!(cert.source_region_hash, source_hash);
        assert_eq!(cert.target_region_hash, target_hash);
        assert_ne!(cert.source_region_hash, cert.target_region_hash);
        assert_ne!(cert.certificate_id, 0);
        assert_ne!(cert.proof_hash, 0);
        assert_ne!(cert.validation_hash, 0);

        let (again, _, _, _) = pair_cert();
        assert_eq!(cert.certificate_id, again.certificate_id);
        assert_eq!(cert.source_region_hash, again.source_region_hash);
        assert_eq!(cert.target_region_hash, again.target_region_hash);
        assert_eq!(cert.proof_hash, again.proof_hash);
        assert_eq!(cert.validation_hash, again.validation_hash);
    }

    #[test]
    fn test_aligned_pair_skips_sources_with_prior_pure_certificate() {
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X0), preg(X2), imm(0)])
            .with_proof(ProofAnnotation::Pure);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X1), preg(X2), imm(8)]);
        let mut func = make_func_with_insts(vec![ldr0, ldr1]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

        assert!(pass.run(&mut func));
        assert_eq!(pass.stats().pure_cse_enabled, 1);
        assert_eq!(pass.stats().pair_mem_ops_combined, 0);
        assert_eq!(func.block(func.entry).insts, vec![InstId(0), InstId(1)]);
        assert_eq!(pass.certificates().len(), 1);
        assert_eq!(
            pass.certificates()[0].kind,
            OptCertificateKind::FlagsRefined
        );
        assert_eq!(
            pass.certificates()[0].annotation,
            Some(ProofAnnotation::Pure)
        );
    }

    #[test]
    fn test_aligned_pair_skips_when_second_source_has_prior_pure_certificate() {
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X0), preg(X2), imm(0)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X1), preg(X2), imm(8)])
            .with_proof(ProofAnnotation::Pure);
        let mut func = make_func_with_insts(vec![ldr0, ldr1]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

        assert!(pass.run(&mut func));
        assert_eq!(pass.stats().pure_cse_enabled, 1);
        assert_eq!(pass.stats().pair_mem_ops_combined, 0);
        assert_eq!(func.block(func.entry).insts, vec![InstId(0), InstId(1)]);
        assert_eq!(pass.certificates().len(), 1);
        assert_eq!(pass.certificates()[0].primary_inst, InstId(1));
        assert_eq!(
            pass.certificates()[0].kind,
            OptCertificateKind::FlagsRefined
        );
        assert_eq!(
            pass.certificates()[0].annotation,
            Some(ProofAnnotation::Pure)
        );
    }

    #[test]
    fn test_aligned_pair_certificate_source_hash_uses_sidecar_source_hashes() {
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X0), preg(X2), imm(0)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X1), preg(X2), imm(8)]);
        let mut func = make_func_with_insts(vec![ldr0, ldr1]);
        let raw_pair_hash = region_hash(&func, &[InstId(0), InstId(1)]);
        let first_source_hash = 0x1111_aaaa_2222_bbbb_3333_cccc_4444_ddddu128;
        let second_source_hash = 0x5555_eeee_6666_ffff_7777_8888_9999_0000u128;
        let expected_source_hash = combined_source_region_identity_hash(
            &func.name,
            &[first_source_hash, second_source_hash],
        );

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);
        pass.set_source_region_hash(InstId(0), first_source_hash);
        pass.set_source_region_hash(InstId(1), second_source_hash);

        assert!(pass.run(&mut func));
        let cert = &pass.certificates()[0];
        assert_eq!(cert.kind, OptCertificateKind::PairCombined);
        assert_eq!(cert.source_region_hash, expected_source_hash);
        assert_ne!(cert.source_region_hash, raw_pair_hash);
    }

    #[test]
    fn test_aligned_pair_certificate_source_hash_combines_sidecar_and_raw_machir() {
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X0), preg(X2), imm(0)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X1), preg(X2), imm(8)]);
        let mut func = make_func_with_insts(vec![ldr0, ldr1]);
        let raw_pair_hash = region_hash(&func, &[InstId(0), InstId(1)]);
        let first_source_hash = 0x1111_2222_3333_4444_5555_6666_7777_8888u128;
        let second_raw_hash = region_hash(&func, &[InstId(1)]);
        let expected_source_hash =
            combined_source_region_identity_hash(&func.name, &[first_source_hash, second_raw_hash]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);
        pass.set_source_region_hash(InstId(0), first_source_hash);

        assert!(pass.run(&mut func));
        let cert = &pass.certificates()[0];
        assert_eq!(cert.kind, OptCertificateKind::PairCombined);
        assert_eq!(cert.source_region_hash, expected_source_hash);
        assert_ne!(cert.source_region_hash, raw_pair_hash);
    }

    #[test]
    fn test_aligned_pair_certificate_source_hash_uses_provenance_hashes() {
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X0), preg(X2), imm(0)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X1), preg(X2), imm(8)]);
        let mut func = make_func_with_insts(vec![ldr0, ldr1]);
        let raw_pair_hash = region_hash(&func, &[InstId(0), InstId(1)]);
        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(41), &[InstId(0)], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(42), &[InstId(1)], PassId::new("isel"));

        let first_source_hash = source_trust_ir_region_hash(&func.name, &[TrustIrInstId(41)]);
        let second_source_hash = source_trust_ir_region_hash(&func.name, &[TrustIrInstId(42)]);
        let expected_source_hash = combined_source_region_identity_hash(
            &func.name,
            &[first_source_hash, second_source_hash],
        );

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);
        let mut analyses = AnalysisCache::new();

        assert!(MachinePass::run_with_analyses_and_provenance(
            &mut pass,
            &mut func,
            &mut analyses,
            &mut provenance,
        ));
        let cert = &pass.certificates()[0];
        assert_eq!(cert.kind, OptCertificateKind::PairCombined);
        assert_eq!(cert.source_region_hash, expected_source_hash);
        assert_ne!(cert.source_region_hash, raw_pair_hash);
    }

    #[test]
    fn test_provenance_records_no_overflow_rewrite_and_guard_deletion() {
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);
        let trap = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(BlockId(1))],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, trap, ret]);
        func.create_block();

        let adds_id = InstId(0);
        let trap_id = InstId(1);
        let ret_id = InstId(2);
        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(50), &[adds_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(51), &[trap_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(52), &[ret_id], PassId::new("isel"));

        let mut pass = ProofOptimization::new();
        let mut analyses = AnalysisCache::new();
        assert!(MachinePass::run_with_analyses_and_provenance(
            &mut pass,
            &mut func,
            &mut analyses,
            &mut provenance,
        ));

        assert_eq!(func.inst(adds_id).opcode, AArch64Opcode::AddRR);
        assert_eq!(func.block(func.entry).insts, vec![adds_id, ret_id]);

        let adds_entry = provenance
            .get_entry(adds_id)
            .expect("rewritten arithmetic provenance");
        assert_eq!(adds_entry.trust_ir_origins, vec![TrustIrInstId(50)]);
        assert!(adds_entry.is_active());
        let transform = adds_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("proof-opts"));
        assert_eq!(transform.kind, TransformKind::Survived);
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(50)),
            Some(&[adds_id][..])
        );

        let trap_entry = provenance
            .get_entry(trap_id)
            .expect("deleted overflow guard provenance");
        assert!(trap_entry.is_optimized_away());
        assert_eq!(trap_entry.trust_ir_origins, vec![TrustIrInstId(51)]);
        assert!(matches!(
            &trap_entry.status,
            ProvenanceStatus::OptimizedAway { pass, justification }
                if *pass == PassId::new("proof-opts")
                    && justification.contains("NoOverflow")
        ));
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(51)),
            Some(&[trap_id][..])
        );
    }

    #[test]
    fn test_run_with_provenance_records_pure_flag_refinement() {
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(1), imm(0)])
            .with_proof(ProofAnnotation::Pure);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr, ret]);

        let ldr_id = InstId(0);
        let ret_id = InstId(1);
        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(60), &[ldr_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(61), &[ret_id], PassId::new("isel"));

        let mut pass = ProofOptimization::new();
        assert!(MachinePass::run_with_provenance(
            &mut pass,
            &mut func,
            &mut provenance,
        ));

        assert!(!func.inst(ldr_id).flags.contains(InstFlags::READS_MEMORY));
        let entry = provenance
            .get_entry(ldr_id)
            .expect("pure refinement provenance");
        assert!(entry.is_active());
        assert_eq!(entry.trust_ir_origins, vec![TrustIrInstId(60)]);
        let transform = entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("proof-opts"));
        assert_eq!(transform.kind, TransformKind::Survived);
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(60)),
            Some(&[ldr_id][..])
        );
        assert_eq!(provenance.get_entry(ret_id).unwrap().transforms.len(), 1);
    }

    #[test]
    fn test_provenance_records_aligned_pair_combine_merge() {
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X0), preg(X2), imm(0)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X1), preg(X2), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr0, ldr1, ret]);

        let first_id = InstId(0);
        let second_id = InstId(1);
        let ret_id = InstId(2);
        let pair_id = InstId(3);
        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(70), &[first_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(71), &[second_id], PassId::new("isel"));
        provenance.record_lowering(TrustIrInstId(72), &[ret_id], PassId::new("isel"));

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(first_id, vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(second_id, vec![ProofFact::Aligned(16)]);
        let mut analyses = AnalysisCache::new();
        assert!(MachinePass::run_with_analyses_and_provenance(
            &mut pass,
            &mut func,
            &mut analyses,
            &mut provenance,
        ));

        assert_eq!(func.block(func.entry).insts, vec![pair_id, ret_id]);
        assert_eq!(func.inst(pair_id).opcode, AArch64Opcode::LdpRI);

        let pair_entry = provenance
            .get_entry(pair_id)
            .expect("combined pair provenance");
        assert!(pair_entry.is_active());
        assert_eq!(
            pair_entry.trust_ir_origins,
            vec![TrustIrInstId(70), TrustIrInstId(71)]
        );
        let transform = pair_entry.transforms.last().unwrap();
        assert_eq!(transform.pass, PassId::new("proof-opts"));
        assert_eq!(
            transform.kind,
            TransformKind::Merged {
                sources: vec![first_id, second_id],
            }
        );
        assert!(provenance.get_entry(first_id).is_none());
        assert!(provenance.get_entry(second_id).is_none());
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(70)),
            Some(&[pair_id][..])
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(71)),
            Some(&[pair_id][..])
        );
        assert_eq!(provenance.get_entry(ret_id).unwrap().transforms.len(), 1);
    }

    #[test]
    fn test_madd_folded_pair_certificate_binds_merged_source_identities() {
        fn madd_pair_cert_with_origin_delta(delta: u32) -> (OptCertificate, u128, u128) {
            let idx2 = MachInst::new(AArch64Opcode::Movz, vec![vreg(5), imm(2)]);
            let scale0 = MachInst::new(AArch64Opcode::Movz, vec![vreg(6), imm(8)]);
            let madd0 = MachInst::new(
                AArch64Opcode::Madd,
                vec![vreg(7), vreg(5), vreg(6), vreg(2)],
            );
            let str0 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(7), imm(0)]);
            let idx3 = MachInst::new(AArch64Opcode::Movz, vec![vreg(8), imm(3)]);
            let scale1 = MachInst::new(AArch64Opcode::Movz, vec![vreg(9), imm(8)]);
            let madd1 = MachInst::new(
                AArch64Opcode::Madd,
                vec![vreg(10), vreg(8), vreg(9), vreg(2)],
            );
            let str1 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(1), vreg(10), imm(0)]);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let mut func = make_func_with_insts(vec![
                idx2, scale0, madd0, str0, idx3, scale1, madd1, str1, ret,
            ]);

            let first_origins = vec![
                TrustIrInstId(100),
                TrustIrInstId(101),
                TrustIrInstId(102),
                TrustIrInstId(103),
            ];
            let second_origins = vec![
                TrustIrInstId(110),
                TrustIrInstId(111),
                TrustIrInstId(112 + delta),
                TrustIrInstId(114),
            ];
            let mut provenance = ProvenanceMap::new();
            for (origin, inst_id) in first_origins
                .iter()
                .chain(second_origins.iter())
                .copied()
                .zip([
                    InstId(0),
                    InstId(1),
                    InstId(2),
                    InstId(3),
                    InstId(4),
                    InstId(5),
                    InstId(6),
                    InstId(7),
                ])
            {
                provenance.record_lowering(origin, &[inst_id], PassId::new("isel"));
            }

            let mut addr_mode = AddrModeEarlyFormation;
            let mut addr_mode_analyses = AnalysisCache::new();
            assert!(MachinePass::run_with_analyses_and_provenance(
                &mut addr_mode,
                &mut func,
                &mut addr_mode_analyses,
                &mut provenance,
            ));
            assert_eq!(
                func.block(func.entry).insts,
                vec![InstId(3), InstId(7), InstId(8)]
            );
            assert_eq!(
                func.inst(InstId(3)).operands,
                vec![vreg(0), vreg(2), imm(16)]
            );
            assert_eq!(
                func.inst(InstId(7)).operands,
                vec![vreg(1), vreg(2), imm(24)]
            );

            let first_merged_origins = provenance
                .get_entry(InstId(3))
                .expect("first folded store provenance")
                .trust_ir_origins
                .clone();
            let second_merged_origins = provenance
                .get_entry(InstId(7))
                .expect("second folded store provenance")
                .trust_ir_origins
                .clone();
            assert_eq!(first_merged_origins, first_origins);
            assert_eq!(second_merged_origins, second_origins);

            let raw_folded_pair_hash = region_hash(&func, &[InstId(3), InstId(7)]);
            let first_source_hash = source_trust_ir_region_hash(&func.name, &first_merged_origins);
            let second_source_hash =
                source_trust_ir_region_hash(&func.name, &second_merged_origins);
            let expected_source_hash = combined_source_region_identity_hash(
                &func.name,
                &[first_source_hash, second_source_hash],
            );

            let mut proof_opts = ProofOptimization::new();
            proof_opts.set_inst_proof_facts(InstId(3), vec![ProofFact::Aligned(16)]);
            proof_opts.set_inst_proof_facts(InstId(7), vec![ProofFact::Aligned(16)]);
            let mut proof_analyses = AnalysisCache::new();
            assert!(MachinePass::run_with_analyses_and_provenance(
                &mut proof_opts,
                &mut func,
                &mut proof_analyses,
                &mut provenance,
            ));
            assert_eq!(proof_opts.certificates().len(), 1);
            let cert = proof_opts.certificates()[0].clone();
            assert_eq!(cert.kind, OptCertificateKind::PairCombined);
            assert_eq!(cert.source_region_hash, expected_source_hash);
            assert_ne!(cert.source_region_hash, raw_folded_pair_hash);

            (cert, expected_source_hash, raw_folded_pair_hash)
        }

        let (base, base_source_hash, base_raw_hash) = madd_pair_cert_with_origin_delta(0);
        let (drifted, drifted_source_hash, drifted_raw_hash) = madd_pair_cert_with_origin_delta(1);

        assert_eq!(base.source_region_hash, base_source_hash);
        assert_eq!(drifted.source_region_hash, drifted_source_hash);
        assert_ne!(base.source_region_hash, base_raw_hash);
        assert_ne!(drifted.source_region_hash, drifted_raw_hash);
        assert_ne!(
            base.source_region_hash, drifted.source_region_hash,
            "changing a folded MADD-chain trust_ir origin must change source identity"
        );
        assert_eq!(
            base.target_region_hash, drifted.target_region_hash,
            "same folded pair target code should keep the target identity stable"
        );
        assert_eq!(
            base.proof_hash, drifted.proof_hash,
            "same consumed alignment fact should keep the proof identity stable"
        );
        assert_ne!(
            base.validation_hash, drifted.validation_hash,
            "validation binds source identity even when target/proof stay stable"
        );
        assert_ne!(
            base.certificate_id, drifted.certificate_id,
            "certificate identity must drift with the folded source identity"
        );
    }

    #[test]
    fn test_aligned_pair_rejects_non_power_of_two_alignment_fact() {
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X0), preg(X2), imm(0)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X1), preg(X2), imm(8)]);
        let mut func = make_func_with_insts(vec![ldr0, ldr1]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(24)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

        assert!(!pass.run(&mut func));
        assert_eq!(pass.stats().pair_mem_ops_combined, 0);
        let block = func.block(func.entry);
        assert_eq!(func.inst(block.insts[0]).opcode, AArch64Opcode::LdrRI);
        assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::LdrRI);
        assert_eq!(pass.certificates().len(), 1);
        let cert = &pass.certificates()[0];
        assert_eq!(cert.kind, OptCertificateKind::PairCombined);
        assert_eq!(
            cert.consumed_facts,
            vec![OptConsumedProofFact::ProofFact(ProofFact::Aligned(24))]
        );
        let rejection = cert.rejection.as_ref().expect("rejection evidence");
        assert_eq!(rejection.code, ProofDiagnosticCode::RewriteRejected);
        assert_eq!(rejection.fact, "Aligned");
        assert_eq!(
            rejection.detail,
            "pair-start address is not proven by an Aligned(N) fact that implies 16-byte alignment"
        );
    }

    #[test]
    fn test_aligned_pair_rejects_insufficient_alignment_fact_with_stable_evidence() {
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X0), preg(X2), imm(0)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X1), preg(X2), imm(8)]);
        let mut func = make_func_with_insts(vec![ldr0, ldr1]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(8)]);

        assert!(!pass.run(&mut func));
        assert_eq!(pass.stats().pair_mem_ops_combined, 0);
        assert_eq!(func.block(func.entry).insts, vec![InstId(0), InstId(1)]);
        assert_eq!(pass.certificates().len(), 1);
        let cert = &pass.certificates()[0];
        assert_eq!(
            cert.consumed_facts,
            vec![OptConsumedProofFact::ProofFact(ProofFact::Aligned(8))]
        );
        let rejection = cert.rejection.as_ref().expect("rejection evidence");
        assert_eq!(rejection.code, ProofDiagnosticCode::RewriteRejected);
        assert_eq!(rejection.fact, "Aligned");
        assert_eq!(
            rejection.detail,
            "pair-start address is not proven by an Aligned(N) fact that implies 16-byte alignment"
        );
        assert_ne!(cert.validation_hash, 0);
    }

    #[test]
    fn test_aligned_pair_rejects_load_that_defines_second_base() {
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X2), preg(X2), imm(0)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X1), preg(X2), imm(8)]);
        let mut func = make_func_with_insts(vec![ldr0, ldr1]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

        assert!(!pass.run(&mut func));
        assert_eq!(pass.stats().pair_mem_ops_combined, 0);
        let block = func.block(func.entry);
        assert_eq!(block.insts, vec![InstId(0), InstId(1)]);
    }

    #[test]
    fn test_aligned_pair_rejects_same_vreg_load_dest() {
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(2), imm(0)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(2), imm(8)]);
        let mut func = make_func_with_insts(vec![ldr0, ldr1]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

        assert!(!pass.run(&mut func));
        assert_eq!(pass.stats().pair_mem_ops_combined, 0);
        assert_eq!(func.block(func.entry).insts, vec![InstId(0), InstId(1)]);
    }

    #[test]
    fn test_aligned_pair_rejects_load_that_defines_vreg_base_first() {
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(2), imm(0)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(1), vreg(2), imm(8)]);
        let mut func = make_func_with_insts(vec![ldr0, ldr1]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

        assert!(!pass.run(&mut func));
        assert_eq!(pass.stats().pair_mem_ops_combined, 0);
        assert_eq!(func.block(func.entry).insts, vec![InstId(0), InstId(1)]);
    }

    #[test]
    fn test_aligned_pair_rejects_load_that_defines_vreg_base_second_until_spills_are_verified() {
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(2), imm(0)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(2), imm(8)]);
        let mut func = make_func_with_insts(vec![ldr0, ldr1]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

        assert!(!pass.run(&mut func));
        assert_eq!(pass.stats().pair_mem_ops_combined, 0);
        assert_eq!(func.block(func.entry).insts, vec![InstId(0), InstId(1)]);
    }

    #[test]
    fn test_aligned_pair_rejects_xzr_transfer_register() {
        let str0 = MachInst::new(AArch64Opcode::StrRI, vec![preg(XZR), preg(X2), imm(0)]);
        let str1 = MachInst::new(AArch64Opcode::StrRI, vec![preg(X1), preg(X2), imm(8)]);
        let mut func = make_func_with_insts(vec![str0, str1]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

        assert!(!pass.run(&mut func));
        assert_eq!(pass.stats().pair_mem_ops_combined, 0);
    }

    #[test]
    fn test_aligned_pair_rejects_gpr32_vreg_transfer_register() {
        let str0 = MachInst::new(AArch64Opcode::StrRI, vec![vreg32(0), vreg(2), imm(0)]);
        let str1 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(1), vreg(2), imm(8)]);
        let mut func = make_func_with_insts(vec![str0, str1]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

        assert!(!pass.run(&mut func));
        assert_eq!(pass.stats().pair_mem_ops_combined, 0);
    }

    #[test]
    fn test_aligned_pair_rejects_gpr32_vreg_base_register() {
        let str0 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg32(2), imm(0)]);
        let str1 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(1), vreg32(2), imm(8)]);
        let mut func = make_func_with_insts(vec![str0, str1]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

        assert!(!pass.run(&mut func));
        assert_eq!(pass.stats().pair_mem_ops_combined, 0);
    }

    #[test]
    fn test_aligned_pair_requires_explicit_special_sp_base() {
        let str0 = MachInst::new(AArch64Opcode::StrRI, vec![preg(X0), preg(SP), imm(0)]);
        let str1 = MachInst::new(AArch64Opcode::StrRI, vec![preg(X1), preg(SP), imm(8)]);
        let mut preg_sp_func = make_func_with_insts(vec![str0, str1]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

        assert!(!pass.run(&mut preg_sp_func));
        assert_eq!(pass.stats().pair_mem_ops_combined, 0);

        let str0 = MachInst::new(
            AArch64Opcode::StrRI,
            vec![preg(X0), MachOperand::Special(SpecialReg::SP), imm(0)],
        );
        let str1 = MachInst::new(
            AArch64Opcode::StrRI,
            vec![preg(X1), MachOperand::Special(SpecialReg::SP), imm(8)],
        );
        let mut special_sp_func = make_func_with_insts(vec![str0, str1]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

        assert!(pass.run(&mut special_sp_func));
        assert_eq!(pass.stats().pair_mem_ops_combined, 1);
        let block = special_sp_func.block(special_sp_func.entry);
        let pair = special_sp_func.inst(block.insts[0]);
        assert_eq!(
            pair.operands,
            vec![
                preg(X0),
                preg(X1),
                MachOperand::Special(SpecialReg::SP),
                imm(0),
            ]
        );
    }

    #[test]
    fn test_aligned_pair_skips_proof_annotated_sources_to_avoid_stale_certificates() {
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X0), preg(X2), imm(0)])
            .with_proof(ProofAnnotation::ValidBorrow);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X1), preg(X2), imm(8)]);
        let mut func = make_func_with_insts(vec![ldr0, ldr1]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

        assert!(pass.run(&mut func));
        assert_eq!(pass.stats().pair_mem_ops_combined, 0);
        assert_eq!(func.block(func.entry).insts, vec![InstId(0), InstId(1)]);
        assert_eq!(pass.certificates().len(), 1);
        assert_eq!(
            pass.certificates()[0].kind,
            OptCertificateKind::FlagsRefined
        );
    }

    #[test]
    fn test_aligned_pair_rejects_signed_pair_offset_overflow() {
        let ldr0 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X0), preg(X6), imm(512)]);
        let ldr1 = MachInst::new(AArch64Opcode::LdrRI, vec![preg(X1), preg(X6), imm(520)]);
        let mut func = make_func_with_insts(vec![ldr0, ldr1]);

        let mut pass = ProofOptimization::new();
        pass.set_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)]);
        pass.set_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

        assert!(!pass.run(&mut func));
        assert_eq!(pass.stats().pair_mem_ops_combined, 0);
    }

    #[test]
    fn test_not_null_certificate_identity_changes_with_guard_operand() {
        fn guard_cert(ptr: u32) -> OptCertificate {
            let guard = MachInst::new(AArch64Opcode::TrapNullIfZero, vec![vreg(ptr)])
                .with_proof(ProofAnnotation::NotNull);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let mut func = make_func_with_insts(vec![guard, ret]);

            let mut pass = ProofOptimization::new();
            assert!(pass.run(&mut func));
            pass.certificates()[0].clone()
        }

        let ptr_0 = guard_cert(0);
        let ptr_1 = guard_cert(1);

        assert_eq!(ptr_0.target_region_hash, ptr_1.target_region_hash);
        assert_ne!(ptr_0.source_region_hash, ptr_1.source_region_hash);
        assert_ne!(ptr_0.validation_hash, ptr_1.validation_hash);
        assert_ne!(ptr_0.certificate_id, ptr_1.certificate_id);
    }

    #[test]
    fn test_certificate_identity_stable_across_unrelated_inst_id_drift() {
        fn overflow_cert(with_prefix: bool) -> OptCertificate {
            let mut insts = Vec::new();
            if with_prefix {
                insts.push(MachInst::new(AArch64Opcode::Nop, vec![]));
            }
            insts.push(
                MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
                    .with_proof(ProofAnnotation::NoOverflow),
            );
            insts.push(MachInst::new(
                AArch64Opcode::TrapOverflow,
                vec![imm(0x06), MachOperand::Block(BlockId(1))],
            ));
            insts.push(MachInst::new(AArch64Opcode::Ret, vec![]));
            let mut func = make_func_with_insts(insts);
            func.create_block();

            let mut pass = ProofOptimization::new();
            assert!(pass.run(&mut func));
            pass.certificates()[0].clone()
        }

        let base = overflow_cert(false);
        let drifted = overflow_cert(true);

        assert_ne!(base.primary_inst, drifted.primary_inst);
        assert_eq!(base.source_region_hash, drifted.source_region_hash);
        assert_eq!(base.target_region_hash, drifted.target_region_hash);
        assert_eq!(base.validation_hash, drifted.validation_hash);
        assert_eq!(base.certificate_id, drifted.certificate_id);
    }

    #[test]
    fn test_certificate_generated_on_bounds_check_elimination() {
        let guard = MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![vreg(0), vreg(1), imm(8)],
        )
        .with_proof(ProofAnnotation::InBounds);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![guard, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let certs = pass.certificates();
        assert_eq!(certs.len(), 1);
        let cert = &certs[0];
        assert_eq!(cert.annotation, Some(ProofAnnotation::InBounds));
        assert_eq!(cert.primary_inst, InstId(0));
        assert!(cert.affected_insts.is_empty());
        assert_eq!(cert.kind, OptCertificateKind::GuardEliminated);
    }

    #[test]
    fn test_certificate_generated_on_null_check_trap_null_if_zero() {
        let guard = MachInst::new(AArch64Opcode::TrapNullIfZero, vec![vreg(0)])
            .with_proof(ProofAnnotation::NotNull);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![guard, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let certs = pass.certificates();
        assert_eq!(certs.len(), 1);
        let cert = &certs[0];
        assert_eq!(cert.annotation, Some(ProofAnnotation::NotNull));
        assert_eq!(cert.primary_inst, InstId(0));
        assert!(cert.affected_insts.is_empty());
        assert_eq!(cert.kind, OptCertificateKind::GuardEliminated);
    }

    #[test]
    fn test_certificate_rejects_legacy_null_check_cbnz() {
        let cbnz = MachInst::new(
            AArch64Opcode::Cbnz,
            vec![vreg(0), MachOperand::Block(BlockId(1))],
        )
        .with_proof(ProofAnnotation::NotNull);

        let mut func = make_func_with_insts(vec![cbnz]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        let certs = pass.certificates();
        assert_eq!(certs.len(), 1);
        let cert = &certs[0];
        assert_eq!(cert.annotation, Some(ProofAnnotation::NotNull));
        assert_eq!(cert.primary_inst, InstId(0));
        assert!(cert.affected_insts.is_empty());
        assert_eq!(cert.kind, OptCertificateKind::GuardEliminated);
        assert!(cert.rejection.is_some());
    }

    #[test]
    fn test_certificate_rejects_legacy_null_check_cbz() {
        let cbz = MachInst::new(
            AArch64Opcode::Cbz,
            vec![vreg(0), MachOperand::Block(BlockId(1))],
        )
        .with_proof(ProofAnnotation::NotNull);

        let mut func = make_func_with_insts(vec![cbz]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));

        let certs = pass.certificates();
        assert_eq!(certs.len(), 1);
        let cert = &certs[0];
        assert_eq!(cert.annotation, Some(ProofAnnotation::NotNull));
        assert_eq!(cert.primary_inst, InstId(0));
        assert!(cert.affected_insts.is_empty());
        assert_eq!(cert.kind, OptCertificateKind::GuardEliminated);
        assert!(cert.rejection.is_some());
    }

    #[test]
    fn test_certificate_generated_on_valid_borrow() {
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(1), imm(0)])
            .with_proof(ProofAnnotation::ValidBorrow);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let certs = pass.certificates();
        assert_eq!(certs.len(), 1);
        let cert = &certs[0];
        assert_eq!(cert.annotation, Some(ProofAnnotation::ValidBorrow));
        assert_eq!(cert.primary_inst, InstId(0));
        assert!(cert.affected_insts.is_empty());
        assert_eq!(cert.kind, OptCertificateKind::FlagsRefined);
    }

    #[test]
    fn test_valid_borrow_refinement_is_idempotent() {
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(1), imm(0)])
            .with_proof(ProofAnnotation::ValidBorrow);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));
        assert!(
            func.inst(InstId(0))
                .flags
                .contains(InstFlags::PROOF_REORDERABLE)
        );
        assert_eq!(pass.stats().alias_refinements, 1);
        assert_eq!(pass.certificates().len(), 1);

        assert!(!pass.run(&mut func));
        assert!(
            func.inst(InstId(0))
                .flags
                .contains(InstFlags::PROOF_REORDERABLE)
        );
        assert_eq!(pass.stats().alias_refinements, 0);
        assert!(pass.certificates().is_empty());
    }

    #[test]
    fn test_certificate_generated_on_refcount_pair() {
        let retain = MachInst::new(AArch64Opcode::Retain, vec![vreg(0)])
            .with_proof(ProofAnnotation::PositiveRefCount);

        let release = MachInst::new(AArch64Opcode::Release, vec![vreg(0)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![retain, release, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let certs = pass.certificates();
        assert_eq!(certs.len(), 1);
        let cert = &certs[0];
        assert_eq!(cert.annotation, Some(ProofAnnotation::PositiveRefCount));
        assert_eq!(cert.primary_inst, InstId(0));
        assert_eq!(cert.affected_insts, vec![InstId(1)]);
        assert_eq!(cert.kind, OptCertificateKind::PairEliminated);
    }

    #[test]
    fn test_certificate_generated_on_divzero_elimination() {
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(0)])
            .with_proof(ProofAnnotation::NonZeroDivisor);
        let trap = MachInst::new(
            AArch64Opcode::TrapDivZero,
            vec![MachOperand::Block(BlockId(1))],
        );

        let udiv = MachInst::new(AArch64Opcode::UDiv, vec![vreg(2), vreg(0), vreg(1)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cmp, trap, udiv, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let certs = pass.certificates();
        assert_eq!(certs.len(), 1);
        let cert = &certs[0];
        assert_eq!(cert.annotation, Some(ProofAnnotation::NonZeroDivisor));
        assert_eq!(cert.primary_inst, InstId(0));
        assert_eq!(cert.affected_insts, vec![InstId(1)]);
        assert_eq!(cert.kind, OptCertificateKind::GuardEliminated);
    }

    #[test]
    fn test_certificate_generated_on_shift_check_elimination() {
        let cmp = MachInst::new(AArch64Opcode::CmpRI, vec![vreg(1), imm(64)])
            .with_proof(ProofAnnotation::ValidShift);

        let trap = MachInst::new(
            AArch64Opcode::TrapShiftRange,
            vec![MachOperand::Block(BlockId(1))],
        );

        let lsl = MachInst::new(AArch64Opcode::LslRR, vec![vreg(2), vreg(0), vreg(1)]);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![cmp, trap, lsl, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let certs = pass.certificates();
        assert_eq!(certs.len(), 1);
        let cert = &certs[0];
        assert_eq!(cert.annotation, Some(ProofAnnotation::ValidShift));
        assert_eq!(cert.primary_inst, InstId(0));
        assert_eq!(cert.affected_insts, vec![InstId(1)]);
        assert_eq!(cert.kind, OptCertificateKind::GuardEliminated);
    }

    #[test]
    fn test_certificate_generated_on_pure() {
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(0), vreg(1), imm(0)])
            .with_proof(ProofAnnotation::Pure);

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ldr, ret]);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let certs = pass.certificates();
        assert_eq!(certs.len(), 1);
        let cert = &certs[0];
        assert_eq!(cert.annotation, Some(ProofAnnotation::Pure));
        assert_eq!(cert.primary_inst, InstId(0));
        assert!(cert.affected_insts.is_empty());
        assert_eq!(cert.kind, OptCertificateKind::FlagsRefined);
    }

    #[test]
    fn test_certificates_cleared_on_rerun() {
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);

        let trap = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(BlockId(1))],
        );

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, trap, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));
        assert_eq!(pass.certificates().len(), 1);

        // Second run: no changes, certificates should be cleared.
        assert!(!pass.run(&mut func));
        assert!(pass.certificates().is_empty());
    }

    #[test]
    fn test_multiple_certificates_in_one_function() {
        let mut func = MachFunction::new(
            "test_multiple_certificates".to_string(),
            Signature::new(vec![], vec![]),
        );

        let work_block = func.create_block();
        let panic_block = func.create_block();

        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);
        let trap = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(panic_block)],
        );
        let branch = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(work_block)]);

        let adds_id = func.push_inst(adds);
        let trap_id = func.push_inst(trap);
        let branch_id = func.push_inst(branch);
        func.append_inst(func.entry, adds_id);
        func.append_inst(func.entry, trap_id);
        func.append_inst(func.entry, branch_id);

        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(3), vreg(0), imm(0)])
            .with_proof(ProofAnnotation::Pure);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);

        let ldr_id = func.push_inst(ldr);
        let ret_id = func.push_inst(ret);
        func.append_inst(work_block, ldr_id);
        func.append_inst(work_block, ret_id);

        let mut pass = ProofOptimization::new();
        assert!(pass.run(&mut func));

        let certs = pass.certificates();
        assert_eq!(certs.len(), 2);
        assert!(certs.iter().any(|cert| {
            cert.annotation == Some(ProofAnnotation::NoOverflow)
                && cert.primary_inst == adds_id
                && cert.affected_insts == vec![trap_id]
                && cert.kind == OptCertificateKind::CheckedToUnchecked
        }));
        assert!(certs.iter().any(|cert| {
            cert.annotation == Some(ProofAnnotation::Pure)
                && cert.primary_inst == ldr_id
                && cert.affected_insts.is_empty()
                && cert.kind == OptCertificateKind::FlagsRefined
        }));
        assert_eq!(pass.stats().total_certificates, 2);
    }

    #[test]
    fn test_no_certificates_without_proofs() {
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)]);

        let trap = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(BlockId(1))],
        );

        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, trap, ret]);
        func.create_block();

        let mut pass = ProofOptimization::new();
        assert!(!pass.run(&mut func));
        assert!(pass.certificates().is_empty());
        assert_eq!(pass.stats().total_certificates, 0);
    }
}
