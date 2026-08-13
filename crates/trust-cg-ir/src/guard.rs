// trust-cg-ir/guard.rs — Arch-neutral guard-elimination contract + Certified-Elimination Kernel (CEK)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Sentinel S0 — the arch-neutral contract for proof-driven guard elimination.
//!
//! This module is the **trusted core** of the guard-elimination design described in
//! `docs/proof-guard-elimination-design.md`. It defines:
//!
//! * [`GuardKind`] — the arch-neutral classification of eliminable runtime safety checks,
//!   and its total mapping to/from [`ProofAnnotation`].
//! * [`GuardOperandIdentity`] — operand identity bound to a *reproducible* fingerprint, so a
//!   later independent re-checker can re-derive it from the live carrier and confirm the proof
//!   is about *these* operands (closing the syntactic-match weakness).
//! * [`GuardObligationReceipt`] — what a carrier records about the obligation that *might*
//!   justify its removal. A receipt is a **claim slot, not permission**.
//! * [`decide`] — the Certified-Elimination Kernel: a **total, pure, panic-free** function that
//!   is the *sole minter* of an [`EliminationCertificate`]. It returns [`EliminationVerdict::Keep`]
//!   for every missing/malformed/under-discharged input (fail-safe by construction).
//! * [`recheck_elimination`] — the independent re-validation path used by the fail-closed
//!   re-checker (S4): it re-derives the operand fingerprint from the *observed* carrier and
//!   re-confirms discharge/lineage against the evidence, by a different code path than `decide`.
//! * [`GuardSiteLedger`] — a per-function snapshot of guard sites at carrier-birth plus
//!   guard-count **conservation** checking (emitted == surviving traps + certificates).
//!
//! ## S0 status (zero behavior change)
//!
//! The kernel logic here is *real*, not a stub — but in S0 nothing in the compile path feeds it
//! evidence (the [`DischargedEvidenceTable`] is empty and receipts carry no obligation id), so it
//! eliminates nothing in practice. S1 threads operand identity onto the carrier; S3 fills the
//! evidence table from trust-ir; S4 turns on the re-checker gate. The module depends only on
//! `std` and [`ProofAnnotation`], keeping the arch-neutral core decoupled from any backend.

use std::collections::BTreeMap;

use crate::inst::ProofAnnotation;

// ---------------------------------------------------------------------------
// Deterministic 128-bit FNV-1a hasher.
//
// We deliberately avoid `std::collections::hash_map::DefaultHasher` / `RandomState`: certificate
// and operand fingerprints must be byte-for-byte reproducible across processes so an independent
// re-checker can re-derive them. FNV-1a is small, total, and dependency-free.
// ---------------------------------------------------------------------------

const FNV_OFFSET_BASIS_128: u128 = 0x6c62272e07bb0142_62b821756295c58d;
const FNV_PRIME_128: u128 = 0x0000000001000000_000000000000013B;

#[derive(Debug, Clone)]
struct Fnv128(u128);

impl Fnv128 {
    #[inline]
    fn new() -> Self {
        Self(FNV_OFFSET_BASIS_128)
    }

    #[inline]
    fn write_u8(&mut self, b: u8) {
        self.0 ^= b as u128;
        self.0 = self.0.wrapping_mul(FNV_PRIME_128);
    }

    #[inline]
    fn write_u64(&mut self, v: u64) {
        for i in 0..8 {
            self.write_u8((v >> (i * 8)) as u8);
        }
    }

    #[inline]
    fn write_u128(&mut self, v: u128) {
        for i in 0..16 {
            self.write_u8((v >> (i * 8)) as u8);
        }
    }

    #[inline]
    fn write_i64(&mut self, v: i64) {
        self.write_u64(v as u64);
    }

    #[inline]
    fn write_str(&mut self, s: &str) {
        for b in s.bytes() {
            self.write_u8(b);
        }
        self.write_u8(0); // length-independent terminator
    }

    #[inline]
    fn write_opt_u128(&mut self, v: Option<u128>) {
        match v {
            Some(x) => {
                self.write_u8(1);
                self.write_u128(x);
            }
            None => self.write_u8(0),
        }
    }

    #[inline]
    fn finish(self) -> u128 {
        self.0
    }
}

// ---------------------------------------------------------------------------
// GuardKind — arch-neutral classification of eliminable runtime safety checks.
// ---------------------------------------------------------------------------

/// Arch-neutral classification of a removable runtime safety check.
///
/// Each variant corresponds to one class of trap a discharged proof can justify removing.
/// Metadata-only proofs (`Pure`, `ValidBorrow`, `PositiveRefCount`, `Associative`,
/// `Commutative`, `Idempotent`) are **not** guards and have no `GuardKind`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GuardKind {
    /// Array-bounds check: `index < bound` (unsigned).
    BoundsCheck,
    /// Null-pointer check: `ptr != 0`.
    NullPtr,
    /// Division-by-zero check: `divisor != 0`.
    DivZero,
    /// Shift-range check: `amount` in `[0, bitwidth)`.
    ShiftRange,
    /// Signed-overflow check (consumes the signed-compatible carrier family).
    SignedOverflow,
    /// Unsigned-overflow / underflow check.
    UnsignedOverflow,
}

impl GuardKind {
    /// Stable small discriminant used for hashing (never reorder existing values).
    #[inline]
    pub fn discriminant(self) -> u8 {
        match self {
            GuardKind::BoundsCheck => 1,
            GuardKind::NullPtr => 2,
            GuardKind::DivZero => 3,
            GuardKind::ShiftRange => 4,
            GuardKind::SignedOverflow => 5,
            GuardKind::UnsignedOverflow => 6,
        }
    }

    /// Every `GuardKind` is, by definition, eliminable by a matching discharged proof. This is a
    /// gate the kernel still checks explicitly so the property is local and testable.
    #[inline]
    pub fn is_eliminable_by_proof(self) -> bool {
        matches!(
            self,
            GuardKind::BoundsCheck
                | GuardKind::NullPtr
                | GuardKind::DivZero
                | GuardKind::ShiftRange
                | GuardKind::SignedOverflow
                | GuardKind::UnsignedOverflow
        )
    }

    /// The canonical proof annotation that justifies eliminating this guard kind.
    ///
    /// Note: `SignedOverflow` is justified by either `NoOverflow` (legacy, signed-compatible) or
    /// `NoSignedOverflow`; this returns the canonical `NoSignedOverflow`. Use
    /// [`GuardKind::from_proof_annotation`] for the (many-to-one) reverse direction.
    #[inline]
    pub fn matching_proof_annotation(self) -> ProofAnnotation {
        match self {
            GuardKind::BoundsCheck => ProofAnnotation::InBounds,
            GuardKind::NullPtr => ProofAnnotation::NotNull,
            GuardKind::DivZero => ProofAnnotation::NonZeroDivisor,
            GuardKind::ShiftRange => ProofAnnotation::ValidShift,
            GuardKind::SignedOverflow => ProofAnnotation::NoSignedOverflow,
            GuardKind::UnsignedOverflow => ProofAnnotation::NoUnsignedOverflow,
        }
    }

    /// Map a [`ProofAnnotation`] to the guard kind it can eliminate, or `None` for metadata-only
    /// proofs that never correspond to a runtime guard. `NoOverflow` (legacy, signed-compatible)
    /// and `NoSignedOverflow` both map to [`GuardKind::SignedOverflow`].
    #[inline]
    pub fn from_proof_annotation(pa: ProofAnnotation) -> Option<GuardKind> {
        match pa {
            ProofAnnotation::InBounds => Some(GuardKind::BoundsCheck),
            ProofAnnotation::NotNull => Some(GuardKind::NullPtr),
            ProofAnnotation::NonZeroDivisor => Some(GuardKind::DivZero),
            ProofAnnotation::ValidShift => Some(GuardKind::ShiftRange),
            ProofAnnotation::NoOverflow | ProofAnnotation::NoSignedOverflow => {
                Some(GuardKind::SignedOverflow)
            }
            ProofAnnotation::NoUnsignedOverflow => Some(GuardKind::UnsignedOverflow),
            // Metadata-only proofs: not runtime guards.
            ProofAnnotation::ValidBorrow
            | ProofAnnotation::PositiveRefCount
            | ProofAnnotation::Pure
            | ProofAnnotation::Associative
            | ProofAnnotation::Commutative
            | ProofAnnotation::Idempotent => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Operand identity.
// ---------------------------------------------------------------------------

/// One operand of a guard, modeled arch-neutrally so this module never imports a backend operand
/// type. A per-backend adapter maps real machine operands onto these references.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GuardOperandRef {
    /// A (virtual) register operand identified by a stable, regalloc-survivable id.
    Reg(u32),
    /// An immediate operand.
    Imm(i64),
}

/// The operands a guard is a claim *about*, plus a reproducible fingerprint.
///
/// The fingerprint is a pure function of the operand list, so the independent re-checker can
/// re-derive it from the live carrier and reject a certificate whose operands no longer match —
/// the defeat of the syntactic-match weakness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GuardOperandIdentity {
    /// Ordered, role-significant operands (e.g. bounds = `[base, index, bound]`; null = `[ptr]`).
    pub operands: Vec<GuardOperandRef>,
    /// `fingerprint_operands(&operands)` — cached for convenience; always reproducible.
    pub fingerprint: u128,
}

impl GuardOperandIdentity {
    /// Build an identity, computing the reproducible fingerprint from the operands.
    pub fn new(operands: Vec<GuardOperandRef>) -> Self {
        let fingerprint = fingerprint_operands(&operands);
        Self {
            operands,
            fingerprint,
        }
    }

    /// True iff `fingerprint` equals the fingerprint recomputed from `operands`. Always true for
    /// values built via [`GuardOperandIdentity::new`]; the re-checker calls this to catch tamper.
    pub fn is_consistent(&self) -> bool {
        self.fingerprint == fingerprint_operands(&self.operands)
    }
}

/// Reproducible fingerprint of an ordered operand list.
pub fn fingerprint_operands(operands: &[GuardOperandRef]) -> u128 {
    let mut h = Fnv128::new();
    h.write_str("trust-cg.guard.operands.v1");
    h.write_u64(operands.len() as u64);
    for op in operands {
        match op {
            GuardOperandRef::Reg(r) => {
                h.write_u8(0);
                h.write_u64(*r as u64);
            }
            GuardOperandRef::Imm(i) => {
                h.write_u8(1);
                h.write_i64(*i);
            }
        }
    }
    h.finish()
}

/// Reproducible carrier→obligation **binding key**: the operand fingerprint with the carrier's
/// [`GuardKind`] folded in (defense-in-depth).
///
/// [`fingerprint_operands`] is deliberately kind-agnostic — it is the *operand-drift* fingerprint
/// stored in [`GuardOperandIdentity`] and re-derived by the certificate re-checker
/// ([`recheck_elimination`]). But the per-function carrier→obligation map (`*::guard_obligations`)
/// and the kernel's lookup of it MUST distinguish two single-operand carriers of *different* kinds
/// over the *same* vreg — e.g. a `NullPtr [ptr]` and a `DivZero [divisor]` both on `Reg(5)` lift to
/// the identical operand list and therefore the identical [`fingerprint_operands`], colliding in the
/// map (last-writer-wins). This helper writes a distinct domain tag, mixes in
/// [`GuardKind::discriminant`], then the same operand sequence, so carriers of different kinds over
/// identical operands get *distinct* keys.
///
/// Use this on BOTH ends of the binding: every ISel `guard_obligations` insert (record side) and
/// every kernel re-derive that looks the binding up (lookup side). Because each re-derive site has
/// already classified the live carrier's kind (via `classify_carrier`) before the lookup, both ends
/// can fold the SAME kind in symmetrically. A kind/operand mismatch simply fails the lookup, so the
/// carrier is KEPT — fail-safe by construction; it can never cause over-elimination.
///
/// Note: the certificate/recheck layer ([`compute_validation_hash`], [`recheck_elimination`]) is
/// already kind-bound (it mixes [`GuardKind::discriminant`] in independently), so this change is
/// purely the missing cross-check at the obligation-binding layer.
pub fn fingerprint_for_kind(kind: GuardKind, operands: &[GuardOperandRef]) -> u128 {
    let mut h = Fnv128::new();
    h.write_str("trust-cg.guard.kindfp.v1");
    h.write_u8(kind.discriminant());
    h.write_u64(operands.len() as u64);
    for op in operands {
        match op {
            GuardOperandRef::Reg(r) => {
                h.write_u8(0);
                h.write_u64(*r as u64);
            }
            GuardOperandRef::Imm(i) => {
                h.write_u8(1);
                h.write_i64(*i);
            }
        }
    }
    h.finish()
}

// ---------------------------------------------------------------------------
// Discharged-evidence table (filled from trust-ir at S3; empty in S0).
// ---------------------------------------------------------------------------

/// Strength tier of a discharged obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DischargeStatus {
    /// Discharged by the trust-ir prover; trusted to the same degree trust-ir already is.
    Discharged,
    /// Discharged *and* backed by CleanCic lineage evidence whose digest the kernel re-derives.
    Certified,
}

impl DischargeStatus {
    #[inline]
    fn discriminant(self) -> u8 {
        match self {
            DischargeStatus::Discharged => 1,
            DischargeStatus::Certified => 2,
        }
    }
}

/// Maps trust-ir obligation ids to their discharge status and (for `Certified`) the lineage
/// digest the kernel re-derives. S0 leaves this empty, so the kernel eliminates nothing.
#[derive(Debug, Clone, Default)]
pub struct DischargedEvidenceTable {
    obligations: BTreeMap<u128, (DischargeStatus, Option<u128>)>,
}

impl DischargedEvidenceTable {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a discharged obligation. `lineage_digest` must be `Some` for `Certified`.
    pub fn insert(
        &mut self,
        obligation_id: u128,
        status: DischargeStatus,
        lineage_digest: Option<u128>,
    ) {
        self.obligations
            .insert(obligation_id, (status, lineage_digest));
    }

    /// Look up an obligation's discharge status and lineage digest.
    pub fn lookup(&self, obligation_id: u128) -> Option<(DischargeStatus, Option<u128>)> {
        self.obligations.get(&obligation_id).copied()
    }

    pub fn is_empty(&self) -> bool {
        self.obligations.is_empty()
    }

    pub fn len(&self) -> usize {
        self.obligations.len()
    }
}

// ---------------------------------------------------------------------------
// Receipt, verdict, certificate.
// ---------------------------------------------------------------------------

/// What a carrier records about the obligation that *might* justify its removal.
///
/// A receipt is a **claim slot, not permission**: only [`decide`] can turn a well-formed receipt
/// (with a discharged obligation) into an [`EliminationCertificate`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GuardObligationReceipt {
    /// What kind of guard this carrier is.
    pub kind: GuardKind,
    /// The operands the guard is a claim about.
    pub operand_identity: GuardOperandIdentity,
    /// Reference to the originating trust-ir obligation (opaque id; `None` until S1/S3 thread it).
    pub proof_obligation_id: Option<u128>,
    /// Lineage digest the receipt claims for the `Certified` tier (`None` for the `Discharged` tier).
    pub lineage_digest: Option<u128>,
}

impl GuardObligationReceipt {
    /// Construct a receipt with no bound obligation (the S0 default; `decide` returns `Keep`).
    pub fn unbound(kind: GuardKind, operand_identity: GuardOperandIdentity) -> Self {
        Self {
            kind,
            operand_identity,
            proof_obligation_id: None,
            lineage_digest: None,
        }
    }
}

/// The kernel's decision for one guard site. `Keep` is the structural default.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EliminationVerdict {
    /// Leave the guard in place; it will lower to a real runtime trap. `reason` is diagnostic.
    Keep { reason: &'static str },
    /// Authorize removal. The certificate is the *sole* authorization a backend pass may act on.
    Eliminate { certificate: EliminationCertificate },
}

impl EliminationVerdict {
    pub fn is_eliminate(&self) -> bool {
        matches!(self, EliminationVerdict::Eliminate { .. })
    }

    pub fn certificate(&self) -> Option<&EliminationCertificate> {
        match self {
            EliminationVerdict::Eliminate { certificate } => Some(certificate),
            EliminationVerdict::Keep { .. } => None,
        }
    }
}

/// A re-checkable record authorizing exactly one guard elimination.
///
/// Construction is private to this module: only [`decide`] (the kernel) mints one, so a backend
/// pass cannot fabricate authorization. The `validation_hash` binds guard kind, operand
/// fingerprint, obligation id, discharge status, and lineage digest, and is independently
/// re-derivable via [`EliminationCertificate::recompute_validation_hash`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EliminationCertificate {
    certificate_id: u128,
    guard_kind: GuardKind,
    operand_fingerprint: u128,
    obligation_id: u128,
    discharge_status: DischargeStatus,
    lineage_digest: Option<u128>,
    validation_hash: u128,
}

impl EliminationCertificate {
    /// Mint a certificate. Private: only the kernel calls this, so `Eliminate` cannot be forged
    /// by untrusted backend code.
    fn mint(
        guard_kind: GuardKind,
        operand_fingerprint: u128,
        obligation_id: u128,
        discharge_status: DischargeStatus,
        lineage_digest: Option<u128>,
    ) -> Self {
        let validation_hash = compute_validation_hash(
            guard_kind,
            operand_fingerprint,
            obligation_id,
            discharge_status,
            lineage_digest,
        );
        Self {
            // The hash doubles as a stable id; it is deterministic (no RNG/clock).
            certificate_id: validation_hash,
            guard_kind,
            operand_fingerprint,
            obligation_id,
            discharge_status,
            lineage_digest,
            validation_hash,
        }
    }

    pub fn certificate_id(&self) -> u128 {
        self.certificate_id
    }
    pub fn guard_kind(&self) -> GuardKind {
        self.guard_kind
    }
    pub fn operand_fingerprint(&self) -> u128 {
        self.operand_fingerprint
    }
    pub fn obligation_id(&self) -> u128 {
        self.obligation_id
    }
    pub fn discharge_status(&self) -> DischargeStatus {
        self.discharge_status
    }
    pub fn lineage_digest(&self) -> Option<u128> {
        self.lineage_digest
    }
    pub fn validation_hash(&self) -> u128 {
        self.validation_hash
    }

    /// Recompute the validation hash from the certificate's own fields (independent re-derivation).
    pub fn recompute_validation_hash(&self) -> u128 {
        compute_validation_hash(
            self.guard_kind,
            self.operand_fingerprint,
            self.obligation_id,
            self.discharge_status,
            self.lineage_digest,
        )
    }

    /// True iff the certificate's stored hash matches a fresh re-derivation from its fields.
    pub fn is_internally_consistent(&self) -> bool {
        self.validation_hash == self.recompute_validation_hash()
            && self.certificate_id == self.validation_hash
    }
}

fn compute_validation_hash(
    guard_kind: GuardKind,
    operand_fingerprint: u128,
    obligation_id: u128,
    discharge_status: DischargeStatus,
    lineage_digest: Option<u128>,
) -> u128 {
    let mut h = Fnv128::new();
    h.write_str("trust-cg.guard.cert.v1");
    h.write_u8(guard_kind.discriminant());
    h.write_u128(operand_fingerprint);
    h.write_u128(obligation_id);
    h.write_u8(discharge_status.discriminant());
    h.write_opt_u128(lineage_digest);
    h.finish()
}

// ---------------------------------------------------------------------------
// The Certified-Elimination Kernel (CEK).
// ---------------------------------------------------------------------------

/// The trusted decision: may this guard be removed?
///
/// **Total, pure, panic-free.** Returns [`EliminationVerdict::Eliminate`] iff *all* hold:
/// 1. the guard kind is proof-eliminable;
/// 2. the receipt carries a non-empty, self-consistent operand identity;
/// 3. the receipt references an obligation present in `evidence`;
/// 4. that obligation is `Discharged` or `Certified`;
/// 5. for `Certified`, the receipt's lineage digest is present and equals the evidence's
///    (re-derived) lineage digest.
///
/// Otherwise it returns [`EliminationVerdict::Keep`] with a diagnostic reason — the fail-safe
/// default. The minted certificate binds the operand fingerprint, so a later re-check against the
/// live carrier's operands (see [`recheck_elimination`]) detects any operand mismatch.
pub fn decide(
    receipt: &GuardObligationReceipt,
    evidence: &DischargedEvidenceTable,
) -> EliminationVerdict {
    if !receipt.kind.is_eliminable_by_proof() {
        return EliminationVerdict::Keep {
            reason: "guard kind is not proof-eliminable",
        };
    }
    if receipt.operand_identity.operands.is_empty() {
        return EliminationVerdict::Keep {
            reason: "receipt has no operand identity",
        };
    }
    if !receipt.operand_identity.is_consistent() {
        return EliminationVerdict::Keep {
            reason: "operand identity fingerprint is inconsistent",
        };
    }
    let obligation_id = match receipt.proof_obligation_id {
        Some(id) => id,
        None => {
            return EliminationVerdict::Keep {
                reason: "no proof obligation bound to this guard",
            };
        }
    };
    let (status, evidence_lineage) = match evidence.lookup(obligation_id) {
        Some(entry) => entry,
        None => {
            return EliminationVerdict::Keep {
                reason: "obligation is not discharged in the evidence table",
            };
        }
    };

    // Certified tier: the kernel re-derives and re-checks the CleanCic lineage binding, so
    // trust-cg never blindly trusts a "Certified" label. Discharged tier: trusted as trust-ir is.
    let cert_lineage = match status {
        DischargeStatus::Discharged => None,
        DischargeStatus::Certified => match (receipt.lineage_digest, evidence_lineage) {
            (Some(claimed), Some(actual)) if claimed == actual => Some(actual),
            _ => {
                return EliminationVerdict::Keep {
                    reason: "certified-tier lineage digest missing or mismatched",
                };
            }
        },
    };

    let certificate = EliminationCertificate::mint(
        receipt.kind,
        receipt.operand_identity.fingerprint,
        obligation_id,
        status,
        cert_lineage,
    );
    EliminationVerdict::Eliminate { certificate }
}

/// Outcome of an independent re-check of a previously-issued certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecheckOutcome {
    /// The elimination is independently re-justified against the observed operands + evidence.
    Valid,
    /// The elimination could not be re-justified; the compile must fail closed. `reason` says why.
    Rejected { reason: &'static str },
}

/// Independently re-validate a certificate against the *observed* carrier operands and the
/// evidence — the re-checker's "different path" (S4). Unlike [`decide`], this starts from the
/// operands actually present at the elimination site and re-derives the fingerprint, so an
/// elimination whose operands drifted (or whose obligation is not really discharged) is rejected.
pub fn recheck_elimination(
    certificate: &EliminationCertificate,
    observed_operands: &[GuardOperandRef],
    evidence: &DischargedEvidenceTable,
) -> RecheckOutcome {
    if !certificate.is_internally_consistent() {
        return RecheckOutcome::Rejected {
            reason: "certificate validation hash does not re-derive",
        };
    }
    if !certificate.guard_kind.is_eliminable_by_proof() {
        return RecheckOutcome::Rejected {
            reason: "certificate guard kind is not proof-eliminable",
        };
    }
    if observed_operands.is_empty() {
        return RecheckOutcome::Rejected {
            reason: "no observed operands at elimination site",
        };
    }
    // Re-derive the operand fingerprint from what is actually at the site.
    if fingerprint_operands(observed_operands) != certificate.operand_fingerprint {
        return RecheckOutcome::Rejected {
            reason: "observed operands do not match certificate fingerprint",
        };
    }
    // Re-confirm discharge status and lineage from the evidence, independently.
    let (status, evidence_lineage) = match evidence.lookup(certificate.obligation_id) {
        Some(entry) => entry,
        None => {
            return RecheckOutcome::Rejected {
                reason: "obligation no longer discharged in evidence",
            };
        }
    };
    if status != certificate.discharge_status {
        return RecheckOutcome::Rejected {
            reason: "discharge status disagrees with certificate",
        };
    }
    match status {
        DischargeStatus::Discharged => {
            if certificate.lineage_digest.is_some() {
                return RecheckOutcome::Rejected {
                    reason: "discharged-tier certificate unexpectedly carries lineage",
                };
            }
        }
        DischargeStatus::Certified => match (certificate.lineage_digest, evidence_lineage) {
            (Some(c), Some(e)) if c == e => {}
            _ => {
                return RecheckOutcome::Rejected {
                    reason: "certified-tier lineage missing or mismatched on re-check",
                };
            }
        },
    }
    RecheckOutcome::Valid
}

// ---------------------------------------------------------------------------
// GuardSiteLedger — carrier-birth snapshot + conservation.
// ---------------------------------------------------------------------------

/// The lifecycle state of a guard site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GuardState {
    /// Born trapping; not yet resolved. Any site left in this state at codegen is a violation.
    BornTrapping,
    /// Resolved to a real runtime trap (the safe outcome).
    Trapped,
    /// Eliminated under a kernel-issued certificate.
    Eliminated { certificate_id: u128 },
}

/// One snapshotted guard site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GuardSite {
    pub site_id: u64,
    pub kind: GuardKind,
    pub operand_identity: GuardOperandIdentity,
    pub obligation_id: Option<u128>,
    pub state: GuardState,
}

/// Report from a successful conservation check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConservationReport {
    pub emitted: usize,
    pub trapped: usize,
    pub eliminated: usize,
}

/// A conservation violation: either a site was never resolved, or the counts do not add up.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConservationViolation {
    pub function: String,
    pub detail: String,
}

/// Per-function snapshot of guard sites at carrier-birth, used to prove guard-count conservation:
/// `emitted == trapped + eliminated`, with no site left unresolved.
#[derive(Debug, Clone, Default)]
pub struct GuardSiteLedger {
    function: String,
    sites: Vec<GuardSite>,
    next_id: u64,
}

impl GuardSiteLedger {
    pub fn new(function: impl Into<String>) -> Self {
        Self {
            function: function.into(),
            sites: Vec::new(),
            next_id: 0,
        }
    }

    pub fn function(&self) -> &str {
        &self.function
    }

    pub fn sites(&self) -> &[GuardSite] {
        &self.sites
    }

    pub fn is_empty(&self) -> bool {
        self.sites.is_empty()
    }

    pub fn len(&self) -> usize {
        self.sites.len()
    }

    /// Record a carrier at birth (born trapping). Returns the stable site id.
    pub fn record_carrier_birth(
        &mut self,
        kind: GuardKind,
        operand_identity: GuardOperandIdentity,
        obligation_id: Option<u128>,
    ) -> u64 {
        let site_id = self.next_id;
        self.next_id += 1;
        self.sites.push(GuardSite {
            site_id,
            kind,
            operand_identity,
            obligation_id,
            state: GuardState::BornTrapping,
        });
        site_id
    }

    fn site_mut(&mut self, site_id: u64) -> Option<&mut GuardSite> {
        self.sites.iter_mut().find(|s| s.site_id == site_id)
    }

    /// Mark a site as resolved to a real trap. Returns false if the site id is unknown.
    pub fn mark_trapped(&mut self, site_id: u64) -> bool {
        match self.site_mut(site_id) {
            Some(site) => {
                site.state = GuardState::Trapped;
                true
            }
            None => false,
        }
    }

    /// Mark a site as eliminated under a certificate. Returns false if the site id is unknown.
    pub fn mark_eliminated(&mut self, site_id: u64, certificate_id: u128) -> bool {
        match self.site_mut(site_id) {
            Some(site) => {
                site.state = GuardState::Eliminated { certificate_id };
                true
            }
            None => false,
        }
    }

    /// Verify guard-count conservation: every site is resolved (trapped or eliminated) and
    /// `emitted == trapped + eliminated`. Fail-closed: any unresolved site is a violation.
    pub fn verify_conservation(&self) -> Result<ConservationReport, ConservationViolation> {
        let mut trapped = 0usize;
        let mut eliminated = 0usize;
        for site in &self.sites {
            match site.state {
                GuardState::BornTrapping => {
                    return Err(ConservationViolation {
                        function: self.function.clone(),
                        detail: format!(
                            "guard site {} ({:?}) was never resolved (still BornTrapping)",
                            site.site_id, site.kind
                        ),
                    });
                }
                GuardState::Trapped => trapped += 1,
                GuardState::Eliminated { .. } => eliminated += 1,
            }
        }
        let emitted = self.sites.len();
        if emitted != trapped + eliminated {
            return Err(ConservationViolation {
                function: self.function.clone(),
                detail: format!(
                    "guard-count conservation failed: emitted={emitted} != trapped={trapped} + eliminated={eliminated}"
                ),
            });
        }
        Ok(ConservationReport {
            emitted,
            trapped,
            eliminated,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bounds_ops() -> GuardOperandIdentity {
        GuardOperandIdentity::new(vec![
            GuardOperandRef::Reg(10), // base
            GuardOperandRef::Reg(11), // index
            GuardOperandRef::Imm(64), // bound
        ])
    }

    // --- GuardKind <-> ProofAnnotation mapping is total and round-trips. ---

    #[test]
    fn guard_kind_annotation_roundtrip() {
        for (kind, anno) in [
            (GuardKind::BoundsCheck, ProofAnnotation::InBounds),
            (GuardKind::NullPtr, ProofAnnotation::NotNull),
            (GuardKind::DivZero, ProofAnnotation::NonZeroDivisor),
            (GuardKind::ShiftRange, ProofAnnotation::ValidShift),
            (GuardKind::SignedOverflow, ProofAnnotation::NoSignedOverflow),
            (
                GuardKind::UnsignedOverflow,
                ProofAnnotation::NoUnsignedOverflow,
            ),
        ] {
            assert_eq!(kind.matching_proof_annotation(), anno);
            assert_eq!(GuardKind::from_proof_annotation(anno), Some(kind));
            assert!(kind.is_eliminable_by_proof());
        }
        // Legacy NoOverflow folds into SignedOverflow.
        assert_eq!(
            GuardKind::from_proof_annotation(ProofAnnotation::NoOverflow),
            Some(GuardKind::SignedOverflow)
        );
    }

    #[test]
    fn metadata_proofs_have_no_guard_kind() {
        for pa in [
            ProofAnnotation::ValidBorrow,
            ProofAnnotation::PositiveRefCount,
            ProofAnnotation::Pure,
            ProofAnnotation::Associative,
            ProofAnnotation::Commutative,
            ProofAnnotation::Idempotent,
        ] {
            assert_eq!(GuardKind::from_proof_annotation(pa), None);
        }
    }

    // --- Operand fingerprint is reproducible and discriminating. ---

    #[test]
    fn operand_fingerprint_is_reproducible_and_discriminating() {
        let a = bounds_ops();
        assert!(a.is_consistent());
        assert_eq!(a.fingerprint, fingerprint_operands(&a.operands));

        let b = GuardOperandIdentity::new(vec![
            GuardOperandRef::Reg(10),
            GuardOperandRef::Reg(99), // different index
            GuardOperandRef::Imm(64),
        ]);
        assert_ne!(a.fingerprint, b.fingerprint);
    }

    // --- Item B (defense-in-depth): the carrier->obligation binding key folds in GuardKind, so
    // two single-operand carriers of DIFFERENT kinds over the SAME vreg get DISTINCT keys. ---

    /// The exact collision Item B closes: a `NullPtr [Reg(5)]` and a `DivZero [Reg(5)]` produce the
    /// SAME kind-agnostic operand fingerprint but DISTINCT `fingerprint_for_kind` binding keys.
    #[test]
    fn fingerprint_for_kind_distinguishes_same_operands_under_different_kinds() {
        let ops = [GuardOperandRef::Reg(5)];

        // Layer (1) — the legacy operand-only fingerprint COLLIDES (this is the gap).
        assert_eq!(
            fingerprint_operands(&ops),
            fingerprint_operands(&ops),
            "operand fingerprint is kind-agnostic by design"
        );

        // Layer (1') — the kind-folded binding key SEPARATES them.
        let null_key = fingerprint_for_kind(GuardKind::NullPtr, &ops);
        let div_key = fingerprint_for_kind(GuardKind::DivZero, &ops);
        assert_ne!(
            null_key, div_key,
            "different kinds over identical operands must key DISTINCT obligations"
        );

        // It is also distinct from the bare operand fingerprint (different domain tag), so a stray
        // operand-only key can never alias a kind-folded one.
        assert_ne!(null_key, fingerprint_operands(&ops));
        assert_ne!(div_key, fingerprint_operands(&ops));

        // Reproducible.
        assert_eq!(null_key, fingerprint_for_kind(GuardKind::NullPtr, &ops));
        assert_eq!(div_key, fingerprint_for_kind(GuardKind::DivZero, &ops));

        // Every kind over the same single operand gets a UNIQUE key (no accidental aliasing).
        let keys = [
            fingerprint_for_kind(GuardKind::BoundsCheck, &ops),
            fingerprint_for_kind(GuardKind::NullPtr, &ops),
            fingerprint_for_kind(GuardKind::DivZero, &ops),
            fingerprint_for_kind(GuardKind::ShiftRange, &ops),
            fingerprint_for_kind(GuardKind::SignedOverflow, &ops),
            fingerprint_for_kind(GuardKind::UnsignedOverflow, &ops),
        ];
        for i in 0..keys.len() {
            for j in (i + 1)..keys.len() {
                assert_ne!(keys[i], keys[j], "kinds {i} and {j} must not alias");
            }
        }
    }

    /// End-to-end binding semantics (the soundness claim): with the per-function carrier->obligation
    /// map keyed by `fingerprint_for_kind`, a discharged NullPtr obligation eliminates ONLY the
    /// NullPtr carrier, and a discharged DivZero obligation eliminates ONLY the DivZero carrier —
    /// even though both carriers are over the SAME vreg. A cross-kind lookup MISSES => carrier KEPT
    /// (fail-safe; no over-elimination). This models exactly what every backend gate does.
    #[test]
    fn kind_folded_binding_eliminates_only_matching_kind() {
        use std::collections::HashMap;

        let ops = [GuardOperandRef::Reg(5)];

        // Two genuinely-discharged obligations, one per kind.
        let null_obl: u128 = 0x1111;
        let div_obl: u128 = 0x2222;
        let mut evidence = DischargedEvidenceTable::new();
        evidence.insert(null_obl, DischargeStatus::Discharged, None);
        evidence.insert(div_obl, DischargeStatus::Discharged, None);

        // The per-function binding map ISel records: each carrier keyed by its kind-folded key.
        let mut guard_obligations: HashMap<u128, u128> = HashMap::new();
        guard_obligations.insert(fingerprint_for_kind(GuardKind::NullPtr, &ops), null_obl);
        guard_obligations.insert(fingerprint_for_kind(GuardKind::DivZero, &ops), div_obl);
        // No last-writer-wins collision: both bindings coexist.
        assert_eq!(guard_obligations.len(), 2);

        // The kernel re-derives the SAME key from the live carrier's kind+operands, looks up the
        // obligation, and decides. Model that for each carrier kind.
        let authorize = |kind: GuardKind| -> EliminationVerdict {
            let key = fingerprint_for_kind(kind, &ops);
            let obl = guard_obligations.get(&key).copied();
            let receipt = GuardObligationReceipt {
                kind,
                operand_identity: GuardOperandIdentity::new(ops.to_vec()),
                proof_obligation_id: obl,
                lineage_digest: None,
            };
            decide(&receipt, &evidence)
        };

        // NullPtr carrier eliminated by the NullPtr obligation.
        let null_verdict = authorize(GuardKind::NullPtr);
        let null_cert = null_verdict.certificate().expect("NullPtr eliminated");
        assert_eq!(null_cert.guard_kind(), GuardKind::NullPtr);
        assert_eq!(null_cert.obligation_id(), null_obl);

        // DivZero carrier eliminated by the DivZero obligation (NOT the NullPtr one).
        let div_verdict = authorize(GuardKind::DivZero);
        let div_cert = div_verdict.certificate().expect("DivZero eliminated");
        assert_eq!(div_cert.guard_kind(), GuardKind::DivZero);
        assert_eq!(div_cert.obligation_id(), div_obl);

        // SOUNDNESS: a carrier kind with NO bound obligation (e.g. ShiftRange over the same vreg)
        // misses the lookup and is KEPT — the discharged Null/Div obligations cannot leak to it.
        let shift_verdict = authorize(GuardKind::ShiftRange);
        assert!(
            !shift_verdict.is_eliminate(),
            "an unbound kind over the same operand must be KEPT (no cross-kind over-elimination)"
        );
    }

    // --- Kernel fail-safe defaults (S0: empty evidence => never eliminate). ---

    #[test]
    fn decide_keeps_unbound_receipt() {
        let evidence = DischargedEvidenceTable::new();
        let receipt = GuardObligationReceipt::unbound(GuardKind::BoundsCheck, bounds_ops());
        assert!(!decide(&receipt, &evidence).is_eliminate());
    }

    #[test]
    fn decide_keeps_when_obligation_absent_from_evidence() {
        let evidence = DischargedEvidenceTable::new();
        let receipt = GuardObligationReceipt {
            kind: GuardKind::NullPtr,
            operand_identity: GuardOperandIdentity::new(vec![GuardOperandRef::Reg(3)]),
            proof_obligation_id: Some(0xABCD),
            lineage_digest: None,
        };
        assert!(!decide(&receipt, &evidence).is_eliminate());
    }

    #[test]
    fn decide_keeps_empty_operands() {
        let evidence = DischargedEvidenceTable::new();
        let receipt = GuardObligationReceipt {
            kind: GuardKind::BoundsCheck,
            operand_identity: GuardOperandIdentity::new(vec![]),
            proof_obligation_id: Some(1),
            lineage_digest: None,
        };
        assert!(!decide(&receipt, &evidence).is_eliminate());
    }

    // --- Kernel eliminate path (Discharged tier). ---

    #[test]
    fn decide_eliminates_discharged() {
        let mut evidence = DischargedEvidenceTable::new();
        evidence.insert(42, DischargeStatus::Discharged, None);
        let ops = bounds_ops();
        let receipt = GuardObligationReceipt {
            kind: GuardKind::BoundsCheck,
            operand_identity: ops.clone(),
            proof_obligation_id: Some(42),
            lineage_digest: None,
        };
        let verdict = decide(&receipt, &evidence);
        let cert = verdict.certificate().expect("should eliminate");
        assert_eq!(cert.guard_kind(), GuardKind::BoundsCheck);
        assert_eq!(cert.operand_fingerprint(), ops.fingerprint);
        assert_eq!(cert.obligation_id(), 42);
        assert_eq!(cert.discharge_status(), DischargeStatus::Discharged);
        assert_eq!(cert.lineage_digest(), None);
        assert!(cert.is_internally_consistent());
    }

    // --- Kernel eliminate path (Certified tier) + lineage gating. ---

    #[test]
    fn decide_certified_requires_matching_lineage() {
        let mut evidence = DischargedEvidenceTable::new();
        evidence.insert(7, DischargeStatus::Certified, Some(0xABCDEF_u128));
        let ops = GuardOperandIdentity::new(vec![GuardOperandRef::Reg(5)]);

        // Missing lineage on the receipt => Keep.
        let no_lineage = GuardObligationReceipt {
            kind: GuardKind::NullPtr,
            operand_identity: ops.clone(),
            proof_obligation_id: Some(7),
            lineage_digest: None,
        };
        assert!(!decide(&no_lineage, &evidence).is_eliminate());

        // Wrong lineage => Keep.
        let wrong_lineage = GuardObligationReceipt {
            kind: GuardKind::NullPtr,
            operand_identity: ops.clone(),
            proof_obligation_id: Some(7),
            lineage_digest: Some(0xBAD),
        };
        assert!(!decide(&wrong_lineage, &evidence).is_eliminate());

        // Matching lineage => Eliminate, carrying the lineage.
        let ok = GuardObligationReceipt {
            kind: GuardKind::NullPtr,
            operand_identity: ops,
            proof_obligation_id: Some(7),
            lineage_digest: Some(0xABCDEF_u128),
        };
        let cert = decide(&ok, &evidence)
            .certificate()
            .cloned()
            .expect("eliminate");
        assert_eq!(cert.discharge_status(), DischargeStatus::Certified);
        assert_eq!(cert.lineage_digest(), Some(0xABCDEF_u128));
    }

    // --- Independent re-check (the S4 "different path"). ---

    #[test]
    fn recheck_accepts_matching_and_rejects_drift() {
        let mut evidence = DischargedEvidenceTable::new();
        evidence.insert(42, DischargeStatus::Discharged, None);
        let ops = bounds_ops();
        let receipt = GuardObligationReceipt {
            kind: GuardKind::BoundsCheck,
            operand_identity: ops.clone(),
            proof_obligation_id: Some(42),
            lineage_digest: None,
        };
        let cert = decide(&receipt, &evidence).certificate().cloned().unwrap();

        // Same operands + same evidence => Valid.
        assert_eq!(
            recheck_elimination(&cert, &ops.operands, &evidence),
            RecheckOutcome::Valid
        );

        // Drifted operands => Rejected (operand-binding soundness).
        let drifted = vec![
            GuardOperandRef::Reg(10),
            GuardOperandRef::Reg(999),
            GuardOperandRef::Imm(64),
        ];
        assert!(matches!(
            recheck_elimination(&cert, &drifted, &evidence),
            RecheckOutcome::Rejected { .. }
        ));

        // Evidence retracted => Rejected.
        let empty = DischargedEvidenceTable::new();
        assert!(matches!(
            recheck_elimination(&cert, &ops.operands, &empty),
            RecheckOutcome::Rejected { .. }
        ));
    }

    // --- Conservation. ---

    #[test]
    fn conservation_ok_when_all_resolved() {
        let mut ledger = GuardSiteLedger::new("f");
        let s0 = ledger.record_carrier_birth(GuardKind::BoundsCheck, bounds_ops(), None);
        let s1 = ledger.record_carrier_birth(
            GuardKind::NullPtr,
            GuardOperandIdentity::new(vec![GuardOperandRef::Reg(1)]),
            Some(9),
        );
        assert!(ledger.mark_trapped(s0));
        assert!(ledger.mark_eliminated(s1, 0xC0FFEE));
        let report = ledger.verify_conservation().expect("conserved");
        assert_eq!(report.emitted, 2);
        assert_eq!(report.trapped, 1);
        assert_eq!(report.eliminated, 1);
    }

    #[test]
    fn conservation_fails_on_unresolved_site() {
        let mut ledger = GuardSiteLedger::new("f");
        ledger.record_carrier_birth(GuardKind::BoundsCheck, bounds_ops(), None);
        assert!(ledger.verify_conservation().is_err());
    }

    #[test]
    fn marking_unknown_site_is_rejected() {
        let mut ledger = GuardSiteLedger::new("f");
        assert!(!ledger.mark_trapped(123));
        assert!(!ledger.mark_eliminated(123, 1));
    }

    // =======================================================================================
    // DIFFERENTIAL BRIDGE: decide() / recheck_elimination() vs. the Clean Lean model.
    //
    // This welds the real Rust kernel to the machine-checked Lean model
    // `proofs/sentinel_decide_spec.lean` (cekDecide:115-138, cekRecheck:479-483, verified
    // 75/75). It EXHAUSTIVELY enumerates the FINITE abstract gate domain that the Lean model
    // abstracts and, for every point, asserts the REAL decide() agrees with an INDEPENDENT
    // oracle re-encoding of the Lean 5-gate decision table.
    //
    // The Lean model is proven sound (Clean). This test proves real decide() == model over
    // the whole finite domain. Composing the two: real decide() is sound over that domain.
    //
    // FAITHFULNESS: the oracle below (`oracle_eliminate`) is written FROM the Lean cekDecide
    // 5-gate nested match (spec:115-138), NOT from decide()'s branch structure or reason
    // strings. It shares NO helper with decide(). If the two ever disagree on any point, the
    // test fails and that is a genuine finding — we do NOT bend the oracle to match decide().
    //
    // ABSTRACT DOMAIN (the same finite gate domain the Lean model abstracts):
    //   GuardKind                 : 6 variants                 (Lean GKind, spec:232-238)
    //   eliminable                : derived from kind          (Lean Flag; is_eliminable_by_proof)
    //   operands                  : {empty, nonempty}          (Lean opsNonempty Flag, gate 2)
    //   fingerprint consistency   : {consistent, inconsistent} (Lean consistent Flag, gate 3)
    //   obligation presence       : {None, Some}               (Lean ObRef, gate 4a)
    //   evidence tier (at lookup) : {NotInTable, Discharged,
    //                                Certified+Some, Certified+None} (Lean Evid, gate 4b/5)
    //   receipt lineage           : {None, Match, Mismatch}    (Lean LinRef + digestCmp, gate 5)
    //
    // BOUNDED / NON-FINITE DIMENSIONS (stated explicitly):
    //   * u128 obligation ids, lineage digests, and operand fingerprints are OPEN, but decide()
    //     and recheck() use them ONLY via equality / table-presence (verified by reading the
    //     code: id only for evidence.lookup + cert equality; lineage only via ==; fingerprint
    //     only via ==). So ONE representative id (OBLIG_ID), ONE evidence digest (EV_DIGEST)
    //     with a matching and a non-matching receipt digest, and ONE nonempty operand list
    //     fully exercise every gate DECISION. The u128 axes are closed at the equality/presence
    //     level only — this is the explicit bound.
    //   * Gate 1 (kind not eliminable) is UNREACHABLE: is_eliminable_by_proof() is true for all
    //     6 kinds (matching Lean gkindEliminable=yes for all 6). The Lean model abstracts gate 1
    //     as a free Flag that CAN be no; the Rust type cannot produce a non-eliminable kind. We
    //     therefore (a) assert is_eliminable_by_proof()==true for all 6 kinds, and (b) feed the
    //     oracle eliminable=true for every real point. The decide()/recheck gate-1 Keep/Reject
    //     branch is a documented dead branch over the real type domain.
    //   * DischargeStatus has only {Discharged, Certified} — there is NO Pending/Failed variant.
    //     The task's tier {absent, Pending, Failed, Discharged, Certified} maps onto the real
    //     domain as: absent = obligation None OR id not in evidence table; Pending/Failed are
    //     NOT representable and collapse to NotInTable (the evidence table only ever holds
    //     discharged-or-better entries). This matches the Lean Evid.absent comment
    //     ("Pending/Failed/missing"). We do not fabricate Pending/Failed states.
    //   * Certified-with-evidence-lineage-None is a REAL input the Lean model omits (Lean
    //     Evid.certified always carries a Digest). Its oracle verdict is Keep (the `_` arm at
    //     decide guard.rs:581). We enumerate it as a real point; the oracle returns Keep for it.
    // =======================================================================================

    /// Fixed representative obligation id (u128 axis closed at presence/equality only).
    const OBLIG_ID: u128 = 42;
    /// Fixed representative evidence-side lineage digest (Certified tier).
    const EV_DIGEST: u128 = 0x00AB_CDEF;
    /// A receipt-side lineage digest that does NOT equal `EV_DIGEST`.
    const BAD_DIGEST: u128 = 0x00BA_D000;

    /// Abstract evidence tier at the obligation-lookup point (mirrors Lean `Evid`, plus the
    /// real-domain-only Certified-with-no-evidence-lineage leaf the Lean model omits).
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Tier {
        /// Obligation absent from the evidence table (= Lean Evid.absent; also Pending/Failed).
        NotInTable,
        /// In table as Discharged (= Lean Evid.discharged).
        Discharged,
        /// In table as Certified carrying the evidence lineage digest (= Lean Evid.certified l).
        CertifiedWithLineage,
        /// In table as Certified but with evidence lineage None — real input the model omits.
        CertifiedNoLineage,
    }

    /// Abstract receipt-side lineage state (mirrors Lean `LinRef` + `digestCmp` against EV_DIGEST).
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum LineageState {
        /// receipt.lineage_digest == None  (= Lean LinRef.noLineage).
        None,
        /// receipt.lineage_digest == Some(EV_DIGEST) (= Lean LinRef.lineage with digestCmp eq).
        Match,
        /// receipt.lineage_digest == Some(BAD_DIGEST) (= Lean LinRef.lineage with digestCmp ne).
        Mismatch,
    }

    /// INDEPENDENT ORACLE — a direct re-encoding of the Lean `cekDecide` 5-gate nested match
    /// (proofs/sentinel_decide_spec.lean:115-138). It returns `true` iff the model says
    /// Eliminate. Written from the spec, NOT from decide(): same gate order, Keep-default at
    /// every gate, and the Certified leaf comparing receipt vs. evidence lineage by equality.
    ///
    /// `eliminable` corresponds to the Lean leading `Flag` (always true for real kinds, see
    /// the dead-branch note above). The remaining axes mirror opsNonempty / consistent /
    /// obligation-presence / Evid / LinRef exactly.
    fn oracle_eliminate(
        eliminable: bool,
        ops_nonempty: bool,
        consistent: bool,
        oblig_present: bool,
        tier: Tier,
        recv_lineage: LineageState,
    ) -> bool {
        // Gate 1 (Lean: match eliminable | no => keep).
        if !eliminable {
            return false;
        }
        // Gate 2 (Lean: match opsNonempty | no => keep).
        if !ops_nonempty {
            return false;
        }
        // Gate 3 (Lean: match consistent | no => keep).
        if !consistent {
            return false;
        }
        // Gate 4a (Lean: match oblig | noObligation => keep).
        if !oblig_present {
            return false;
        }
        // Gate 4b + Gate 5 (Lean: match lookup id | absent => keep
        //                                          | discharged => eliminate
        //                                          | certified l => match recLineage ...).
        match tier {
            Tier::NotInTable => false,
            Tier::Discharged => true,
            // Lean Evid.certified l => match recLineage:
            //   noLineage => keep;  lineage r => digestCmp r l (eq => eliminate, ne => keep).
            // The model's Evid.certified ALWAYS carries a digest, so CertifiedWithLineage is the
            // modeled leaf; the comparison succeeds iff the receipt claims the matching digest.
            Tier::CertifiedWithLineage => matches!(recv_lineage, LineageState::Match),
            // Real-domain-only leaf the Lean model omits: evidence lineage is None, so even a
            // matching-looking receipt cannot satisfy "both Some and equal" => Keep.
            Tier::CertifiedNoLineage => false,
        }
    }

    /// Build the real `DischargedEvidenceTable` for an abstract tier (inserting at OBLIG_ID).
    fn build_evidence(tier: Tier) -> DischargedEvidenceTable {
        let mut ev = DischargedEvidenceTable::new();
        match tier {
            Tier::NotInTable => {} // leave empty: lookup(OBLIG_ID) => None
            Tier::Discharged => ev.insert(OBLIG_ID, DischargeStatus::Discharged, None),
            Tier::CertifiedWithLineage => {
                ev.insert(OBLIG_ID, DischargeStatus::Certified, Some(EV_DIGEST))
            }
            Tier::CertifiedNoLineage => ev.insert(OBLIG_ID, DischargeStatus::Certified, None),
        }
        ev
    }

    /// Build the real receipt for an abstract point. `ops_nonempty` / `consistent` shape the
    /// operand identity; gate-3 inconsistency is forced by overwriting the (pub) fingerprint
    /// field with a wrong value (is_consistent() recomputes from operands, guard.rs:244-246).
    fn build_receipt(
        kind: GuardKind,
        ops_nonempty: bool,
        consistent: bool,
        oblig_present: bool,
        recv_lineage: LineageState,
    ) -> GuardObligationReceipt {
        let raw_ops = if ops_nonempty {
            vec![
                GuardOperandRef::Reg(10),
                GuardOperandRef::Reg(11),
                GuardOperandRef::Imm(64),
            ]
        } else {
            vec![]
        };
        let mut operand_identity = GuardOperandIdentity::new(raw_ops);
        if !consistent {
            // Force gate-3 inconsistency: corrupt the cached fingerprint so is_consistent()
            // (which recomputes from operands) returns false. Only public-API way to hit gate 3.
            operand_identity.fingerprint ^= 1;
        }
        let lineage_digest = match recv_lineage {
            LineageState::None => None,
            LineageState::Match => Some(EV_DIGEST),
            LineageState::Mismatch => Some(BAD_DIGEST),
        };
        GuardObligationReceipt {
            kind,
            operand_identity,
            proof_obligation_id: if oblig_present { Some(OBLIG_ID) } else { None },
            lineage_digest,
        }
    }

    const ALL_KINDS: [GuardKind; 6] = [
        GuardKind::BoundsCheck,
        GuardKind::NullPtr,
        GuardKind::DivZero,
        GuardKind::ShiftRange,
        GuardKind::SignedOverflow,
        GuardKind::UnsignedOverflow,
    ];
    const ALL_TIERS: [Tier; 4] = [
        Tier::NotInTable,
        Tier::Discharged,
        Tier::CertifiedWithLineage,
        Tier::CertifiedNoLineage,
    ];
    const ALL_LINEAGE: [LineageState; 3] = [
        LineageState::None,
        LineageState::Match,
        LineageState::Mismatch,
    ];

    /// EXHAUSTIVE differential enumeration of decide() over the finite abstract gate domain,
    /// asserting agreement with the independent Lean-model oracle at EVERY point.
    ///
    /// Domain size: kind(6) x ops{empty,nonempty}(2) x consistent{yes,no}(2)
    ///            x oblig{None,Some}(2) x tier(4) x receipt-lineage(3) = 6*2*2*2*4*3 = 1152.
    #[test]
    fn decide_agrees_with_lean_model_over_full_finite_domain() {
        // Gate-1 closure check: the model's eliminable Flag is always yes for real kinds, so we
        // feed the oracle eliminable=true everywhere. Document the dead Keep-on-gate-1 branch.
        for k in ALL_KINDS {
            assert!(
                k.is_eliminable_by_proof(),
                "gate-1 is closed: every real GuardKind must be eliminable (model gkindEliminable=yes)"
            );
        }

        let mut enumerated: u64 = 0;
        let mut disagreements: Vec<String> = Vec::new();

        for kind in ALL_KINDS {
            for &ops_nonempty in &[false, true] {
                for &consistent in &[false, true] {
                    for &oblig_present in &[false, true] {
                        for tier in ALL_TIERS {
                            for recv_lineage in ALL_LINEAGE {
                                enumerated += 1;

                                let evidence = build_evidence(tier);
                                let receipt = build_receipt(
                                    kind,
                                    ops_nonempty,
                                    consistent,
                                    oblig_present,
                                    recv_lineage,
                                );

                                // (b) call the REAL decide().
                                let verdict = decide(&receipt, &evidence);
                                let real_eliminate = verdict.is_eliminate();

                                // (c) compute the EXPECTED verdict from the model oracle
                                //     (eliminable always true for real kinds — gate 1 closed).
                                let model_eliminate = oracle_eliminate(
                                    true,
                                    ops_nonempty,
                                    consistent,
                                    oblig_present,
                                    tier,
                                    recv_lineage,
                                );

                                // (d) assert AGREEMENT; collect any disagreement w/ coordinates.
                                if real_eliminate != model_eliminate {
                                    disagreements.push(format!(
                                        "DISAGREEMENT @ kind={kind:?} ops_nonempty={ops_nonempty} \
                                         consistent={consistent} oblig_present={oblig_present} \
                                         tier={tier:?} recv_lineage={recv_lineage:?}: \
                                         decide()={real_eliminate} model={model_eliminate}"
                                    ));
                                    continue;
                                }

                                // When eliminating, the minted certificate must faithfully bind
                                // the modeled coordinates (kind / obligation / tier / lineage).
                                if real_eliminate {
                                    let cert = verdict
                                        .certificate()
                                        .expect("Eliminate must carry a certificate");
                                    assert_eq!(cert.guard_kind(), kind);
                                    assert_eq!(cert.obligation_id(), OBLIG_ID);
                                    assert_eq!(
                                        cert.operand_fingerprint(),
                                        receipt.operand_identity.fingerprint
                                    );
                                    assert!(cert.is_internally_consistent());
                                    match tier {
                                        Tier::Discharged => {
                                            assert_eq!(
                                                cert.discharge_status(),
                                                DischargeStatus::Discharged
                                            );
                                            // Lean: discharged leaf carries no lineage.
                                            assert_eq!(cert.lineage_digest(), None);
                                        }
                                        Tier::CertifiedWithLineage => {
                                            assert_eq!(
                                                cert.discharge_status(),
                                                DischargeStatus::Certified
                                            );
                                            assert_eq!(cert.lineage_digest(), Some(EV_DIGEST));
                                        }
                                        // The only two tiers that can Eliminate.
                                        Tier::NotInTable | Tier::CertifiedNoLineage => {
                                            panic!("tier {tier:?} must never Eliminate");
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        assert!(
            disagreements.is_empty(),
            "decide() diverged from the Lean model on {} of {} points:\n{}",
            disagreements.len(),
            enumerated,
            disagreements.join("\n")
        );
        // Whole finite gate domain enumerated.
        assert_eq!(
            enumerated,
            6 * 2 * 2 * 2 * 4 * 3,
            "must enumerate the full domain"
        );
    }

    /// RECHECK differential bridge — scoped to the property the Lean model actually covers:
    /// `cekRecheck` (spec:479-483) abstracts recheck to "accept iff decide would Eliminate"
    /// (cekRecheck_iff_cekDecide, spec:519-525), and EXPLICITLY does NOT model the certificate
    /// validation hash nor the FNV operand re-derivation (LIMITATION notes spec:59-61, :468-470).
    ///
    /// recheck consumes a CERTIFICATE, which only decide() mints, so there is no certificate to
    /// recheck when decide Keeps; the model's "reject when decide keeps" is vacuous on the real
    /// API. We therefore enumerate every domain point where the MODEL says Eliminate, mint the
    /// REAL certificate via decide(), and assert recheck on the EXACT minting operands+evidence
    /// returns Valid (== model accept). This is the model-faithful direction.
    ///
    /// We ALSO assert the Rust-STRICTER superset axes (operand drift / empty observed operands /
    /// evidence retraction) Reject — but those are Rust soundness features OUTSIDE the model's
    /// scope, so they are asserted on their own (not against the model oracle), exactly as the
    /// spec's limitation notes prescribe.
    ///
    /// Coverage bound: a real decide-minted certificate is always internally consistent and of
    /// an eliminable kind, so recheck's cert-corruption reject branches (guard.rs:617, :622) are
    /// UNREACHABLE without unsafe private-field mutation — a documented, bounded coverage gap
    /// that matches the Lean model's own stated limitation.
    #[test]
    fn recheck_agrees_with_lean_model_on_minted_certificates() {
        let mut minted = 0u64;
        let mut valid_agreements = 0u64;
        let mut reject_drift = 0u64;

        let drifted_ops = vec![
            GuardOperandRef::Reg(10),
            GuardOperandRef::Reg(999), // drifted
            GuardOperandRef::Imm(64),
        ];

        for kind in ALL_KINDS {
            for tier in ALL_TIERS {
                for recv_lineage in ALL_LINEAGE {
                    // Use the eliminate-capable configuration (ops nonempty + consistent +
                    // obligation present); the decide-side agreement is proven exhaustively in
                    // the test above, so here we focus on the recheck verdict.
                    let model_eliminate =
                        oracle_eliminate(true, true, true, true, tier, recv_lineage);
                    if !model_eliminate {
                        continue;
                    }

                    let evidence = build_evidence(tier);
                    let receipt = build_receipt(kind, true, true, true, recv_lineage);
                    let verdict = decide(&receipt, &evidence);
                    let cert = verdict
                        .certificate()
                        .cloned()
                        .expect("model says Eliminate => decide must mint a cert");
                    minted += 1;

                    // MODEL-FAITHFUL DIRECTION: recheck on the EXACT minting operands+evidence
                    // must be Valid (== cekRecheck accept, since decide would Eliminate).
                    assert_eq!(
                        recheck_elimination(&cert, &receipt.operand_identity.operands, &evidence),
                        RecheckOutcome::Valid,
                        "recheck must accept the exact elimination decide just minted \
                         (kind={kind:?} tier={tier:?} recv_lineage={recv_lineage:?})"
                    );
                    valid_agreements += 1;

                    // RUST-STRICTER SUPERSET (outside the Lean model's scope):
                    // operand drift => Reject.
                    assert!(
                        matches!(
                            recheck_elimination(&cert, &drifted_ops, &evidence),
                            RecheckOutcome::Rejected { .. }
                        ),
                        "operand drift must be rejected (kind={kind:?} tier={tier:?})"
                    );
                    // empty observed operands => Reject.
                    assert!(
                        matches!(
                            recheck_elimination(&cert, &[], &evidence),
                            RecheckOutcome::Rejected { .. }
                        ),
                        "empty observed operands must be rejected (kind={kind:?} tier={tier:?})"
                    );
                    // evidence retracted => Reject.
                    assert!(
                        matches!(
                            recheck_elimination(
                                &cert,
                                &receipt.operand_identity.operands,
                                &DischargedEvidenceTable::new()
                            ),
                            RecheckOutcome::Rejected { .. }
                        ),
                        "evidence retraction must be rejected (kind={kind:?} tier={tier:?})"
                    );
                    reject_drift += 1;
                }
            }
        }

        // Every eliminable tier (Discharged, Certified+matching-lineage) over all 6 kinds is
        // minted and rechecked: 6 kinds * (Discharged{any lineage} + Certified+Match) points.
        // Discharged eliminates for all 3 lineage states; Certified only for Match => 6*(3+1)=24.
        assert_eq!(minted, 24, "expected 24 eliminable minted certificates");
        assert_eq!(
            valid_agreements, minted,
            "every minted cert must recheck Valid on its own inputs"
        );
        assert_eq!(
            reject_drift, minted,
            "every minted cert must reject drift/empty/retraction"
        );
    }

    // =======================================================================================
    // OPERAND-DRIFT WELD: real fingerprint_operands <-> Lean fnvFingerprint / cekRecheckWithDrift.
    //
    // This welds the REAL FNV operand fingerprint (`fingerprint_operands`, guard.rs:250-267) and
    // the REAL re-checker drift gate (`recheck_elimination`'s fingerprint re-derivation,
    // guard.rs:633) to the machine-checked Lean operand-drift model in §IV of
    // proofs/sentinel_decide_spec.lean:
    //
    //   * fnvFingerprint : Operands -> Fp                 (Lean spec §IV)
    //   * fpCmp : Fp -> Fp -> Cmp                          (Lean spec §IV)
    //   * cekRecheckWithDrift (fpMatch) ...                (Lean spec §IV): Reject on Cmp.ne,
    //                                                       else delegate to the §III verdict logic.
    //   * cekRecheck_rejects_on_fingerprint_mismatch       (Lean SAFETY, axiom-free).
    //   * drift_detected (under CollisionResistant)        (Lean COMPLETENESS, hypothesis-scoped).
    //
    // The Lean model proves: re-derived-fp != cert-fp  =>  Reject (safety), and (under collision
    // resistance) observed-operands != minted-operands => Reject (completeness). Here we INSTANTIATE
    // that decision on REAL operand lists + REAL fingerprints and assert the REAL recheck agrees
    // with the Lean `cekRecheckWithDrift` decision EXACTLY, point by point:
    //
    //   - SAME operands  => fingerprint_operands matches the certificate => recheck Valid
    //                       (Lean: fpCmp = eq => delegate => the §III verdict, which is accept here).
    //   - DRIFTED operands (any single-axis perturbation) => fingerprint_operands differs =>
    //                       recheck Rejected (Lean: fpCmp = ne => cekRecheckWithDrift = Reject).
    //
    // The drift-gate oracle below is re-encoded straight from the Lean §IV `cekRecheckWithDrift`
    // (compare re-derived fp to cert fp; Reject on mismatch, else delegate). It shares NO helper
    // with `recheck_elimination`. The fingerprints are computed by the REAL `fingerprint_operands`,
    // so this also discharges, over the enumerated finite operand domain, the concrete instance of
    // the Lean `CollisionResistant` hypothesis: every enumerated DRIFT actually changes the real FNV
    // fingerprint (no collision among the tested points) — the empirical footing under the proof's
    // stated assumption.
    // =======================================================================================

    /// INDEPENDENT drift-gate oracle — a direct re-encoding of Lean §IV `cekRecheckWithDrift`:
    /// the re-checker re-derives the operand fingerprint and compares it to the certificate's; on
    /// mismatch it Rejects (safety), otherwise it delegates to the verdict logic. Returns `true`
    /// iff the model says the drift gate PASSES (fingerprints match) for this observed/cert pair.
    fn drift_gate_passes(observed_fp: u128, cert_fp: u128) -> bool {
        // Lean: match fpCmp observedFp certFp | Cmp.ne => reject ; Cmp.eq => delegate.
        observed_fp == cert_fp
    }

    /// The real operand configurations we weld the model against: distinct guard operand shapes,
    /// each exercising regs and immediates the way real carriers do.
    fn drift_base_configs() -> Vec<Vec<GuardOperandRef>> {
        vec![
            vec![
                GuardOperandRef::Reg(10),
                GuardOperandRef::Reg(11),
                GuardOperandRef::Imm(64),
            ],
            vec![GuardOperandRef::Reg(3)],
            vec![GuardOperandRef::Imm(0)],
            vec![GuardOperandRef::Reg(7), GuardOperandRef::Imm(-1)],
            vec![
                GuardOperandRef::Imm(64),
                GuardOperandRef::Reg(10),
                GuardOperandRef::Reg(11),
            ],
        ]
    }

    /// Enumerate single-axis DRIFTED variants of a base operand list — each a realistic operand
    /// drift: change a reg id, change an imm value, flip reg<->imm (tag drift), drop the last
    /// operand, append an operand, reorder. Every variant is a genuinely DIFFERENT operand list.
    fn drift_variants(base: &[GuardOperandRef]) -> Vec<Vec<GuardOperandRef>> {
        let mut out: Vec<Vec<GuardOperandRef>> = Vec::new();

        // Per-position perturbations.
        for i in 0..base.len() {
            // Change this operand to a different reg.
            let mut v = base.to_vec();
            v[i] = GuardOperandRef::Reg(0xDEAD);
            out.push(v);
            // Change this operand to a different imm (tag flip if it was a reg).
            let mut v = base.to_vec();
            v[i] = GuardOperandRef::Imm(0x7FFF);
            out.push(v);
        }

        // Drop the last operand (length drift) — but never produce empty (empty is a separate gate).
        if base.len() > 1 {
            out.push(base[..base.len() - 1].to_vec());
        }

        // Append an operand (length drift).
        let mut appended = base.to_vec();
        appended.push(GuardOperandRef::Reg(424242));
        out.push(appended);

        // Reorder the first two operands when they differ (order is role-significant).
        if base.len() >= 2 && base[0] != base[1] {
            let mut v = base.to_vec();
            v.swap(0, 1);
            out.push(v);
        }

        out
    }

    /// REAL recheck vs Lean cekRecheckWithDrift over real operands + real FNV fingerprints.
    ///
    /// For each base operand config: mint a real Discharged certificate (so the §III verdict path
    /// would Accept), then assert the REAL `recheck_elimination` agrees with the Lean drift-gate
    /// decision at EVERY observed-operand point — Valid on the exact minting operands, Rejected on
    /// every drift variant — and that the agreement is driven by the REAL `fingerprint_operands`.
    #[test]
    fn recheck_welds_real_fingerprint_to_lean_drift_model() {
        let mut evidence = DischargedEvidenceTable::new();
        evidence.insert(OBLIG_ID, DischargeStatus::Discharged, None);

        let mut checked_valid = 0u64;
        let mut checked_reject = 0u64;

        for base in drift_base_configs() {
            // Mint a real certificate over the base operands (Discharged => §III would Accept).
            let ops_identity = GuardOperandIdentity::new(base.clone());
            let cert_fp = ops_identity.fingerprint;
            // Sanity: the cached fingerprint IS the real FNV of the operands.
            assert_eq!(cert_fp, fingerprint_operands(&base));

            let receipt = GuardObligationReceipt {
                kind: GuardKind::BoundsCheck,
                operand_identity: ops_identity,
                proof_obligation_id: Some(OBLIG_ID),
                lineage_digest: None,
            };
            let cert = decide(&receipt, &evidence)
                .certificate()
                .cloned()
                .expect("discharged obligation must mint a certificate");
            assert_eq!(cert.operand_fingerprint(), cert_fp);

            // ---- SAME operands: real fp matches => Lean drift gate passes => recheck Valid. ----
            let observed_fp = fingerprint_operands(&base);
            assert!(
                drift_gate_passes(observed_fp, cert.operand_fingerprint()),
                "model drift gate must pass on identical operands (base={base:?})"
            );
            assert_eq!(
                recheck_elimination(&cert, &base, &evidence),
                RecheckOutcome::Valid,
                "real recheck must be Valid when the model drift gate passes (base={base:?})"
            );
            checked_valid += 1;

            // ---- DRIFTED operands: real fp differs => Lean drift gate fails => recheck Rejected. ----
            for variant in drift_variants(&base) {
                // The variant must be a genuinely different operand list (real drift).
                assert_ne!(
                    variant, base,
                    "drift variant must differ from base (base={base:?})"
                );

                let variant_fp = fingerprint_operands(&variant);

                // CONCRETE collision-resistance footing: the REAL FNV fingerprint actually CHANGES
                // under this drift (no collision at this enumerated point). This is the empirical
                // instance of the Lean `CollisionResistant` hypothesis `drift_detected` assumes.
                assert_ne!(
                    variant_fp, cert_fp,
                    "real FNV fingerprint must change under operand drift \
                     (base={base:?} variant={variant:?}) — collision-resistance footing"
                );

                // Lean drift gate must therefore FAIL on this observed/cert pair...
                assert!(
                    !drift_gate_passes(variant_fp, cert.operand_fingerprint()),
                    "model drift gate must fail on drifted operands (variant={variant:?})"
                );
                // ...and the REAL recheck must Reject, EXACTLY as Lean cekRecheckWithDrift = Reject
                // (cekRecheck_rejects_on_fingerprint_mismatch / drift_detected).
                assert!(
                    matches!(
                        recheck_elimination(&cert, &variant, &evidence),
                        RecheckOutcome::Rejected { .. }
                    ),
                    "real recheck must Reject drifted operands the model rejects \
                     (base={base:?} variant={variant:?})"
                );
                checked_reject += 1;
            }

            // Empty observed operands is a SEPARATE Rust gate (recheck guard.rs:627), mirroring the
            // Lean §III gate-2 (opsNonempty=no => keep/reject). Assert it here too for completeness.
            assert!(
                matches!(
                    recheck_elimination(&cert, &[], &evidence),
                    RecheckOutcome::Rejected { .. }
                ),
                "empty observed operands must be Rejected (base={base:?})"
            );
        }

        // We minted/rechecked one Valid per base config and at least one Reject per drift variant.
        assert_eq!(checked_valid, drift_base_configs().len() as u64);
        assert!(
            checked_reject >= 5 * drift_base_configs().len() as u64,
            "expected several drift rejects per base config, got {checked_reject}"
        );
    }
}
