// trust-cg-lower/lattice_guard.rs — the decidable, obligation-bound guard-replay capability
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! **The exact, obligation-bound replay capability the guard seam has been waiting for.**
//!
//! [`crate::guard_evidence`] says, and still says, that a trust-ir [`ProofStatus`] or a
//! `CleanCic` lineage record is *producer-owned metadata*: constructible through trust-ir's
//! public data model, therefore never elimination authority. That judgement is unchanged and
//! this module does not relax it by one bit.
//!
//! What changed is that trust-ir v30 added something that is **not** producer-owned metadata:
//! a *decidable predicate lattice* ([`trust_ir::pred`]). `PredTable::implies` is a total,
//! allocation-free, solver-free decision procedure that returns `true` ONLY when the
//! implication genuinely holds. That is exactly the shape the seam demanded:
//!
//! | seam requirement | how the lattice meets it |
//! |---|---|
//! | *independent* | the decision is trust-ir's, re-derived here from the module's own tables; trust-cg asserts nothing |
//! | *exact* | interval containment / finite-set subset / universe+space equality — no heuristic, no widening, no "probably" |
//! | *obligation-bound* | the production id is a pure function of the DISCHARGING PREDICATE'S CONTENT, the EXACT interval, and the originating function/base/index; changing any component changes the obligation |
//! | *replayable* | [`LatticeBoundsCapability::replay`] re-runs the whole decision from scratch against the tables and re-derives both ids; nothing is taken on trust |
//!
//! # What a capability means, precisely
//!
//! A diagnostic [`LatticeBoundsCapability`] for `(pred, bound)` asserts one thing:
//!
//! > the refinement predicate `pred` carried by the guard's INDEX value entails
//! > `Interval(0, bound - 1)`, which is exactly the condition the bounds guard tests.
//!
//! `TrapBoundsCheckExact base, index, bound` traps iff `!(index <u bound)`. So a certified
//! `index ∈ [0, bound-1]` means the trap is unreachable. Production additionally binds that
//! decision to the exact source function/base/index and requires ISel to reproduce the association
//! before the carrier is dead code.
//!
//! # Fail-closed, in five independent ways
//!
//! 1. **No source-bound capability, no elision.** Fields are private and there is no `Default` or
//!    `serde`. The public lattice witness is deliberately unbound and cannot become authority.
//! 2. **`implies` answers `false` when unsure.** A one-directional sound decision procedure
//!    means an almost-sufficient predicate (off by one, wrong space, wrong universe) mints
//!    nothing and the guard survives as a runtime check.
//! 3. **Exact per-use association.** ISel issues an opaque carrier binding only when function,
//!    LIR base, and LIR index match the private source association; a caller map or same-bound
//!    substitute carrier is inert.
//! 4. **The authority is feature-gated.** Without `lattice-guard-elision` the capability can
//!    still be minted and inspected (so its tests are meaningful on the default build) but
//!    [`lattice_guard_replay_authority_available`] is `false`, and every consumer refuses to
//!    turn it into behavior.
//! 5. **The kernel still decides.** A capability only fills a
//!    [`trust_cg_ir::DischargedEvidenceTable`] entry; deletion still requires
//!    [`trust_cg_ir::decide`] plus the independent operand-fingerprint re-check.
//!
//! [`ProofStatus`]: trust_ir::proof::ProofStatus

use std::collections::HashMap;

use trust_cg_ir::{
    AArch64GuardTarget, DischargeStatus, DischargedEvidenceTable, EliminationCertificate,
    EliminationVerdict, GuardKind, GuardObligationReceipt, GuardTarget, InstId, MachFunction,
    RecheckOutcome, decide, fingerprint_for_kind, recheck_elimination,
};
use trust_ir::Module;
use trust_ir::pred::{Pred, PredTable, Space, Universe};
use trust_ir::value::PredId;

use crate::instructions::Value;

/// Whether production holds a *decidable-lattice* guard-replay authority.
///
/// This is a SECOND, independent seam beside
/// [`crate::guard_evidence::validator_guard_replay_authority_available`], which stays `false`.
/// The two are deliberately not merged: that one is about producer-owned proof *labels* and
/// must remain unwired; this one is about a decision procedure trust-cg re-runs itself.
///
/// Gated on the `lattice-guard-elision` Cargo feature — a compile-time switch, not an
/// environment variable, so no runtime input can turn it on and a default build is bit-identical
/// to the pre-lattice compiler.
#[inline]
pub fn lattice_guard_replay_authority_available() -> bool {
    cfg!(feature = "lattice-guard-elision")
}

// ---------------------------------------------------------------------------
// Deterministic 128-bit FNV-1a — byte-for-byte reproducible across processes.
//
// Mirrors `trust_cg_ir::guard`'s private hasher for the same reason: the ids below must be
// re-derivable by an independent replay, so `DefaultHasher`/`RandomState` are unusable.
// ---------------------------------------------------------------------------

const FNV_OFFSET_BASIS_128: u128 = 0x6c62272e07bb0142_62b821756295c58d;
const FNV_PRIME_128: u128 = 0x0000000001000000_000000000000013B;

struct Fnv128(u128);

impl Fnv128 {
    fn new() -> Self {
        Self(FNV_OFFSET_BASIS_128)
    }
    fn u8(&mut self, b: u8) {
        self.0 ^= b as u128;
        self.0 = self.0.wrapping_mul(FNV_PRIME_128);
    }
    fn u64(&mut self, v: u64) {
        for i in 0..8 {
            self.u8((v >> (i * 8)) as u8);
        }
    }
    fn i128(&mut self, v: i128) {
        for i in 0..16 {
            self.u8((v as u128 >> (i * 8)) as u8);
        }
    }
    fn str(&mut self, s: &str) {
        self.u64(s.len() as u64);
        for b in s.bytes() {
            self.u8(b);
        }
    }
    fn finish(self) -> u128 {
        self.0
    }
}

/// Domain separation: nothing else in the compiler hashes with this tag, so a lattice
/// obligation id can never be confused with a module `ProofId` or a synthesized carrier id.
const LATTICE_OBLIGATION_DOMAIN: &str = "trust-cg.lattice-guard.bounds@1";
/// Separate tag for the lineage digest so the two ids of one capability are independent.
const LATTICE_LINEAGE_DOMAIN: &str = "trust-cg.lattice-guard.lineage@1";

/// Lattice obligation ids live strictly above every module `ProofId` (a dense `u32` index) AND
/// above [`crate::ProofContext::SYNTHESIZED_OBLIGATION_BASE`] (`1 << 32`), in the top quarter of
/// the `u64` space. An id in this range is, by construction, not any other kind of obligation.
pub const LATTICE_OBLIGATION_BASE: u64 = 3u64 << 62;

// ---------------------------------------------------------------------------
// RefinementEnv — the module's interned predicate/universe tables, carried forward.
// ---------------------------------------------------------------------------

/// A snapshot of a module's CONTENT-INTERNED `predicates` / `universes` tables.
///
/// The adapter consumes a `&Module` and produces LIR that outlives it, so the lattice tables
/// must travel with the proof context for the decision to be replayable downstream. Cloning
/// them is cheap in the only case that matters — a module with no refinements carries two empty
/// vectors — and it preserves interning exactly (the ids are indices into these very vectors).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RefinementEnv {
    predicates: Vec<Pred>,
    universes: Vec<Universe>,
}

impl RefinementEnv {
    /// Snapshot the module's lattice tables.
    pub fn from_module(module: &Module) -> Self {
        Self {
            predicates: module.predicates.clone(),
            universes: module.universes.clone(),
        }
    }

    /// Build the decision procedure over this snapshot.
    pub fn table(&self) -> PredTable<'_> {
        PredTable::new(&self.predicates, &self.universes)
    }

    /// No refinements in this module: every lattice query is a no-op.
    pub fn is_empty(&self) -> bool {
        self.predicates.is_empty() && self.universes.is_empty()
    }

    pub fn predicates(&self) -> &[Pred] {
        &self.predicates
    }

    pub fn universes(&self) -> &[Universe] {
        &self.universes
    }

    /// The predicate behind an id, or `None` when the id dangles (which every consumer must
    /// read as "no fact", never as "satisfied").
    pub fn pred(&self, id: PredId) -> Option<&Pred> {
        self.predicates.get(id.index() as usize)
    }

    /// Human-readable rendering of a predicate, for the certificate's "WHICH predicate
    /// discharged it" field and for diagnostics.
    pub fn describe(&self, id: PredId) -> Option<String> {
        self.pred(id)?;
        Some(self.table().describe(id))
    }
}

// ---------------------------------------------------------------------------
// The capability.
// ---------------------------------------------------------------------------

/// Exact source carrier that a lattice decision was made for.
///
/// A true predicate implication is not, by itself, permission to attach the result to an
/// arbitrary same-bound guard. The adapter records the originating function and exact LIR
/// base/index pair here; ISel must reproduce that association before it can mint the opaque
/// machine-carrier binding consumed by [`LatticeGuardReplayAuthority`].
#[derive(Debug, Clone, PartialEq, Eq)]
struct LatticeSourceCarrier {
    function: String,
    base: Value,
    index: Value,
}

/// An exact, obligation-bound, replayable authorization to elide ONE bounds guard.
///
/// Production capabilities are constructed only by the adapter's private, source-binding minter.
/// [`certify_bounds_guard`] deliberately returns an unbound decision witness for diagnostics and
/// lattice tests; an unbound witness can never produce behavior authority. Every field is private:
/// a capability cannot be forged, edited, deserialized, or defaulted into existence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LatticeBoundsCapability {
    /// The obligation id this capability discharges — a pure function of the discharging
    /// predicate's CONTENT plus the demanded interval. Threaded onto the guard carrier so the
    /// Certified-Elimination Kernel can bind receipt to evidence.
    obligation_id: u64,
    /// The `Certified`-tier lineage digest the kernel re-derives and compares.
    lineage_digest: u128,
    /// WHICH predicate discharged the obligation (the id, in the module's interned table).
    discharging_pred: PredId,
    /// WHICH predicate discharged the obligation (rendered, for the recorded certificate).
    discharging_pred_text: String,
    /// The obligation itself: `index ∈ [0, required_hi]`.
    required_hi: i128,
    /// The exact carrier bound this was certified against.
    bound: u64,
    /// Exact source function/base/index association. `None` means a diagnostic-only lattice
    /// decision witness, never replay authority.
    source_carrier: Option<LatticeSourceCarrier>,
}

impl LatticeBoundsCapability {
    /// The obligation id to thread onto the guard carrier.
    pub fn obligation_id(&self) -> u64 {
        self.obligation_id
    }

    /// The `Certified`-tier lineage digest for the evidence table and the carrier receipt.
    pub fn lineage_digest(&self) -> u128 {
        self.lineage_digest
    }

    /// The predicate id that discharged this obligation.
    pub fn discharging_pred(&self) -> PredId {
        self.discharging_pred
    }

    /// The predicate that discharged this obligation, rendered.
    pub fn discharging_pred_text(&self) -> &str {
        &self.discharging_pred_text
    }

    /// The exact carrier bound.
    pub fn bound(&self) -> u64 {
        self.bound
    }

    /// The discharged obligation, rendered for the elimination certificate.
    pub fn obligation_text(&self) -> String {
        format!(
            "index in [0, {}] (bounds guard `index <u {}`) discharged by refinement predicate \
             pred.{} = {}",
            self.required_hi,
            self.bound,
            self.discharging_pred.index(),
            self.discharging_pred_text,
        )
    }

    /// **Replay.** Re-run the entire decision from the tables and re-derive both ids; return
    /// `true` only if everything reproduces exactly.
    ///
    /// This is what makes the capability a *replay* capability rather than a claim: the
    /// consumer never has to trust the struct it is holding. Deterministic, solver-free, and
    /// independent of how the capability was originally minted (it re-enters through
    /// the same shared decision routine used by both the public diagnostic witness and the
    /// adapter's private source-binding minter).
    pub fn replay(&self, env: &RefinementEnv) -> bool {
        match certify_bounds_guard_impl(
            env,
            self.discharging_pred,
            self.bound,
            self.source_carrier.clone(),
        ) {
            Some(fresh) => fresh == *self,
            None => false,
        }
    }

    /// Whether this capability is bound to the exact LIR carrier currently being selected.
    pub(crate) fn matches_source_carrier(&self, function: &str, base: Value, index: Value) -> bool {
        self.source_carrier.as_ref().is_some_and(|carrier| {
            carrier.function == function && carrier.base == base && carrier.index == index
        })
    }
}

/// Decide whether refinement predicate `actual` entails the condition an exact bounds guard with
/// element count `bound` tests, and on success mint an **unbound diagnostic witness**.
///
/// This public result can be inspected and replayed, but cannot authorize elimination: production
/// uses [`certify_bounds_guard_for_source_carrier`] to add a private exact source association, and
/// ISel requires that association before issuing an opaque machine-carrier binding.
///
/// Returns `None` — and therefore keeps the guard — whenever:
///
/// * the module has no lattice tables, or `actual` dangles in them;
/// * `bound == 0` (an empty array: no index is in bounds, so there is nothing to discharge and
///   the demanded interval `[0, -1]` is not even well-formed);
/// * `bound` exceeds the `i128` interval space (unreachable for a real array, handled anyway);
/// * `PredTable::implies` answers `false`, which it does for every undecided case — including
///   an interval that is off by one, a finite set with one element too many, an
///   `InUniverse(_, Member)` where an index was demanded, and `Top` (a dropped fact).
pub fn certify_bounds_guard(
    env: &RefinementEnv,
    actual: PredId,
    bound: u64,
) -> Option<LatticeBoundsCapability> {
    certify_bounds_guard_impl(env, actual, bound, None)
}

/// Production minter: bind a decidable lattice implication to one exact source carrier.
///
/// This is crate-private so a public caller cannot turn a true predicate about one value into
/// authority for an unrelated same-bound LIR carrier. ISel independently matches this sealed
/// association before minting the machine-carrier binding.
pub(crate) fn certify_bounds_guard_for_source_carrier(
    env: &RefinementEnv,
    actual: PredId,
    bound: u64,
    function: &str,
    base: Value,
    index: Value,
) -> Option<LatticeBoundsCapability> {
    certify_bounds_guard_impl(
        env,
        actual,
        bound,
        Some(LatticeSourceCarrier {
            function: function.to_string(),
            base,
            index,
        }),
    )
}

fn certify_bounds_guard_impl(
    env: &RefinementEnv,
    actual: PredId,
    bound: u64,
    source_carrier: Option<LatticeSourceCarrier>,
) -> Option<LatticeBoundsCapability> {
    if env.is_empty() {
        return None;
    }
    // An empty array admits no in-bounds index; `Interval(0, -1)` is ill-formed and
    // `Pred::interval` rejects it. Fail closed rather than construct a degenerate obligation.
    if bound == 0 {
        return None;
    }
    let required_hi = i128::from(bound).checked_sub(1)?;
    let required = Pred::interval(0, required_hi)?;

    let table = env.table();
    let actual_pred = table.pred(actual)?;

    // THE DECISION. One call, no heuristic, no fallback, no widening. `implies_pred` is
    // trust-ir's own procedure over trust-ir's own tables; trust-cg contributes no judgement.
    if !table.implies_pred(actual_pred, &required) {
        return None;
    }

    let discharging_pred_text = table.describe(actual);
    let obligation_id =
        lattice_obligation_id(actual_pred, required_hi, bound, source_carrier.as_ref());
    let lineage_digest =
        lattice_lineage_digest(actual_pred, required_hi, bound, source_carrier.as_ref());

    Some(LatticeBoundsCapability {
        obligation_id,
        lineage_digest,
        discharging_pred: actual,
        discharging_pred_text,
        required_hi,
        bound,
        source_carrier,
    })
}

/// Opaque selector-issued association between a lattice obligation and one exact machine carrier.
///
/// Fields and constructor are crate-private. Public callers may inspect/clone a binding produced
/// by genuine ISel, but cannot fabricate a different fingerprint or associate a capability with
/// another same-bound carrier. The binding retains the *entire* capability rather than only its
/// compact obligation id: replay therefore compares the exact predicate, source association,
/// interval, full-width lineage, and id, and cannot join two capabilities on an id collision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LatticeGuardCarrierBinding {
    capability: LatticeBoundsCapability,
    operand_fingerprint: u128,
}

impl LatticeGuardCarrierBinding {
    pub(crate) fn new(capability: &LatticeBoundsCapability, operand_fingerprint: u128) -> Self {
        Self {
            capability: capability.clone(),
            operand_fingerprint,
        }
    }

    fn matches_capability(&self, candidate: &LatticeBoundsCapability) -> bool {
        self.capability == *candidate
    }
}

#[derive(Debug, Clone)]
struct LatticeCarrierBinding {
    obligation_id: u128,
    lineage_digest: u128,
    /// Fingerprint observed while the replayed capability was bound to the live carrier.
    ///
    /// Keeping this inside the opaque authority object prevents an `InstId`-only binding from
    /// silently surviving operand drift between gate construction and the proof pass.
    operand_fingerprint: u128,
    /// Function identity from the exact source carrier. This is checked again by `authorize`, so
    /// even a fully constructed authority cannot be transported to a different-named function
    /// with an otherwise identical machine-carrier fingerprint.
    source_function: String,
}

/// Opaque, replay-derived authority for AArch64 lattice bounds-guard elimination.
///
/// This is deliberately distinct from a caller-constructible
/// [`DischargedEvidenceTable`]/`HashMap` pair.  The only constructor replays the private
/// [`LatticeBoundsCapability`] values against their [`RefinementEnv`], re-derives each live
/// carrier fingerprint, and binds only an ISel-recorded lattice obligation whose certified bound
/// matches the carrier.  Consumers can ask this object to authorize or re-check a carrier, but
/// cannot inspect or replace its evidence and binding tables.
///
/// A compile-time feature enables the *replay procedure*; it is never, by itself, permission to
/// trust arbitrary public inputs.
#[derive(Debug, Clone, Default)]
pub struct LatticeGuardReplayAuthority {
    enabled: bool,
    /// Exact machine function the selector bindings were replayed against.
    ///
    /// Proof annotations are deliberately normalized away: the production
    /// pipeline stamps `InBounds` only after constructing this authority.
    /// Everything executable or structural remains in the identity, including
    /// definitions, operands, block membership, predecessor/successor edges,
    /// layout, signature, stack state, and lowering provenance. Keeping the
    /// canonical snapshot itself (rather than a compact hash) makes
    /// cross-function substitution collision-free.
    function_identity: String,
    evidence: DischargedEvidenceTable,
    bindings: HashMap<InstId, LatticeCarrierBinding>,
}

fn lattice_authority_function_identity(func: &MachFunction) -> String {
    let mut normalized = func.clone();
    for inst in &mut normalized.insts {
        inst.proof = None;
    }
    normalized.function_proofs.clear();
    format!("{normalized:?}")
}

impl LatticeGuardReplayAuthority {
    /// Replay lattice capabilities and bind them to exact live AArch64 guard carriers.
    ///
    /// `carrier_bindings` is the selector-issued opaque handoff. The resulting object retains
    /// neither caller-supplied evidence nor a caller-constructible fingerprint map: both evidence
    /// and per-`InstId` authority are reconstructed here from replayed source-bound capabilities,
    /// sealed selector bindings, and live carrier operands.
    pub fn replay_and_bind_aarch64(
        func: &MachFunction,
        carrier_bindings: &[LatticeGuardCarrierBinding],
        env: &RefinementEnv,
        capabilities: &[LatticeBoundsCapability],
    ) -> Self {
        if !lattice_guard_replay_authority_available() {
            return Self::default();
        }

        let mut authority = Self {
            enabled: true,
            function_identity: lattice_authority_function_identity(func),
            evidence: DischargedEvidenceTable::new(),
            bindings: HashMap::new(),
        };
        if capabilities.is_empty() || carrier_bindings.is_empty() {
            return authority;
        }

        // Admit only selector bindings whose *entire embedded capability* is still present and
        // replayable in the current context. Never join the two opaque handoffs on the compact
        // 62-bit obligation id: an id collision must be a fail-closed mismatch, not authority
        // substitution. Bind the originating function here as well as in `authorize`.
        let replayed_bindings: Vec<&LatticeGuardCarrierBinding> = carrier_bindings
            .iter()
            .filter(|binding| {
                let sealed = &binding.capability;
                let Some(source) = sealed.source_carrier.as_ref() else {
                    return false;
                };
                source.function == func.name
                    && capabilities.iter().any(|candidate| {
                        binding.matches_capability(candidate) && candidate.replay(env)
                    })
            })
            .collect();
        if replayed_bindings.is_empty() {
            return authority;
        }

        let target = AArch64GuardTarget;
        for idx in 0..func.insts.len() {
            let inst_id = InstId(idx as u32);
            let Some(kind) = target.classify_carrier(func.inst(inst_id)) else {
                continue;
            };
            if kind != GuardKind::BoundsCheck {
                continue;
            }

            let identity = target.operand_identity(func.inst(inst_id));
            let operand_fingerprint = fingerprint_for_kind(kind, &identity.operands);
            let mut matching = replayed_bindings
                .iter()
                .copied()
                .filter(|binding| binding.operand_fingerprint == operand_fingerprint);
            let Some(binding) = matching.next() else {
                continue;
            };
            // Two distinct exact capabilities claiming the same live carrier are ambiguous.
            // Refuse both rather than making iteration order an authority decision.
            if matching.any(|other| other.capability != binding.capability) {
                continue;
            }
            let capability = &binding.capability;
            let obligation_id = capability.obligation_id();
            if !is_lattice_obligation_id(obligation_id) {
                continue;
            }
            let lineage_digest = capability.lineage_digest();
            let certified_bound = capability.bound();
            let source_function = capability
                .source_carrier
                .as_ref()
                .expect("replayed binding was source-checked above")
                .function
                .clone();

            // The lattice obligation id includes `bound`, but the ISel handoff remains a map.
            // Re-check the live carrier's bound explicitly so even a corrupted/misassociated map
            // cannot bind a capability for one interval to a different runtime check.
            let Ok(certified_bound) = i64::try_from(certified_bound) else {
                continue;
            };
            if identity.operands.last() != Some(&trust_cg_ir::GuardOperandRef::Imm(certified_bound))
            {
                continue;
            }

            authority.evidence.insert(
                u128::from(obligation_id),
                DischargeStatus::Certified,
                Some(lineage_digest),
            );
            authority.bindings.insert(
                inst_id,
                LatticeCarrierBinding {
                    obligation_id: u128::from(obligation_id),
                    lineage_digest,
                    operand_fingerprint,
                    source_function,
                },
            );
        }
        authority
    }

    /// Whether the compile-time lattice replay lane was enabled when this object was built.
    pub fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Exact carriers bound by replay.  Used only to attach the dispatch annotation to those sites.
    pub fn bound_inst_ids(&self) -> impl Iterator<Item = InstId> + '_ {
        self.bindings.keys().copied()
    }

    /// Ask the Certified-Elimination Kernel about one exact live carrier.
    pub fn authorize(
        &self,
        func: &MachFunction,
        inst_id: InstId,
    ) -> Option<EliminationCertificate> {
        if !self.enabled {
            return None;
        }
        if lattice_authority_function_identity(func) != self.function_identity {
            return None;
        }
        let binding = self.bindings.get(&inst_id)?;
        if func.name != binding.source_function {
            return None;
        }
        let target = AArch64GuardTarget;
        let inst = func.inst(inst_id);
        let kind = target.classify_carrier(inst)?;
        if kind != GuardKind::BoundsCheck {
            return None;
        }
        let operand_identity = target.operand_identity(inst);
        if fingerprint_for_kind(kind, &operand_identity.operands) != binding.operand_fingerprint {
            return None;
        }
        let receipt = GuardObligationReceipt {
            kind,
            operand_identity,
            proof_obligation_id: Some(binding.obligation_id),
            lineage_digest: Some(binding.lineage_digest),
        };
        match decide(&receipt, &self.evidence) {
            EliminationVerdict::Eliminate { certificate } => Some(certificate),
            EliminationVerdict::Keep { .. } => None,
        }
    }

    /// Independently re-check a certificate against live, re-lifted operands.
    pub fn recheck(
        &self,
        certificate: &EliminationCertificate,
        observed_operands: &[trust_cg_ir::GuardOperandRef],
    ) -> RecheckOutcome {
        recheck_elimination(certificate, observed_operands, &self.evidence)
    }
}

/// Fold the directly represented predicate payload into the hasher.
///
/// Scalar predicates are content-stable across modules. `Conj`/`Disj` and
/// `InUniverse` contain table-local ids, so their compact identity is scoped to
/// the exact [`RefinementEnv`] replayed with the capability; it is not claimed
/// to be a cross-module content hash. The capability retains and replays the
/// complete predicate against that environment before this digest can carry
/// authority.
fn hash_pred_content(h: &mut Fnv128, p: &Pred) {
    match p {
        Pred::Interval { lo, hi } => {
            h.u8(1);
            h.i128(*lo);
            h.i128(*hi);
        }
        Pred::FiniteSet(items) => {
            h.u8(2);
            h.u64(items.len() as u64);
            for item in items {
                match trust_ir::pred::constant_key(item) {
                    Some((tag, v)) => {
                        h.u8(tag);
                        h.i128(v);
                    }
                    // A non-scalar member is not canonical and cannot appear in a validated
                    // module; fold a distinct marker rather than silently colliding.
                    None => h.u8(0xff),
                }
            }
        }
        Pred::InUniverse(u, space) => {
            h.u8(3);
            h.u64(u64::from(u.index()));
            h.u8(match space {
                Space::Index => 0,
                Space::Member => 1,
            });
        }
        Pred::NonZero => h.u8(4),
        Pred::NonNull => h.u8(5),
        Pred::Conj(children) => {
            h.u8(6);
            h.u64(children.len() as u64);
            for c in children {
                h.u64(u64::from(c.index()));
            }
        }
        Pred::Disj(children) => {
            h.u8(7);
            h.u64(children.len() as u64);
            for c in children {
                h.u64(u64::from(c.index()));
            }
        }
        Pred::Top => h.u8(8),
        Pred::Bottom => h.u8(9),
    }
}

fn hash_source_carrier(h: &mut Fnv128, source_carrier: Option<&LatticeSourceCarrier>) {
    match source_carrier {
        Some(carrier) => {
            h.u8(1);
            h.str(&carrier.function);
            h.u64(u64::from(carrier.base.0));
            h.u64(u64::from(carrier.index.0));
        }
        None => h.u8(0),
    }
}

fn lattice_obligation_id(
    actual: &Pred,
    required_hi: i128,
    bound: u64,
    source_carrier: Option<&LatticeSourceCarrier>,
) -> u64 {
    let mut h = Fnv128::new();
    h.str(LATTICE_OBLIGATION_DOMAIN);
    hash_pred_content(&mut h, actual);
    h.i128(required_hi);
    h.u64(bound);
    hash_source_carrier(&mut h, source_carrier);
    // Fold 128 -> 62 bits and lift into the reserved lattice range. The range tag is what makes
    // the id unmistakable; the 62 bits of content keep distinct obligations distinct.
    let folded = h.finish();
    let low = ((folded as u64) ^ ((folded >> 64) as u64)) & ((1u64 << 62) - 1);
    LATTICE_OBLIGATION_BASE | low
}

fn lattice_lineage_digest(
    actual: &Pred,
    required_hi: i128,
    bound: u64,
    source_carrier: Option<&LatticeSourceCarrier>,
) -> u128 {
    let mut h = Fnv128::new();
    h.str(LATTICE_LINEAGE_DOMAIN);
    hash_pred_content(&mut h, actual);
    h.i128(required_hi);
    h.u64(bound);
    hash_source_carrier(&mut h, source_carrier);
    h.finish()
}

/// Is this obligation id one the lattice minted? Used by consumers to assert that the only
/// authority in an evidence table is lattice authority.
#[inline]
pub fn is_lattice_obligation_id(id: u64) -> bool {
    id & LATTICE_OBLIGATION_BASE == LATTICE_OBLIGATION_BASE
}

#[cfg(test)]
mod tests {
    use super::*;
    // Machine-IR carriers are used ONLY by the elision helpers below, which are
    // themselves `#[cfg(feature = "lattice-guard-elision")]`. Without the same
    // gate these imports are unused in the default feature set, and the crate's
    // `-D warnings` lint level turns that into a hard error — so
    // `cargo test -p trust-cg-lower` could not build AT ALL by default.
    #[cfg(feature = "lattice-guard-elision")]
    use trust_cg_ir::regs::{RegClass, VReg};
    #[cfg(feature = "lattice-guard-elision")]
    use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand, Signature as MachSignature};
    use trust_ir::constant::Constant;
    use trust_ir::value::UnivId;

    /// Build an env with one predicate; returns the env and its id.
    fn env_with(preds: Vec<Pred>, universes: Vec<Universe>) -> RefinementEnv {
        RefinementEnv {
            predicates: preds,
            universes,
        }
    }

    #[test]
    fn exact_interval_certifies_the_matching_bound() {
        let env = env_with(vec![Pred::interval(0, 7).unwrap()], vec![]);
        let cap = certify_bounds_guard(&env, PredId::new(0), 8)
            .expect("[0,7] entails the [0,7] a bound-8 guard demands");
        assert_eq!(cap.bound(), 8);
        assert_eq!(cap.discharging_pred(), PredId::new(0));
        assert!(is_lattice_obligation_id(cap.obligation_id()));
        assert!(cap.obligation_id() > crate::ProofContext::SYNTHESIZED_OBLIGATION_BASE);
        assert!(cap.replay(&env), "a freshly minted capability must replay");
    }

    /// THE FAIL-CLOSED PROOF: a predicate that is ALMOST sufficient — off by exactly one — mints
    /// nothing, so the guard survives.
    #[test]
    fn off_by_one_interval_certifies_nothing() {
        // The value is in [0, 8]; the bound-8 guard demands [0, 7]. Index 8 traps.
        let env = env_with(vec![Pred::interval(0, 8).unwrap()], vec![]);
        assert!(certify_bounds_guard(&env, PredId::new(0), 8).is_none());
        // Tighten by one and it certifies — so the refusal above is about the off-by-one, not
        // about the machinery being inert.
        let tight = env_with(vec![Pred::interval(0, 7).unwrap()], vec![]);
        assert!(certify_bounds_guard(&tight, PredId::new(0), 8).is_some());
    }

    #[test]
    fn negative_lower_bound_certifies_nothing() {
        // [-1, 7] admits index -1, which a `<u bound` guard traps on.
        let env = env_with(vec![Pred::interval(-1, 7).unwrap()], vec![]);
        assert!(certify_bounds_guard(&env, PredId::new(0), 8).is_none());
    }

    #[test]
    fn top_certifies_nothing() {
        // Top is where a DROPPED fact lands. It must entail nothing non-trivial.
        let env = env_with(vec![Pred::Top], vec![]);
        assert!(certify_bounds_guard(&env, PredId::new(0), 8).is_none());
    }

    #[test]
    fn member_space_never_certifies_an_index_bound() {
        // THE SHIPPED MISCOMPILE CLASS, at the guard site. Universe U has EIGHT members, so an
        // INDEX into it is in [0,7] and safely indexes an 8-element array. A MEMBER of U is a
        // completely different integer — here {100,...,107} — and indexing with it walks off the
        // end. Same machine word, same universe; only the CONVENTION differs. That is exactly
        // the fact the type now carries, and the guard survives when it says "member".
        let universes = vec![Universe::members((100i128..108).map(Constant::Int)).unwrap()];
        let member = env_with(
            vec![Pred::InUniverse(UnivId::new(0), Space::Member)],
            universes.clone(),
        );
        assert!(
            certify_bounds_guard(&member, PredId::new(0), 8).is_none(),
            "a MEMBER of U is not an INDEX into U — the guard must stay"
        );
        // The INDEX space over the SAME universe does certify: `0 <= v < |U| = 8`.
        let index = env_with(
            vec![Pred::InUniverse(UnivId::new(0), Space::Index)],
            universes,
        );
        assert!(
            certify_bounds_guard(&index, PredId::new(0), 8).is_some(),
            "flipping ONLY the convention flips the verdict — the refusal above is non-vacuous"
        );
    }

    #[test]
    fn universe_index_does_not_certify_a_larger_bound_than_its_cardinality_allows() {
        // |U| = 8 so an index is in [0,7]; that entails a bound-8 guard AND every WIDER guard,
        // but never a NARROWER one.
        let universes = vec![Universe::members((0i128..8).map(Constant::Int)).unwrap()];
        let env = env_with(
            vec![Pred::InUniverse(UnivId::new(0), Space::Index)],
            universes,
        );
        assert!(certify_bounds_guard(&env, PredId::new(0), 8).is_some());
        assert!(certify_bounds_guard(&env, PredId::new(0), 9).is_some());
        assert!(certify_bounds_guard(&env, PredId::new(0), 7).is_none());
    }

    #[test]
    fn empty_env_dangling_id_and_zero_bound_all_certify_nothing() {
        let empty = RefinementEnv::default();
        assert!(certify_bounds_guard(&empty, PredId::new(0), 8).is_none());

        let env = env_with(vec![Pred::interval(0, 7).unwrap()], vec![]);
        assert!(
            certify_bounds_guard(&env, PredId::new(9), 8).is_none(),
            "a dangling PredId must read as no fact, never as a satisfied one"
        );
        assert!(
            certify_bounds_guard(&env, PredId::new(0), 0).is_none(),
            "a zero-length array admits no in-bounds index"
        );
    }

    #[test]
    fn obligation_id_is_a_function_of_predicate_content_and_bound() {
        let a = env_with(vec![Pred::interval(0, 7).unwrap()], vec![]);
        let b = env_with(
            vec![Pred::Top, Pred::interval(0, 7).unwrap()],
            vec![Universe::range(0, 3).unwrap()],
        );
        // Same predicate CONTENT at a different id in a differently-shaped table => same id.
        let ca = certify_bounds_guard(&a, PredId::new(0), 8).unwrap();
        let cb = certify_bounds_guard(&b, PredId::new(1), 8).unwrap();
        assert_eq!(ca.obligation_id(), cb.obligation_id());
        assert_eq!(ca.lineage_digest(), cb.lineage_digest());

        // A different bound is a DIFFERENT obligation, even from the same predicate.
        let wider = certify_bounds_guard(&a, PredId::new(0), 9).unwrap();
        assert_ne!(ca.obligation_id(), wider.obligation_id());
        assert_ne!(ca.lineage_digest(), wider.lineage_digest());
        // ... and the two ids of one capability are independent (different domain tags).
        assert_ne!(u128::from(ca.obligation_id()), ca.lineage_digest());
    }

    #[test]
    fn replay_rejects_a_capability_whose_env_no_longer_supports_it() {
        let env = env_with(vec![Pred::interval(0, 7).unwrap()], vec![]);
        let cap = certify_bounds_guard(&env, PredId::new(0), 8).unwrap();
        // Same id, weaker predicate: the replay re-decides and refuses.
        let drifted = env_with(vec![Pred::interval(0, 8).unwrap()], vec![]);
        assert!(!cap.replay(&drifted));
        // Same id, same-shaped table but the fact was dropped to Top.
        let dropped = env_with(vec![Pred::Top], vec![]);
        assert!(!cap.replay(&dropped));
    }

    #[test]
    fn finite_set_subset_certifies_and_a_superset_does_not() {
        let inside = env_with(
            vec![Pred::finite_set([0i128, 3, 7].map(Constant::Int)).unwrap()],
            vec![],
        );
        assert!(certify_bounds_guard(&inside, PredId::new(0), 8).is_some());
        let outside = env_with(
            vec![Pred::finite_set([0i128, 3, 8].map(Constant::Int)).unwrap()],
            vec![],
        );
        assert!(certify_bounds_guard(&outside, PredId::new(0), 8).is_none());
    }

    #[test]
    fn describe_names_the_discharging_predicate() {
        let env = env_with(vec![Pred::interval(0, 7).unwrap()], vec![]);
        let cap = certify_bounds_guard(&env, PredId::new(0), 8).unwrap();
        assert!(!cap.discharging_pred_text().is_empty());
        let text = cap.obligation_text();
        assert!(
            text.contains("pred.0"),
            "certificate names WHICH predicate: {text}"
        );
        assert!(text.contains("index in [0, 7]"), "{text}");
    }

    #[test]
    fn default_build_holds_no_lattice_authority() {
        // The capability is mintable and inspectable on every build; only the AUTHORITY to turn
        // it into behavior is feature-gated.
        assert_eq!(
            lattice_guard_replay_authority_available(),
            cfg!(feature = "lattice-guard-elision")
        );
    }

    #[test]
    fn lattice_ids_never_collide_with_module_or_synthesized_obligation_ids() {
        // Module ProofIds are dense u32 indices; synthesized ids start at 1<<32.
        assert!(!is_lattice_obligation_id(0));
        assert!(!is_lattice_obligation_id(u64::from(u32::MAX)));
        assert!(!is_lattice_obligation_id(
            crate::ProofContext::SYNTHESIZED_OBLIGATION_BASE
        ));
        assert!(is_lattice_obligation_id(LATTICE_OBLIGATION_BASE));
    }

    #[cfg(feature = "lattice-guard-elision")]
    fn bounds_carrier_named(name: &str, bound: i64, index: u32) -> (MachFunction, InstId, u128) {
        let mut func = MachFunction::new(name.to_string(), MachSignature::new(vec![], vec![]));
        let guard = MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![
                MachOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                MachOperand::VReg(VReg::new(index, RegClass::Gpr64)),
                MachOperand::Imm(bound),
            ],
        );
        let guard_id = func.push_inst(guard);
        func.append_inst(func.entry, guard_id);
        let target = AArch64GuardTarget;
        let identity = target.operand_identity(func.inst(guard_id));
        let fingerprint = fingerprint_for_kind(GuardKind::BoundsCheck, &identity.operands);
        (func, guard_id, fingerprint)
    }

    #[cfg(feature = "lattice-guard-elision")]
    fn bounds_carrier_with_index(bound: i64, index: u32) -> (MachFunction, InstId, u128) {
        bounds_carrier_named("lattice_authority", bound, index)
    }

    #[cfg(feature = "lattice-guard-elision")]
    fn source_bound_capability(env: &RefinementEnv) -> LatticeBoundsCapability {
        certify_bounds_guard_for_source_carrier(
            env,
            PredId::new(0),
            8,
            "lattice_authority",
            Value(0),
            Value(1),
        )
        .unwrap()
    }

    #[cfg(feature = "lattice-guard-elision")]
    #[test]
    fn replay_authority_binds_exact_carrier_and_rejects_later_operand_drift() {
        let env = env_with(vec![Pred::interval(0, 7).unwrap()], vec![]);
        let capability = source_bound_capability(&env);
        let (mut func, guard_id, fingerprint) = bounds_carrier_with_index(8, 1);
        let carrier_bindings = [LatticeGuardCarrierBinding::new(&capability, fingerprint)];

        let authority = LatticeGuardReplayAuthority::replay_and_bind_aarch64(
            &func,
            &carrier_bindings,
            &env,
            std::slice::from_ref(&capability),
        );
        assert!(authority.is_enabled());
        assert_eq!(authority.bound_inst_ids().collect::<Vec<_>>(), [guard_id]);
        let certificate = authority
            .authorize(&func, guard_id)
            .expect("the replay-bound exact carrier must authorize");
        let observed = AArch64GuardTarget
            .operand_identity(func.inst(guard_id))
            .operands;
        assert_eq!(
            authority.recheck(&certificate, &observed),
            RecheckOutcome::Valid
        );

        func.inst_mut(guard_id).operands[1] = MachOperand::VReg(VReg::new(2, RegClass::Gpr64));
        assert!(
            authority.authorize(&func, guard_id).is_none(),
            "an InstId binding must not survive live operand drift"
        );
    }

    #[cfg(feature = "lattice-guard-elision")]
    #[test]
    fn replay_authority_rejects_capability_misassociated_with_another_bound() {
        let env = env_with(vec![Pred::interval(0, 7).unwrap()], vec![]);
        let capability = source_bound_capability(&env);
        let (func, guard_id, wrong_fingerprint) = bounds_carrier_with_index(9, 1);
        // Model a corrupted selector handoff that associates a valid bound-8 capability with a
        // live bound-9 carrier. The explicit live-bound check must keep it unbound.
        let carrier_bindings = [LatticeGuardCarrierBinding::new(
            &capability,
            wrong_fingerprint,
        )];
        let authority = LatticeGuardReplayAuthority::replay_and_bind_aarch64(
            &func,
            &carrier_bindings,
            &env,
            std::slice::from_ref(&capability),
        );
        assert!(authority.bound_inst_ids().next().is_none());
        assert!(authority.authorize(&func, guard_id).is_none());
    }

    #[cfg(feature = "lattice-guard-elision")]
    #[test]
    fn replay_authority_rejects_same_bound_carrier_substitution() {
        let env = env_with(vec![Pred::interval(0, 7).unwrap()], vec![]);
        let capability = source_bound_capability(&env);
        let (_, _, certified_fingerprint) = bounds_carrier_with_index(8, 1);
        let carrier_bindings = [LatticeGuardCarrierBinding::new(
            &capability,
            certified_fingerprint,
        )];

        // Same guard kind and same bound, but a different index carrier. A caller-supplied map
        // could associate the capability with this fingerprint; the opaque selector binding
        // cannot be rewritten, so replay must keep the substituted guard.
        let (substituted, guard_id, substituted_fingerprint) = bounds_carrier_with_index(8, 2);
        assert_ne!(certified_fingerprint, substituted_fingerprint);
        let authority = LatticeGuardReplayAuthority::replay_and_bind_aarch64(
            &substituted,
            &carrier_bindings,
            &env,
            std::slice::from_ref(&capability),
        );
        assert!(authority.bound_inst_ids().next().is_none());
        assert!(authority.authorize(&substituted, guard_id).is_none());
    }

    #[cfg(feature = "lattice-guard-elision")]
    #[test]
    fn public_unbound_lattice_witness_cannot_become_authority() {
        let env = env_with(vec![Pred::interval(0, 7).unwrap()], vec![]);
        let unbound = certify_bounds_guard(&env, PredId::new(0), 8).unwrap();
        let (func, guard_id, fingerprint) = bounds_carrier_with_index(8, 1);
        let carrier_bindings = [LatticeGuardCarrierBinding::new(&unbound, fingerprint)];
        let authority = LatticeGuardReplayAuthority::replay_and_bind_aarch64(
            &func,
            &carrier_bindings,
            &env,
            std::slice::from_ref(&unbound),
        );
        assert!(authority.bound_inst_ids().next().is_none());
        assert!(authority.authorize(&func, guard_id).is_none());
    }

    #[cfg(feature = "lattice-guard-elision")]
    #[test]
    fn replay_authority_rejects_cross_function_identical_carrier_substitution() {
        let env = env_with(vec![Pred::interval(0, 7).unwrap()], vec![]);
        let capability = source_bound_capability(&env);
        let (original, original_guard, fingerprint) = bounds_carrier_with_index(8, 1);
        let carrier_bindings = [LatticeGuardCarrierBinding::new(&capability, fingerprint)];

        // The exact same opcode, operands, bound, InstId, and fingerprint in a different function
        // must not inherit the original function's refinement authority.
        let (substituted, substituted_guard, substituted_fingerprint) =
            bounds_carrier_named("unrelated_function", 8, 1);
        assert_eq!(original_guard, substituted_guard);
        assert_eq!(fingerprint, substituted_fingerprint);

        let substituted_authority = LatticeGuardReplayAuthority::replay_and_bind_aarch64(
            &substituted,
            &carrier_bindings,
            &env,
            std::slice::from_ref(&capability),
        );
        assert!(substituted_authority.bound_inst_ids().next().is_none());
        assert!(
            substituted_authority
                .authorize(&substituted, substituted_guard)
                .is_none()
        );

        // Also reject transporting an already-built authority after replay.
        let original_authority = LatticeGuardReplayAuthority::replay_and_bind_aarch64(
            &original,
            &carrier_bindings,
            &env,
            std::slice::from_ref(&capability),
        );
        assert!(
            original_authority
                .authorize(&substituted, substituted_guard)
                .is_none()
        );
    }

    #[cfg(feature = "lattice-guard-elision")]
    #[test]
    fn replay_authority_rejects_same_name_different_definition_or_cfg() {
        let env = env_with(vec![Pred::interval(0, 7).unwrap()], vec![]);
        let capability = source_bound_capability(&env);
        let (original, guard_id, fingerprint) = bounds_carrier_with_index(8, 1);
        let carrier_bindings = [LatticeGuardCarrierBinding::new(&capability, fingerprint)];
        let authority = LatticeGuardReplayAuthority::replay_and_bind_aarch64(
            &original,
            &carrier_bindings,
            &env,
            std::slice::from_ref(&capability),
        );
        assert!(authority.authorize(&original, guard_id).is_some());

        // Same function name, guard InstId, opcode, operands, and bound, but a
        // different definition of the guard's index carrier. A per-carrier
        // fingerprint cannot see this substitution; the exact function
        // identity must.
        let mut different_definition = original.clone();
        let definition = different_definition.push_inst(MachInst::new(
            AArch64Opcode::Movz,
            vec![
                MachOperand::VReg(VReg::new(1, RegClass::Gpr64)),
                MachOperand::Imm(99),
            ],
        ));
        different_definition
            .block_mut(different_definition.entry)
            .insts
            .insert(0, definition);
        assert!(
            authority
                .authorize(&different_definition, guard_id)
                .is_none()
        );

        // Preserve the complete instruction arena but move the guard into a
        // different CFG block. Block membership and edges are semantic inputs
        // to dominance, so this must also invalidate the authority.
        let mut different_cfg = original.clone();
        let other = different_cfg.create_block();
        different_cfg.block_mut(different_cfg.entry).insts.clear();
        different_cfg.append_inst(other, guard_id);
        assert!(authority.authorize(&different_cfg, guard_id).is_none());

        // Dispatch-only proof metadata is intentionally excluded: production
        // stamps this annotation after replay and the executable function is
        // otherwise byte-for-byte identical.
        let mut annotated = original.clone();
        annotated.inst_mut(guard_id).proof = Some(trust_cg_ir::ProofAnnotation::InBounds);
        assert!(authority.authorize(&annotated, guard_id).is_some());
    }

    #[cfg(feature = "lattice-guard-elision")]
    #[test]
    fn selector_binding_rejects_obligation_id_collision_substitution() {
        let env = env_with(
            vec![
                Pred::interval(0, 7).unwrap(),
                Pred::finite_set([0i128, 1, 2, 3, 4, 5, 6, 7].map(Constant::Int)).unwrap(),
            ],
            vec![],
        );
        let original = certify_bounds_guard_for_source_carrier(
            &env,
            PredId::new(0),
            8,
            "lattice_authority",
            Value(0),
            Value(1),
        )
        .unwrap();
        let mut colliding_substitute = certify_bounds_guard_for_source_carrier(
            &env,
            PredId::new(1),
            8,
            "lattice_authority",
            Value(0),
            Value(1),
        )
        .unwrap();
        assert_ne!(
            original.obligation_id(),
            colliding_substitute.obligation_id()
        );
        assert_ne!(
            original.lineage_digest(),
            colliding_substitute.lineage_digest()
        );

        // Model a collision in the compact 62-bit id while retaining a different full-width
        // lineage and exact predicate. The selector binding compares the entire capability, so
        // equal compact ids can never substitute for one another.
        colliding_substitute.obligation_id = original.obligation_id();
        let binding = LatticeGuardCarrierBinding::new(&original, 0);
        assert_eq!(
            binding.capability.obligation_id(),
            colliding_substitute.obligation_id()
        );
        assert!(!binding.matches_capability(&colliding_substitute));
    }
}
