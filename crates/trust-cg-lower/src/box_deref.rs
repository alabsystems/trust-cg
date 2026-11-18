// trust-cg-lower/src/box_deref.rs - the one acceptance check for trust-ir Inst::BoxDeref
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The ONE acceptance check for trust-ir `Inst::BoxDeref` (wire v74,
//! `SPEC_RATIFICATIONS` section 28), shared by every target.
//!
//! # What is decided here
//!
//! [`admit_box_derefs`] is the only function in this backend that decides
//! whether a module's `BoxDeref` instructions are admitted. The x86-64,
//! AArch64 and RISC-V lanes reach it through the shared pin-move floor
//! (`reject_unconsumed_v41_target_neutral_surface*`) and through
//! [`crate::CodegenLicensePolicy::enforce_module`]; the WASM module entries
//! call the same two functions before their own lowering. No lane restates
//! the rule, and no lane compares tiers itself.
//!
//! The structural rules of the carried fact (rules 1 to 9) and the evidence
//! floor are trust-ir's, read from
//! `trust_ir_build::validate_module_for_codegen_with` under
//! `CodegenAdmission::with_require_box_validity_evidence`. This module
//! classifies those findings as one typed refusal
//! ([`AdapterError::BoxDerefNotAdmitted`]) and writes the manifest. The one
//! verdict it adds is its own re-derivation (below), which only the floors
//! that opt into it consult, and which can only discharge a floor finding
//! for a conjunct it establishes; it never relaxes a rule.
//!
//! # The three floors
//!
//! [`BoxValidityFloor`] has three values, most restrictive first, and no
//! spelling for anything weaker than the last:
//!
//! - [`BoxValidityFloor::Refuse`] (the default of every policy, and the gate
//!   of every proof-emitting, verified-promotion and JIT-verified compile):
//!   trust-ir's `ConsumerRederived` floor, exactly as trust-ir states it. No
//!   evidence kind of the pinned format reaches it, so every `BoxDeref` is
//!   refused at it. This backend's re-derivation is NOT consulted here.
//! - [`BoxValidityFloor::LocallyRederived`] (opt-in by name,
//!   [`crate::CodegenLicensePolicy::with_locally_rederived_box_floor`]):
//!   trust-ir's findings at its `ConsumerRederived` floor, each discharged
//!   only for a conjunct this backend RE-DERIVES itself from the function's
//!   own instructions ([`crate::box_deref_rederive`]): a stack slot or a
//!   success-tested Rust-heap allocation of the same function, in bounds,
//!   aligned, and neither freed nor escaped on any path to the deref. Every
//!   other `BoxDeref` is refused, and a named premise is never evidence at
//!   it. This is a consumer-local verdict, not trust-ir's tier (which is
//!   defined as what EVERY consumer re-derives), so it has its own name and
//!   its own license identity token.
//! - [`BoxValidityFloor::NamedPremise`]: trust-ir's `NamedPremise` floor. A
//!   consumer opts in by name and only by handing over the place the
//!   assumptions are reported
//!   ([`crate::CodegenLicensePolicy::with_named_premise_box_floor`], which
//!   takes a [`BoxDerefDisclosure`]): there is no way to select this floor
//!   without one, so every entry that admits under it reports to its caller.
//!   It admits a fact whose every conjunct is a premise on a root the format
//!   classes as a named premise, and refuses the assumed roots
//!   (`returned_box_assumed`, `reference_arg_box_valid`) and both reserved
//!   evidence kinds, except that a conjunct this backend re-derives
//!   discharges its finding here too, so this floor admits everything
//!   `LocallyRederived` admits.
//!
//! The shared floor, which has no policy in scope, checks every module at
//! [`BoxValidityFloor::MOST_PERMISSIVE`]: nothing below trust-ir's
//! `NamedPremise` floor, and nothing `LocallyRederived` would refuse, is
//! admitted on any path, whatever a policy says.
//!
//! # The consumer re-derivation
//!
//! At a floor that opts into it ([`BoxValidityFloor::rederives`]), trust-ir's
//! floor finding for a conjunct this backend re-derives
//! ([`crate::box_deref_rederive`]) is discharged ([`discharged_by_rederivation`],
//! used by the three entries that read trust-ir's findings). Nothing else is
//! relaxed: the structural rules of the fact (1 to 9) still refuse first, a
//! conjunct that is not re-derived keeps trust-ir's floor finding, and the
//! re-derivation is a decision of this consumer that is never written back
//! into the module (the v74 wire has no consumer-re-derived evidence kind).
//! The manifest keeps the fact's own evidence tier and lists the re-derived
//! conjuncts separately; a row whose every conjunct is re-derived is not an
//! assumption and is not disclosed as one.
//!
//! # What an admitted instruction licenses
//!
//! Nothing. An admitted `BoxDeref` is lowered as the pointer-preserving copy
//! it is. The fact is a named assumption: it is validated, counted in the
//! manifest and reported, and no pass or lowering may use it, or the
//! instruction's undefined behaviour, to remove a check or a branch or to
//! move or introduce a memory access (section 28, "No licence from the
//! undefined behaviour"). A re-derived conjunct licenses nothing either: it
//! decides admission only. The manifest is evidence of what was assumed and
//! of what this backend re-derived, not a proof of validity.

use trust_ir::box_validity::{BoxDerefSite, BoxValidityTier, PremiseRoot, ValidityConjunct};
use trust_ir::{BlockId, Function, Inst, Module};

use crate::adapter::AdapterError;
pub(crate) use crate::box_deref_rederive::ModuleRederiver;

/// The evidence floor a consumer holds `Inst::BoxDeref` to. Ordered most
/// restrictive first; each floor admits everything the floors before it
/// admit, and there is no value below trust-ir's `NamedPremise`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub enum BoxValidityFloor {
    /// Refuse every `BoxDeref` (trust-ir's `ConsumerRederived` floor, which
    /// no v74 evidence reaches; this backend's re-derivation is not
    /// consulted). The default, and the only floor a proof-required lane may
    /// use.
    #[default]
    Refuse,
    /// Admit only a `BoxDeref` whose every conjunct this backend re-derives
    /// from its own function (trust-ir's findings at `ConsumerRederived`,
    /// discharged per conjunct by [`crate::box_deref_rederive`]). Opt-in; a
    /// consumer-local verdict, not trust-ir's tier.
    LocallyRederived,
    /// Admit a fact whose every conjunct rests on a named premise (trust-ir's
    /// `NamedPremise` floor) or is re-derived by this backend. Opt-in; the
    /// diagnostic lane's floor.
    NamedPremise,
}

impl BoxValidityFloor {
    /// The weakest floor any path of this backend applies: the bound the
    /// policy-free shared floor checks every module against.
    pub const MOST_PERMISSIVE: Self = Self::NamedPremise;

    /// The trust-ir tier whose findings this floor reads.
    #[must_use]
    pub const fn tier(self) -> BoxValidityTier {
        match self {
            Self::Refuse | Self::LocallyRederived => BoxValidityTier::ConsumerRederived,
            Self::NamedPremise => BoxValidityTier::NamedPremise,
        }
    }

    /// Whether this floor consults this backend's own re-derivation to
    /// discharge a trust-ir floor finding. `Refuse` never does.
    #[must_use]
    pub const fn rederives(self) -> bool {
        match self {
            Self::Refuse => false,
            Self::LocallyRederived | Self::NamedPremise => true,
        }
    }

    /// The diagnostic and identity spelling: trust-ir's name of the tier for
    /// the two floors that are trust-ir's, and this backend's own name for
    /// the consumer-local one (never trust-ir's tier name).
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Refuse | Self::NamedPremise => self.tier().name(),
            Self::LocallyRederived => "trust_cg_locally_rederived_v1",
        }
    }
}

/// Why a `BoxDeref` was not admitted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoxDerefRefusal {
    /// A conjunct's evidence is below the floor. All three names are
    /// trust-ir's (`BoxValidityEvidenceBelowFloor`).
    EvidenceBelowFloor {
        conjunct: &'static str,
        tier: &'static str,
        floor: &'static str,
        /// Why this backend's own re-derivation did not establish the
        /// conjunct (`None` where the entry classified the finding without
        /// running it).
        not_rederived: Option<&'static str>,
    },
    /// trust-ir's validator refused the carried fact under one of its
    /// structural rules; `rule` is its variant name and `finding` its text.
    FactRefused { rule: &'static str, finding: String },
    /// The function was handed to a lowering entry without the module its
    /// fact must be validated against, so no rule was checked.
    NoModule,
    /// The fact passed validation but names no single premise root or has no
    /// evidence tier: the manifest cannot state what was assumed.
    NoManifestRow,
}

impl std::fmt::Display for BoxDerefRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EvidenceBelowFloor {
                conjunct,
                tier,
                floor,
                not_rederived,
            } => {
                write!(
                    f,
                    "conjunct {conjunct} is backed at tier {tier}, below this lane's Box validity \
                     floor {floor}"
                )?;
                if let Some(why) = not_rederived {
                    write!(f, "; this backend does not re-derive it: {why}")?;
                }
                Ok(())
            }
            Self::FactRefused { rule, finding } => {
                write!(f, "trust-ir refuses its validity fact ({rule}): {finding}")
            }
            Self::NoModule => f.write_str(
                "the function was not admitted with its module, so its validity fact was \
                 checked against no rule",
            ),
            Self::NoManifestRow => f.write_str(
                "its validity fact names no single premise root, so the assumption manifest \
                 cannot state what was assumed",
            ),
        }
    }
}

/// One admitted `BoxDeref`: what was assumed, per instruction (never per
/// site id; one id may label several instructions).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoxDerefManifestRow {
    pub function: String,
    pub block: u32,
    pub inst_index: u32,
    /// The producer's site id, verbatim.
    pub site: BoxDerefSite,
    /// The one root every premise of the fact names.
    pub root: PremiseRoot,
    /// The weakest evidence tier the FACT carries, exactly as trust-ir
    /// grades it. Never raised by this backend's re-derivation, which is
    /// reported in `rederived` instead.
    pub tier: BoxValidityTier,
    /// The conjuncts this backend re-derived from the function itself, in
    /// canonical order (empty when none was, and always empty at a floor that
    /// does not consult the re-derivation).
    pub rederived: Vec<ValidityConjunct>,
    /// The conjuncts that rest on the fact's evidence alone, below trust-ir's
    /// `ConsumerRederived` tier and not in `rederived`, in canonical order.
    pub assumed: Vec<ValidityConjunct>,
}

impl BoxDerefManifestRow {
    /// Whether the row rests on an assumption: some conjunct is backed only
    /// by the fact's evidence and was not re-derived.
    #[must_use]
    pub fn is_assumption(&self) -> bool {
        !self.assumed.is_empty()
    }
}

/// The assumptions a module was admitted under: one row per admitted
/// `BoxDeref` instruction, in function / block / instruction order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoxDerefManifest {
    /// The floor the rows were admitted at.
    pub floor: BoxValidityFloor,
    pub rows: Vec<BoxDerefManifestRow>,
}

impl BoxDerefManifest {
    /// The label a policy-level report carries for a module admitted with
    /// these rows. Admission can precede a later lowering or object-emission
    /// failure, so this deliberately makes no claim that code was compiled.
    #[must_use]
    pub fn disclosure(&self) -> Option<String> {
        let assumed: Vec<&BoxDerefManifestRow> =
            self.rows.iter().filter(|row| row.is_assumption()).collect();
        if assumed.is_empty() {
            return None;
        }
        let mut by_root = std::collections::BTreeMap::<&'static str, usize>::new();
        for row in &assumed {
            *by_root.entry(row.root.name()).or_default() += 1;
        }
        let roots = by_root
            .iter()
            .map(|(root, count)| format!("{root} x{count}"))
            .collect::<Vec<_>>()
            .join(", ");
        Some(format!(
            "admitted for compilation under named assumptions: Box validity at {} \
             instruction(s) is assumed for admission, not established ({roots}; standing: \
             safe_body, sound_callees, box_unique)",
            assumed.len()
        ))
    }
}

/// One module admitted under named assumptions, as a license policy recorded
/// it: the module's name and exactly what [`admit_box_derefs`] returned.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoxDerefDisclosureRecord {
    /// `Module::name` of the admitted module.
    pub module: String,
    /// The assumptions it was admitted under (never empty).
    pub manifest: BoxDerefManifest,
}

/// Where a compile under [`BoxValidityFloor::NamedPremise`] reports what it
/// assumed (section 28 clause 2: a premise is carried AND reported).
///
/// The caller that opts into the floor creates one and hands it to
/// [`crate::CodegenLicensePolicy::with_named_premise_box_floor`], the only
/// way to select that floor. Every license verdict that admits a module
/// holding a `BoxDeref` records the manifest here before it returns, so the
/// report reaches the caller on every entry that takes a license, whatever
/// that entry's own result type carries. Clones share one record list.
///
/// Equality is identity (two handles are equal when they share a list): a
/// policy compares equal to its clone, never to a policy reporting elsewhere.
#[derive(Debug, Clone, Default)]
pub struct BoxDerefDisclosure {
    records: std::sync::Arc<std::sync::Mutex<Vec<BoxDerefDisclosureRecord>>>,
}

impl PartialEq for BoxDerefDisclosure {
    fn eq(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.records, &other.records)
    }
}

impl Eq for BoxDerefDisclosure {}

impl BoxDerefDisclosure {
    /// An empty report.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, Vec<BoxDerefDisclosureRecord>> {
        // A panic while the list was held leaves complete records behind
        // (each push is one whole record); keep reporting them.
        self.records
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    /// Record one admission. A manifest with no assumed row (a module
    /// holding no `BoxDeref`, or only wholly re-derived ones) assumed nothing
    /// and is not recorded; a verdict repeated for the same module (a license
    /// is consulted more than once per compile) is recorded once.
    pub(crate) fn record(&self, module: &Module, manifest: &BoxDerefManifest) {
        if !manifest.rows.iter().any(BoxDerefManifestRow::is_assumption) {
            return;
        }
        let record = BoxDerefDisclosureRecord {
            module: module.name.clone(),
            manifest: manifest.clone(),
        };
        let mut records = self.lock();
        if !records.contains(&record) {
            records.push(record);
        }
    }

    /// Every admission recorded so far, in first-admission order.
    #[must_use]
    pub fn records(&self) -> Vec<BoxDerefDisclosureRecord> {
        self.lock().clone()
    }

    /// Whether any module admission observed a named assumption.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.lock().is_empty()
    }

    /// The label each recorded module's report must carry
    /// ([`BoxDerefManifest::disclosure`]), prefixed with the module's name.
    #[must_use]
    pub fn lines(&self) -> Vec<String> {
        self.lock()
            .iter()
            .filter_map(|record| {
                record
                    .manifest
                    .disclosure()
                    .map(|line| format!("module `{}`: {line}", record.module))
            })
            .collect()
    }
}

/// Whether `func` holds a `BoxDeref`.
#[must_use]
pub fn function_has_box_deref(func: &Function) -> bool {
    func.blocks
        .iter()
        .flat_map(|block| &block.body)
        .any(|node| matches!(node.inst, Inst::BoxDeref { .. }))
}

/// Whether `module` holds a `BoxDeref`.
#[must_use]
pub fn module_has_box_deref(module: &Module) -> bool {
    module.functions.iter().any(function_has_box_deref)
}

/// The refusal of the first `BoxDeref` of `func`, for an entry that holds a
/// function and no module: the fact's rules read the module (the pointee's
/// layout on its target, the function's parameters and allocations), so
/// without one nothing was checked and nothing is admitted.
pub fn refuse_box_deref_without_module(func: &Function) -> Result<(), AdapterError> {
    for block in &func.blocks {
        for (inst_index, node) in block.body.iter().enumerate() {
            if matches!(node.inst, Inst::BoxDeref { .. }) {
                return Err(AdapterError::BoxDerefNotAdmitted {
                    function: func.name.clone(),
                    block: block.id.index(),
                    inst_index: inst_index as u32,
                    reason: BoxDerefRefusal::NoModule,
                });
            }
        }
    }
    Ok(())
}

/// THE acceptance check: every `BoxDeref` of `module` is admitted at `floor`,
/// or the first one that is not is refused by name.
///
/// A module with no `BoxDeref` returns an empty manifest without running
/// anything. Otherwise trust-ir's codegen admission runs with the floor's
/// tier; a structural finding about a fact (rules 1 to 9) is reported before
/// a floor finding, each in trust-ir's function / block / instruction order.
/// Findings about anything else are not this function's to decide and are
/// left to the entry that called it.
///
/// On success the manifest has exactly one row per `BoxDeref` instruction.
pub fn admit_box_derefs(
    module: &Module,
    floor: BoxValidityFloor,
) -> Result<BoxDerefManifest, AdapterError> {
    if !module_has_box_deref(module) {
        return Ok(BoxDerefManifest {
            floor,
            rows: Vec::new(),
        });
    }
    // The pinned admission as it stands. Its other findings (a claim-less
    // body, an unrecognized gate) are the license policy's verdicts and are
    // not read here: only the Box findings below are, and trust-ir reports
    // them whatever else it found.
    let admission = admission_at(trust_ir_build::CodegenAdmission::pinned(), floor);
    let findings = trust_ir_build::validate_module_for_codegen_with(module, &admission);
    if let Some(refusal) = findings.iter().find_map(fact_rule_refusal) {
        return Err(refusal);
    }
    // At a floor that consults it, a floor finding stands unless this
    // backend re-derives its conjunct; the refusal of one that stands says
    // why the re-derivation did not. At `Refuse` every floor finding stands
    // exactly as trust-ir reported it.
    let mut rederiver = ModuleRederiver::new(module);
    if let Some(refusal) = findings
        .iter()
        .find_map(|error| floor_refusal_explained(&mut rederiver, floor, error))
    {
        return Err(refusal);
    }
    let mut rows = Vec::new();
    for (function, func) in module.functions.iter().enumerate() {
        for block in &func.blocks {
            for (inst_index, node) in block.body.iter().enumerate() {
                let Inst::BoxDeref { fact, .. } = &node.inst else {
                    continue;
                };
                let rederived: Vec<ValidityConjunct> = if floor.rederives() {
                    rederiver
                        .rederive(function, block.id, inst_index)
                        .map(|rederivation| rederivation.established_conjuncts())
                        .unwrap_or_default()
                } else {
                    Vec::new()
                };
                let tier = fact
                    .evidence
                    .iter()
                    .map(|entry| entry.evidence.tier())
                    .min();
                // In the fact's own (canonical, rule-checked) order.
                let mut assumed: Vec<ValidityConjunct> = Vec::new();
                for entry in &fact.evidence {
                    if entry.evidence.tier() < BoxValidityTier::ConsumerRederived
                        && !rederived.contains(&entry.conjunct)
                        && !assumed.contains(&entry.conjunct)
                    {
                        assumed.push(entry.conjunct);
                    }
                }
                let (Some(root), Some(tier)) = (fact.premise_root(), tier) else {
                    return Err(AdapterError::BoxDerefNotAdmitted {
                        function: func.name.clone(),
                        block: block.id.index(),
                        inst_index: inst_index as u32,
                        reason: BoxDerefRefusal::NoManifestRow,
                    });
                };
                rows.push(BoxDerefManifestRow {
                    function: func.name.clone(),
                    block: block.id.index(),
                    inst_index: inst_index as u32,
                    site: fact.site,
                    root,
                    tier,
                    rederived,
                    assumed,
                });
            }
        }
    }
    Ok(BoxDerefManifest { floor, rows })
}

/// `admission` holding `Inst::BoxDeref` to `floor`. The one place a
/// [`BoxValidityFloor`] becomes trust-ir's knob, used by [`admit_box_derefs`]
/// and by the two entries that already run trust-ir's admission for their
/// own findings (`validate_codegen_prerequisites`, `ingest::admission_findings`)
/// and classify the Box findings through [`refusal_of_finding`].
#[must_use]
pub(crate) fn admission_at<'a>(
    admission: trust_ir_build::CodegenAdmission<'a>,
    floor: BoxValidityFloor,
) -> trust_ir_build::CodegenAdmission<'a> {
    admission.with_require_box_validity_evidence(Some(floor.tier()))
}

/// The typed refusal of one trust-ir finding, when the finding is about a
/// `BoxDeref` (a rule of its fact, or the evidence floor), for an entry that
/// read trust-ir's findings at `floor`. The classifier every entry shares;
/// `None` for a finding about anything else, and for a floor finding `floor`
/// discharges.
pub(crate) fn refusal_of_finding(
    module: &Module,
    floor: BoxValidityFloor,
    error: &trust_ir_build::ValidationError,
) -> Option<AdapterError> {
    fact_rule_refusal(error)
        .or_else(|| floor_refusal_explained(&mut ModuleRederiver::new(module), floor, error))
}

/// trust-ir's structural verdict on a fact, as this backend's typed refusal.
/// Lists every `BoxDeref*` rule variant of the pinned validator; the
/// must-refuse corpus has a row per rule, so a rule a later pin adds and this
/// list lacks fails `must_refuse_corpus` by name.
fn fact_rule_refusal(error: &trust_ir_build::ValidationError) -> Option<AdapterError> {
    use trust_ir_build::BoxDerefValidationRule as R;
    use trust_ir_build::ValidationError as V;
    let rule = error.box_deref_rule()?;
    let (function, block, inst_index, rule_name) = match rule {
        R::TypeMismatch => {
            let V::BoxDerefTypeMismatch {
                function,
                block,
                inst_index,
                ..
            } = error
            else {
                unreachable!("typed BoxDeref rule disagrees with its validation error")
            };
            (function, block, inst_index, "BoxDerefTypeMismatch")
        }
        R::PointeeOutOfScope => {
            let V::BoxDerefPointeeOutOfScope {
                function,
                block,
                inst_index,
                ..
            } = error
            else {
                unreachable!("typed BoxDeref rule disagrees with its validation error")
            };
            (function, block, inst_index, "BoxDerefPointeeOutOfScope")
        }
        R::ConjunctCover => {
            let V::BoxDerefConjunctCover {
                function,
                block,
                inst_index,
                ..
            } = error
            else {
                unreachable!("typed BoxDeref rule disagrees with its validation error")
            };
            (function, block, inst_index, "BoxDerefConjunctCover")
        }
        R::ConjunctUnestablished => {
            let V::BoxDerefConjunctUnestablished {
                function,
                block,
                inst_index,
                ..
            } = error
            else {
                unreachable!("typed BoxDeref rule disagrees with its validation error")
            };
            (function, block, inst_index, "BoxDerefConjunctUnestablished")
        }
        R::PremiseNotPinned => {
            let V::BoxDerefPremiseNotPinned {
                function,
                block,
                inst_index,
                ..
            } = error
            else {
                unreachable!("typed BoxDeref rule disagrees with its validation error")
            };
            (function, block, inst_index, "BoxDerefPremiseNotPinned")
        }
        R::SessionRefused => {
            let V::BoxDerefSessionRefused {
                function,
                block,
                inst_index,
                ..
            } = error
            else {
                unreachable!("typed BoxDeref rule disagrees with its validation error")
            };
            (function, block, inst_index, "BoxDerefSessionRefused")
        }
        R::DominatingCheckInvalid => {
            let V::BoxDerefDominatingCheckInvalid {
                function,
                block,
                inst_index,
                ..
            } = error
            else {
                unreachable!("typed BoxDeref rule disagrees with its validation error")
            };
            (
                function,
                block,
                inst_index,
                "BoxDerefDominatingCheckInvalid",
            )
        }
        R::ObligationUnbound => {
            let V::BoxDerefObligationUnbound {
                function,
                block,
                inst_index,
                ..
            } = error
            else {
                unreachable!("typed BoxDeref rule disagrees with its validation error")
            };
            (function, block, inst_index, "BoxDerefObligationUnbound")
        }
        R::NonClaimsNotPinned => {
            let V::BoxDerefNonClaimsNotPinned {
                function,
                block,
                inst_index,
            } = error
            else {
                unreachable!("typed BoxDeref rule disagrees with its validation error")
            };
            (function, block, inst_index, "BoxDerefNonClaimsNotPinned")
        }
        R::PremiseContradicted => {
            let V::BoxDerefPremiseContradicted {
                function,
                block,
                inst_index,
                ..
            } = error
            else {
                unreachable!("typed BoxDeref rule disagrees with its validation error")
            };
            (function, block, inst_index, "BoxDerefPremiseContradicted")
        }
        // The evidence-floor finding has a different refusal payload and is
        // classified by `floor_refusal` below. Naming it here keeps this
        // match exhaustive: a new TrustIR Box rule cannot silently fall
        // through the non-exhaustive `ValidationError` wildcard.
        R::EvidenceBelowFloor => return None,
    };
    Some(AdapterError::BoxDerefNotAdmitted {
        function: function.clone(),
        block: *block,
        inst_index: *inst_index,
        reason: BoxDerefRefusal::FactRefused {
            rule: rule_name,
            finding: error.to_string(),
        },
    })
}

/// The conjunct of a trust-ir floor finding and this backend's
/// re-derivation of its instruction, or `None` for any other finding and for
/// one whose function is not named by exactly one function of the module (a
/// finding is never matched to a guessed body).
fn rederivation_for_finding(
    rederiver: &mut ModuleRederiver<'_>,
    error: &trust_ir_build::ValidationError,
) -> Option<(ValidityConjunct, crate::box_deref_rederive::Rederivation)> {
    let trust_ir_build::ValidationError::BoxValidityEvidenceBelowFloor {
        function,
        block,
        inst_index,
        conjunct,
        ..
    } = error
    else {
        return None;
    };
    let conjunct = ValidityConjunct::from_name(conjunct)?;
    let mut named = rederiver
        .module()
        .functions
        .iter()
        .enumerate()
        .filter(|(_, func)| func.name == *function)
        .map(|(index, _)| index);
    let (Some(index), None) = (named.next(), named.next()) else {
        return None;
    };
    let rederivation = rederiver.rederive(
        index,
        BlockId::new(*block),
        usize::try_from(*inst_index).ok()?,
    )?;
    Some((conjunct, rederivation))
}

/// Whether `error` is a trust-ir floor finding that `floor` discharges: the
/// floor consults this backend's re-derivation
/// ([`BoxValidityFloor::rederives`]; `Refuse` never does) and the
/// re-derivation establishes the finding's conjunct from the instruction's
/// own function. The one predicate every entry that reads trust-ir's
/// findings applies before it classifies them ([`admit_box_derefs`],
/// `validate_codegen_prerequisites`, `ingest::admission_findings`), each
/// with the floor it read them at and one [`ModuleRederiver`] for all of
/// them: a discharged finding is not a refusal, and every other finding is
/// left exactly as trust-ir reported it.
#[must_use]
pub(crate) fn discharged_by_rederivation(
    rederiver: &mut ModuleRederiver<'_>,
    floor: BoxValidityFloor,
    error: &trust_ir_build::ValidationError,
) -> bool {
    floor.rederives()
        && rederivation_for_finding(rederiver, error)
            .is_some_and(|(conjunct, rederivation)| rederivation.established(conjunct))
}

/// trust-ir's floor verdict, as this backend's typed refusal, unless `floor`
/// consults the re-derivation and it establishes the finding's conjunct
/// (then `None`: discharged). At such a floor a refusal that stands carries
/// the re-derivation's reason; at `Refuse` it is trust-ir's verdict
/// unchanged. Every entry classifies a floor finding through this one
/// function, so the refusal text is the same on every target.
fn floor_refusal_explained(
    rederiver: &mut ModuleRederiver<'_>,
    floor: BoxValidityFloor,
    error: &trust_ir_build::ValidationError,
) -> Option<AdapterError> {
    let mut refusal = floor_refusal(error)?;
    if !floor.rederives() {
        return Some(refusal);
    }
    if let Some((conjunct, rederivation)) = rederivation_for_finding(rederiver, error) {
        let Err(why) = rederivation.verdict(conjunct) else {
            return None;
        };
        if let AdapterError::BoxDerefNotAdmitted {
            reason: BoxDerefRefusal::EvidenceBelowFloor { not_rederived, .. },
            ..
        } = &mut refusal
        {
            *not_rederived = Some(why.reason());
        }
    }
    Some(refusal)
}

/// trust-ir's floor verdict, as this backend's typed refusal.
fn floor_refusal(error: &trust_ir_build::ValidationError) -> Option<AdapterError> {
    let trust_ir_build::ValidationError::BoxValidityEvidenceBelowFloor {
        function,
        block,
        inst_index,
        conjunct,
        tier,
        floor,
    } = error
    else {
        return None;
    };
    Some(AdapterError::BoxDerefNotAdmitted {
        function: function.clone(),
        block: *block,
        inst_index: *inst_index,
        reason: BoxDerefRefusal::EvidenceBelowFloor {
            conjunct,
            tier,
            floor,
            not_rederived: None,
        },
    })
}
