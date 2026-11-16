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
//! The verdict is trust-ir's, never this crate's: the structural rules of the
//! carried fact (rules 1 to 9) and the evidence floor are read from
//! `trust_ir_build::validate_module_for_codegen_with` under
//! `CodegenAdmission::with_require_box_validity_evidence`. This module
//! classifies those findings as one typed refusal
//! ([`AdapterError::BoxDerefNotAdmitted`]) and writes the manifest.
//!
//! # The two floors
//!
//! [`BoxValidityFloor`] has two values and no spelling for anything weaker:
//!
//! - [`BoxValidityFloor::Refuse`] (the default of every policy): trust-ir's
//!   `ConsumerRederived` floor. No evidence kind of the pinned format reaches
//!   it, so every `BoxDeref` is refused. This is the proof-required answer:
//!   a named premise is not evidence a proof lane may rest on.
//! - [`BoxValidityFloor::NamedPremise`]: trust-ir's `NamedPremise` floor. A
//!   consumer opts in by name and only by handing over the place the
//!   assumptions are reported
//!   ([`crate::CodegenLicensePolicy::with_named_premise_box_floor`], which
//!   takes a [`BoxDerefDisclosure`]): there is no way to select this floor
//!   without one, so every entry that admits under it reports to its caller.
//!   It admits a fact whose every conjunct is a premise on a root the format
//!   classes as a named premise, and refuses the assumed roots
//!   (`returned_box_assumed`, `reference_arg_box_valid`) and both reserved
//!   evidence kinds.
//!
//! The shared floor, which has no policy in scope, checks every module at
//! [`BoxValidityFloor::MOST_PERMISSIVE`]: nothing below trust-ir's
//! `NamedPremise` floor is admitted on any path, whatever a policy says.
//!
//! # What an admitted instruction licenses
//!
//! Nothing. An admitted `BoxDeref` is lowered as the pointer-preserving copy
//! it is. The fact is a named assumption: it is validated, counted in the
//! manifest and reported, and no pass or lowering may use it, or the
//! instruction's undefined behaviour, to remove a check or a branch or to
//! move or introduce a memory access (section 28, "No licence from the
//! undefined behaviour"). The manifest is evidence of what was assumed, not
//! of validity.

use trust_ir::box_validity::{BoxDerefSite, BoxValidityTier, PremiseRoot};
use trust_ir::{Function, Inst, Module};

use crate::adapter::AdapterError;

/// The evidence floor a consumer holds `Inst::BoxDeref` to. Ordered most
/// restrictive first; there is no value below trust-ir's `NamedPremise`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub enum BoxValidityFloor {
    /// Refuse every `BoxDeref` (trust-ir's `ConsumerRederived` floor). The
    /// default, and the only floor a proof-required lane may use.
    #[default]
    Refuse,
    /// Admit a fact whose every conjunct rests on a named premise (trust-ir's
    /// `NamedPremise` floor). Opt-in; the diagnostic lane's floor.
    NamedPremise,
}

impl BoxValidityFloor {
    /// The weakest floor any path of this backend applies: the bound the
    /// policy-free shared floor checks every module against.
    pub const MOST_PERMISSIVE: Self = Self::NamedPremise;

    /// The trust-ir tier this floor is.
    #[must_use]
    pub const fn tier(self) -> BoxValidityTier {
        match self {
            Self::Refuse => BoxValidityTier::ConsumerRederived,
            Self::NamedPremise => BoxValidityTier::NamedPremise,
        }
    }

    /// The diagnostic spelling: trust-ir's name of the tier.
    #[must_use]
    pub const fn name(self) -> &'static str {
        self.tier().name()
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
            } => write!(
                f,
                "conjunct {conjunct} is backed at tier {tier}, below this lane's Box validity \
                 floor {floor}"
            ),
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
    /// The fact's weakest evidence tier.
    pub tier: BoxValidityTier,
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
        if self.rows.is_empty() {
            return None;
        }
        let mut by_root = std::collections::BTreeMap::<&'static str, usize>::new();
        for row in &self.rows {
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
            self.rows.len()
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

    /// Record one admission. A manifest with no row (a module holding no
    /// `BoxDeref`) assumed nothing and is not recorded; a verdict repeated
    /// for the same module (a license is consulted more than once per
    /// compile) is recorded once.
    pub(crate) fn record(&self, module: &Module, manifest: &BoxDerefManifest) {
        if manifest.rows.is_empty() {
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
    if let Some(refusal) = findings.iter().find_map(floor_refusal) {
        return Err(refusal);
    }
    let mut rows = Vec::new();
    for func in &module.functions {
        for block in &func.blocks {
            for (inst_index, node) in block.body.iter().enumerate() {
                let Inst::BoxDeref { fact, .. } = &node.inst else {
                    continue;
                };
                let (Some(root), Some(tier)) = (fact.premise_root(), fact.weakest_tier()) else {
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
/// `BoxDeref` (a rule of its fact, or the evidence floor). The classifier
/// every entry shares; `None` for a finding about anything else.
pub(crate) fn refusal_of_finding(error: &trust_ir_build::ValidationError) -> Option<AdapterError> {
    fact_rule_refusal(error).or_else(|| floor_refusal(error))
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
        },
    })
}
