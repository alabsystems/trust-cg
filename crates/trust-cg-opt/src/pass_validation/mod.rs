// trust-cg-opt - Per-pass translation validation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Per-pass translation validation for the AArch64 machine-IR pipeline.
//!
//! A pass run is validated by comparing the function before the run with the
//! function after it, with a check chosen for the kind of rewrite the pass
//! performs. The checks are computed from the two functions alone: none of
//! them reuses the pass's own analysis.
//!
//! | Validator | Passes | Shown |
//! |-----------|--------|-------|
//! | [`ValidatorKind::DependencePreservation`] | the list schedulers | the output is a per-block permutation of unchanged instructions, and every register, NZCV, memory, side-effect, barrier and pre-allocation fixed-register dependence of the input order holds in the output order |
//! | [`ValidatorKind::SymbolicRegionEquivalence`] | `mem-pair-formation`, the if-conversion family | every changed acyclic single-entry region computes the same values, memory, effects and control decisions at its exits (symbolic evaluation), and executes no load on a path where the input did not |
//! | [`ValidatorKind::HoistConditions`] | `licm` | each moved instruction meets the code-motion side conditions (invariant operands, a single in-loop definition not live into the loop, no in-loop or later preheader memory writer for a load other than a bounded access to a different fixed stack slot, guaranteed execution or an in-bounds frame access for anything that can fault, and no exception edge of an invoke target that skips it on the way to the source or reaches a landing pad reading it), or for a pure value a move to any dominating block no reader can tell apart, and nothing else changed |
//!
//! A validation verdict is evidence about one pass run under the validator's
//! machine model ([`ValidationVerdict`]). It is a translation-validation
//! check, not a proof of the pass, and it inherits the shared operand-role
//! and memory-effect tables (`crate::effects`) as its description of each
//! opcode.
//!
//! # Policy
//!
//! [`PassValidationPolicy`] says what a failed or missing validation does,
//! and [`PassValidationScope`] which validators run: the default diagnostic
//! runs only the schedulers' validator, which needs no copy of the function
//! (+0.5% to +0.8% instructions retired on the compile corpus at
//! `bc4be093d` and `ec6c90504`), while the dedicated tier copies the function before each
//! covered pass (+5.0% to +8.0%; every proof-grade compile, the rustc
//! bridge's default route included, pays it). The optimizer only records verdicts in
//! [`PassValidationSummary`]; the caller (the codegen pipeline) decides
//! whether a recorded failure refuses the compile
//! ([`PassValidationSummary::first_refusal`]).
//!
//! # Transitions
//!
//! A caller that composes a function's stage checks into one transition
//! chain (trust-cg-codegen's composed transition record, ledger L09-P3)
//! passes a [`FunctionInterfaceDigest`]: every pass run then records the
//! function's interface digest before and after, and a run that changed the
//! interface becomes a [`PassTransition`] carrying that run's verdict. Under
//! transitions every run is validated for the record, by its dedicated
//! validator or else by the generic symbolic region check, even where the
//! scope would not run one; such a composition-only verdict goes into the
//! transition alone, and the summary's counters and the policy's refusals
//! stay exactly what the scope alone produces. A run that reported no change
//! but altered the interface is a refuted transition.

mod dependence;
mod hoist;
mod region;
mod semantics;
mod term;

use std::hash::{Hash, Hasher};

use serde::{Deserialize, Serialize};
use trust_cg_ir::{MachFunction, MachInst, MachOperand};

pub use dependence::{PermutationSnapshot, validate_permutation};

/// What a failed or missing validation does.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum PassValidationPolicy {
    /// No validation runs and nothing is recorded.
    Off,
    /// Validators run and every verdict is recorded; nothing is refused.
    #[default]
    Diagnostic,
    /// A covered pass run whose validation did not succeed refuses the
    /// compile. A changed run of a pass with no validator is recorded as
    /// uncovered.
    Enforce,
    /// [`Self::Enforce`], and a changed run of a pass with no validator
    /// refuses the compile as well.
    RequireCoverage,
}

impl PassValidationScope {
    /// Stable lowercase spelling used by diagnostics and the environment
    /// control.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Schedulers => "schedulers",
            Self::Dedicated => "dedicated",
            Self::AllPasses => "all",
        }
    }

    /// The wider of two scopes.
    pub fn widest(self, other: Self) -> Self {
        fn rank(scope: PassValidationScope) -> u8 {
            match scope {
                PassValidationScope::Schedulers => 0,
                PassValidationScope::Dedicated => 1,
                PassValidationScope::AllPasses => 2,
            }
        }
        if rank(other) > rank(self) {
            other
        } else {
            self
        }
    }

    /// Parse [`Self::as_str`]'s spelling.
    pub fn parse(text: &str) -> Option<Self> {
        match text.trim() {
            "schedulers" => Some(Self::Schedulers),
            "dedicated" => Some(Self::Dedicated),
            "all" => Some(Self::AllPasses),
            _ => None,
        }
    }
}

impl PassValidationPolicy {
    /// Stable lowercase spelling used by diagnostics and the environment
    /// control.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::Diagnostic => "diagnostic",
            Self::Enforce => "enforce",
            Self::RequireCoverage => "require-coverage",
        }
    }

    /// Parse [`Self::as_str`]'s spelling.
    pub fn parse(text: &str) -> Option<Self> {
        match text.trim() {
            "off" => Some(Self::Off),
            "diagnostic" => Some(Self::Diagnostic),
            "enforce" => Some(Self::Enforce),
            "require-coverage" => Some(Self::RequireCoverage),
            _ => None,
        }
    }

    /// Whether validators run at all.
    pub fn is_active(self) -> bool {
        self != Self::Off
    }

    /// The stricter of two policies.
    pub fn strongest(self, other: Self) -> Self {
        fn rank(policy: PassValidationPolicy) -> u8 {
            match policy {
                PassValidationPolicy::Off => 0,
                PassValidationPolicy::Diagnostic => 1,
                PassValidationPolicy::Enforce => 2,
                PassValidationPolicy::RequireCoverage => 3,
            }
        }
        if rank(other) > rank(self) {
            other
        } else {
            self
        }
    }
}

/// Which validators a pipeline attempts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum PassValidationScope {
    /// Only the dependence-preservation validator (the schedulers), which
    /// needs no copy of the function: the default diagnostic. Every other
    /// changed pass run is recorded as uncovered.
    #[default]
    Schedulers,
    /// Only passes with a dedicated validator ([`dedicated_validator`]):
    /// what proof-grade and certified pipelines run at least. Every other
    /// changed pass run is recorded as uncovered.
    Dedicated,
    /// Every pass: the dedicated validator where one exists, otherwise the
    /// generic symbolic region check, plus an unchanged-claim check of every
    /// run that reported no change. Measurement and coverage mode.
    AllPasses,
}

/// Validation configuration for one optimization pipeline.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub struct PassValidationConfig {
    /// What a failed or missing validation does.
    pub policy: PassValidationPolicy,
    /// Which validators run.
    pub scope: PassValidationScope,
}

impl PassValidationConfig {
    /// Validation disabled.
    pub const fn off() -> Self {
        Self {
            policy: PassValidationPolicy::Off,
            scope: PassValidationScope::Dedicated,
        }
    }

    /// The default: the schedulers' dependence validator, recorded but never
    /// refusing (the cheap tier; see [`PassValidationScope::Schedulers`]).
    pub const fn diagnostic() -> Self {
        Self {
            policy: PassValidationPolicy::Diagnostic,
            scope: PassValidationScope::Schedulers,
        }
    }

    /// Dedicated validators whose failures refuse the compile.
    pub const fn enforce() -> Self {
        Self {
            policy: PassValidationPolicy::Enforce,
            scope: PassValidationScope::Dedicated,
        }
    }

    /// Replace the scope (builder).
    pub const fn with_scope(mut self, scope: PassValidationScope) -> Self {
        self.scope = scope;
        self
    }
}

/// The check a pass run was validated with.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ValidatorKind {
    /// The output is a per-block permutation of unchanged instructions that
    /// keeps every dependence of the input order.
    DependencePreservation,
    /// Symbolic equivalence of every changed acyclic single-entry region.
    SymbolicRegionEquivalence,
    /// Code-motion side conditions of every moved instruction.
    HoistConditions,
    /// A run that reported no change left the function unchanged.
    UnchangedClaim,
    /// Value-flow comparison of the post-allocation stages with their input
    /// (`trust_cg_verify::post_ra_value_flow`): the codegen pipeline records
    /// it once per function (`post-ra-value-flow`), or per stage boundary
    /// when split.
    PostAllocationValueFlow,
}

impl ValidatorKind {
    /// Stable spelling used in diagnostics and records.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::DependencePreservation => "dependence-preservation",
            Self::SymbolicRegionEquivalence => "symbolic-region-equivalence",
            Self::HoistConditions => "hoist-conditions",
            Self::UnchangedClaim => "unchanged-claim",
            Self::PostAllocationValueFlow => "post-allocation-value-flow",
        }
    }
}

/// The dedicated validator of an AArch64 pass, by [`crate::MachinePass::name`].
pub fn dedicated_validator(pass_name: &str) -> Option<ValidatorKind> {
    match pass_name {
        "instruction-scheduler" | "pressure-aware-scheduler" => {
            Some(ValidatorKind::DependencePreservation)
        }
        "mem-pair-formation" | "if-convert" | "late-boolean-diamond" | "tiny-loop-diamond" => {
            Some(ValidatorKind::SymbolicRegionEquivalence)
        }
        "licm" => Some(ValidatorKind::HoistConditions),
        // The post-allocation stage boundaries the codegen pipeline compares
        // (never an optimizer pass).
        "post-ra-allocation" | "post-ra-frame-layout" | "post-ra-value-flow" => {
            Some(ValidatorKind::PostAllocationValueFlow)
        }
        _ => None,
    }
}

/// What one validation concluded.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "verdict", content = "reason")]
pub enum ValidationVerdict {
    /// Preservation was shown under the validator's model.
    Validated,
    /// The validator found a definite violation of its model. Only the
    /// checks that decide their model exactly report it: the dependence
    /// validator (a reversed dependence, a dropped, added or rewritten
    /// instruction) and the unchanged-claim check (a run that reported no
    /// change altered the function).
    Refuted(String),
    /// The validator could not show preservation. The symbolic region and
    /// code-motion checks report every failure this way, because their
    /// comparison (syntactic equality of normalized terms) does not separate
    /// "different" from "not shown equal": an unmodeled construct, two
    /// computations it could not prove equal, and a genuine violation (a
    /// speculated load, an unmatched effect) all land here. So it is not by
    /// itself evidence of a miscompile, and not evidence of preservation
    /// either; the one miscompile these checks found (mem-pair formation
    /// pairing a load ahead of its guard) was reported as unproved.
    Unproved(String),
    /// The pass changed the function and no validator covers it.
    Uncovered,
}

impl ValidationVerdict {
    /// Whether this verdict shows preservation.
    pub fn is_validated(&self) -> bool {
        matches!(self, Self::Validated)
    }

    /// Stable lowercase spelling.
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Validated => "validated",
            Self::Refuted(_) => "refuted",
            Self::Unproved(_) => "unproved",
            Self::Uncovered => "uncovered",
        }
    }

    /// The reason text of a refuted or unproved verdict.
    pub fn reason(&self) -> Option<&str> {
        match self {
            Self::Refuted(reason) | Self::Unproved(reason) => Some(reason),
            Self::Validated | Self::Uncovered => None,
        }
    }
}

/// One pass run's validation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PassValidationRecord {
    /// [`crate::MachinePass::name`] of the validated run.
    pub pass_name: String,
    /// Function the pass ran on.
    pub function_name: String,
    /// The check used; `None` for an uncovered run.
    pub validator: Option<ValidatorKind>,
    /// The conclusion.
    pub verdict: ValidationVerdict,
}

/// The digest of a machine function's interface, supplied by a caller that
/// records [`PassTransition`]s (trust-cg-verify's composed transition owner
/// hashes [`hash_function_interface`] with SHA-256). It must be a pure
/// function of the fields [`hash_function_interface`] feeds.
pub type FunctionInterfaceDigest = fn(&MachFunction) -> [u8; 32];

/// One run of a mutating step that changed the function's interface, recorded
/// when the caller asked for transitions ([`PassValidationSummary::transitions`]).
///
/// `before` and `after` are the caller's [`FunctionInterfaceDigest`] of the
/// function as the run received it and as it left it. The verdict is the
/// run's validation under its validator's model, or
/// [`ValidationVerdict::Uncovered`] when no validator ran;
/// a run that reported no change but altered the interface is
/// [`ValidationVerdict::Refuted`] under [`ValidatorKind::UnchangedClaim`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PassTransition {
    /// [`crate::MachinePass::name`] of the run, or the step's name.
    pub pass_name: String,
    /// What the run reported.
    pub reported_change: bool,
    /// Interface digest of the function the run received.
    pub before: [u8; 32],
    /// Interface digest of the function the run left.
    pub after: [u8; 32],
    /// The check the verdict came from; `None` for an uncovered run.
    pub validator: Option<ValidatorKind>,
    /// The run's verdict.
    pub verdict: ValidationVerdict,
}

/// Per-pass validation counters.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct PassValidationCounts {
    /// Pass name.
    pub pass_name: String,
    /// Runs that reported a change.
    pub changed_runs: u32,
    /// Changed runs shown to preserve semantics.
    pub validated: u32,
    /// Runs with a definite violation (changed, or an unchanged-claim
    /// violation).
    pub refuted: u32,
    /// Changed runs the validator could not show.
    pub unproved: u32,
    /// Changed runs no validator covers.
    pub uncovered: u32,
    /// Unchanged runs whose no-change claim was checked.
    pub unchanged_checked: u32,
}

/// The most failure records a summary keeps; counters stay exact.
pub const MAX_RECORDED_FAILURES: usize = 64;

/// Validation outcome of one or more pipeline runs.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct PassValidationSummary {
    /// The configuration the verdicts were produced under.
    pub config: PassValidationConfig,
    /// Counters per pass, in first-seen order.
    pub passes: Vec<PassValidationCounts>,
    /// Every refuted, unproved or uncovered run, up to
    /// [`MAX_RECORDED_FAILURES`]. Past the cap a refuted or unproved record
    /// displaces the latest uncovered one, so the records a refusing policy
    /// acts on are the last to go; [`Self::first_refusal`] refuses from the
    /// exact counters either way.
    pub failures: Vec<PassValidationRecord>,
    /// Failure records dropped past [`MAX_RECORDED_FAILURES`].
    pub dropped_failures: u32,
    /// Instructions the validators examined (before plus after), a
    /// deterministic cost measure.
    pub examined_instructions: u64,
    /// Every run that changed the function's interface, in run order, when
    /// the caller asked for transitions ([`FunctionInterfaceDigest`]);
    /// empty otherwise. Composition-only verdicts live here alone: they
    /// change no counter above and no refusal of the policy.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub transitions: Vec<PassTransition>,
}

impl PassValidationSummary {
    /// An empty summary for `config`.
    pub fn new(config: PassValidationConfig) -> Self {
        Self {
            config,
            ..Self::default()
        }
    }

    fn counts_mut(&mut self, pass_name: &str) -> &mut PassValidationCounts {
        if let Some(index) = self.passes.iter().position(|c| c.pass_name == pass_name) {
            return &mut self.passes[index];
        }
        self.passes.push(PassValidationCounts {
            pass_name: pass_name.to_string(),
            ..PassValidationCounts::default()
        });
        let last = self.passes.len() - 1;
        &mut self.passes[last]
    }

    /// Record one validation.
    pub fn record(&mut self, record: PassValidationRecord, changed: bool) {
        log_record(&record);
        let counts = self.counts_mut(&record.pass_name);
        if changed {
            counts.changed_runs += 1;
        } else {
            counts.unchanged_checked += 1;
        }
        match record.verdict {
            ValidationVerdict::Validated => {
                if changed {
                    counts.validated += 1;
                }
                return;
            }
            ValidationVerdict::Refuted(_) => counts.refuted += 1,
            ValidationVerdict::Unproved(_) => counts.unproved += 1,
            ValidationVerdict::Uncovered => counts.uncovered += 1,
        }
        self.keep_failure(record);
    }

    /// Keep a failure record within [`MAX_RECORDED_FAILURES`], preferring
    /// refuted and unproved records over uncovered ones.
    fn keep_failure(&mut self, record: PassValidationRecord) {
        if self.failures.len() < MAX_RECORDED_FAILURES {
            self.failures.push(record);
            return;
        }
        self.dropped_failures = self.dropped_failures.saturating_add(1);
        if record.verdict.reason().is_some()
            && let Some(index) = self
                .failures
                .iter()
                .rposition(|kept| kept.verdict == ValidationVerdict::Uncovered)
        {
            self.failures.remove(index);
            self.failures.push(record);
        }
    }

    /// Fold another summary (another function or pipeline stage) into this
    /// one. The configuration is kept from `self` unless it is the default.
    pub fn merge(&mut self, other: &PassValidationSummary) {
        if self.passes.is_empty() && self.failures.is_empty() {
            self.config = other.config;
        }
        for counts in &other.passes {
            let mine = self.counts_mut(&counts.pass_name);
            mine.changed_runs += counts.changed_runs;
            mine.validated += counts.validated;
            mine.refuted += counts.refuted;
            mine.unproved += counts.unproved;
            mine.uncovered += counts.uncovered;
            mine.unchanged_checked += counts.unchanged_checked;
        }
        for failure in &other.failures {
            self.keep_failure(failure.clone());
        }
        self.dropped_failures = self.dropped_failures.saturating_add(other.dropped_failures);
        self.examined_instructions = self
            .examined_instructions
            .saturating_add(other.examined_instructions);
        self.transitions.extend(other.transitions.iter().cloned());
    }

    /// Total refuted runs.
    pub fn refuted(&self) -> u32 {
        self.passes.iter().map(|c| c.refuted).sum()
    }

    /// Total unproved runs.
    pub fn unproved(&self) -> u32 {
        self.passes.iter().map(|c| c.unproved).sum()
    }

    /// Total validated changed runs.
    pub fn validated(&self) -> u32 {
        self.passes.iter().map(|c| c.validated).sum()
    }

    /// Total uncovered changed runs.
    pub fn uncovered(&self) -> u32 {
        self.passes.iter().map(|c| c.uncovered).sum()
    }

    /// One certified-pass-chain record for each pass of `function_name` that
    /// a validator covered and that changed it: verified when every changed
    /// run was validated, failed otherwise. Passes no validator covers get no
    /// record (they stay listed as uncovered in the summary).
    ///
    /// The record's local checker is this module's translation validation,
    /// not a proof checker; the chain carries it as evidence of that strength.
    pub fn certified_pass_runs(
        &self,
        function_name: &str,
    ) -> Vec<crate::pass_manager::CertifiedPassRunRecord> {
        use crate::pass_manager::{
            CertifiedPassCheckerRecord, CertifiedPassRunRecord, CertifiedPassRunStatus,
        };
        let mut out = Vec::new();
        for counts in &self.passes {
            let checked = counts.validated + counts.refuted + counts.unproved;
            if counts.changed_runs == 0 || checked == 0 {
                continue;
            }
            let failures: Vec<&PassValidationRecord> = self
                .failures
                .iter()
                .filter(|r| r.pass_name == counts.pass_name && r.verdict.reason().is_some())
                .collect();
            let failed = counts.refuted + counts.unproved;
            let status = if failed == 0 {
                CertifiedPassRunStatus::Verified
            } else {
                CertifiedPassRunStatus::Failed
            };
            let validator = dedicated_validator(&counts.pass_name)
                .unwrap_or(ValidatorKind::SymbolicRegionEquivalence);
            let mut hasher = crate::cache::StableHasher::new();
            hasher.write_str("trust-cg.opt.pass-validation.v1");
            hasher.write_str(function_name);
            hasher.write_str(&counts.pass_name);
            hasher.write_str(validator.as_str());
            for value in [
                counts.changed_runs,
                counts.validated,
                counts.refuted,
                counts.unproved,
                counts.uncovered,
            ] {
                hasher.write_u32(value);
            }
            for failure in &failures {
                hasher.write_str(failure.verdict.reason().unwrap_or(""));
            }
            out.push(CertifiedPassRunRecord {
                format_version: "trust-cg.opt.certified_pass_run.v1".to_string(),
                pass_name: counts.pass_name.clone(),
                pass_version: 1,
                pass_instance_id: format!("pass-validation:{}:v1", counts.pass_name),
                function_name: function_name.to_string(),
                changed: true,
                status,
                certificate_count: counts.validated as usize,
                failure_count: failed as usize,
                obligation_hash: format!(
                    "trust-cg-opt-pass-validation-v1:{:032x}",
                    hasher.finish128()
                ),
                local_checker: CertifiedPassCheckerRecord {
                    kind: "trust-cg-opt-translation-validation".to_string(),
                    name: validator.as_str().to_string(),
                    version: "1".to_string(),
                    status,
                },
                summary: serde_json::json!({
                    "evidence": "translation validation of each changed run (not a proof of the pass)",
                    "validator": validator.as_str(),
                    "changed_runs": counts.changed_runs,
                    "validated": counts.validated,
                    "refuted": counts.refuted,
                    "unproved": counts.unproved,
                    "failures": failures
                        .iter()
                        .map(|r| serde_json::json!({
                            "verdict": r.verdict.as_str(),
                            "reason": r.verdict.reason().unwrap_or(""),
                        }))
                        .collect::<Vec<_>>(),
                }),
            });
        }
        out
    }

    /// The refuted and unproved records kept in [`Self::failures`].
    pub fn refusing_records(&self) -> impl Iterator<Item = &PassValidationRecord> {
        self.failures
            .iter()
            .filter(|record| record.verdict.reason().is_some())
    }

    /// The first record `policy` refuses the compile for, if any.
    ///
    /// [`PassValidationPolicy::Enforce`] refuses every refuted or unproved
    /// run; [`PassValidationPolicy::RequireCoverage`] also refuses uncovered
    /// changed runs. The other policies never refuse.
    ///
    /// The decision is made from the exact per-pass counters, not from the
    /// bounded record list: a kept record is returned when there is one, and
    /// otherwise a record is rebuilt from the counters (its reason says the
    /// run's own record was dropped), so a full record list can never let a
    /// failed run through.
    pub fn first_refusal(&self, policy: PassValidationPolicy) -> Option<PassValidationRecord> {
        let refusing = |counts: &PassValidationCounts| match policy {
            PassValidationPolicy::Off | PassValidationPolicy::Diagnostic => false,
            PassValidationPolicy::Enforce => counts.refuted + counts.unproved > 0,
            PassValidationPolicy::RequireCoverage => {
                counts.refuted + counts.unproved + counts.uncovered > 0
            }
        };
        let counts = self.passes.iter().find(|counts| refusing(counts))?;
        let kept = match policy {
            PassValidationPolicy::Off | PassValidationPolicy::Diagnostic => None,
            PassValidationPolicy::Enforce => self.refusing_records().next(),
            PassValidationPolicy::RequireCoverage => self
                .refusing_records()
                .next()
                .or_else(|| self.failures.first()),
        };
        if let Some(record) = kept {
            return Some(record.clone());
        }
        let reason = format!(
            "{} refuted, {} unproved and {} uncovered run(s) of this pass; their records \
             were dropped past the {MAX_RECORDED_FAILURES} kept",
            counts.refuted, counts.unproved, counts.uncovered
        );
        let (verdict, validator) = if counts.refuted > 0 {
            (
                ValidationVerdict::Refuted(reason),
                dedicated_validator(&counts.pass_name),
            )
        } else if counts.unproved > 0 {
            (
                ValidationVerdict::Unproved(reason),
                dedicated_validator(&counts.pass_name),
            )
        } else {
            (ValidationVerdict::Uncovered, None)
        };
        Some(PassValidationRecord {
            pass_name: counts.pass_name.clone(),
            function_name: String::new(),
            validator,
            verdict,
        })
    }
}

/// Measurement log: with `TRUST_CG_PASS_VALIDATION_LOG=<path>`, every
/// recorded validation is appended to `<path>` as one tab-separated line
/// (`pass`, `validator`, `verdict`, `function`, `reason`). Off by default; it
/// never changes a verdict.
fn log_record(record: &PassValidationRecord) {
    use std::io::Write;
    use std::sync::OnceLock;
    static PATH: OnceLock<Option<std::path::PathBuf>> = OnceLock::new();
    let Some(path) = PATH
        .get_or_init(|| std::env::var_os("TRUST_CG_PASS_VALIDATION_LOG").map(Into::into))
        .as_ref()
    else {
        return;
    };
    let reason: String = record
        .verdict
        .reason()
        .unwrap_or("")
        .chars()
        .map(|c| if c == '\t' || c == '\n' { ' ' } else { c })
        .take(400)
        .collect();
    let line = format!(
        "{}\t{}\t{}\t{}\t{}\n",
        record.pass_name,
        record.validator.map_or("none", ValidatorKind::as_str),
        record.verdict.as_str(),
        record.function_name,
        reason
    );
    if let Ok(mut file) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
    {
        let _ = file.write_all(line.as_bytes());
    }
}

/// Measurement aid: with `TRUST_CG_PASS_VALIDATION_DUMP=<dir>`, every run
/// that was not validated writes its input and output listing to a file in
/// `<dir>`. Off by default; it never changes a verdict.
fn dump_failure(
    record: &PassValidationRecord,
    before: Option<&MachFunction>,
    after: &MachFunction,
) {
    use std::sync::OnceLock;
    use std::sync::atomic::{AtomicU32, Ordering};
    static DIR: OnceLock<Option<std::path::PathBuf>> = OnceLock::new();
    static SEQ: AtomicU32 = AtomicU32::new(0);
    let Some(dir) = DIR
        .get_or_init(|| std::env::var_os("TRUST_CG_PASS_VALIDATION_DUMP").map(Into::into))
        .as_ref()
    else {
        return;
    };
    let listing = |func: &MachFunction| -> String {
        use std::fmt::Write;
        let mut out = String::new();
        for &b in &func.block_order {
            let block = func.block(b);
            let _ = writeln!(
                out,
                "block {} preds {:?} succs {:?}",
                b.0, block.preds, block.succs
            );
            for &id in &block.insts {
                let inst = func.inst(id);
                let _ = writeln!(
                    out,
                    "  {:5} {:?} {:?} flags={:#x} iu={:?} id={:?}",
                    id.0,
                    inst.opcode,
                    inst.operands,
                    inst.flags.bits(),
                    inst.implicit_uses,
                    inst.implicit_defs
                );
            }
        }
        out
    };
    let seq = SEQ.fetch_add(1, Ordering::Relaxed);
    let name: String = format!(
        "{}-{}-{}-{seq}",
        std::process::id(),
        record.pass_name,
        record.function_name
    )
    .chars()
    .map(|c| {
        if c.is_ascii_alphanumeric() || c == '-' || c == '_' {
            c
        } else {
            '_'
        }
    })
    .take(180)
    .collect();
    let text = format!(
        "pass {}\nfunction {}\nverdict {:?}\n\n== before ==\n{}\n== after ==\n{}",
        record.pass_name,
        record.function_name,
        record.verdict,
        before.map(listing).unwrap_or_default(),
        listing(after)
    );
    let _ = std::fs::write(dir.join(format!("{name}.txt")), text);
}

/// The state a validator needs from before a pass run.
pub(crate) enum PassSnapshot {
    /// Block orders and an instruction digest (permutation passes).
    Permutation(PermutationSnapshot),
    /// The whole function and its digest ([`function_digest`]), for the
    /// symbolic checks.
    Function(Box<MachFunction>, u128),
}

/// A behavior digest of `func` ([`function_digest`]): two functions with
/// different digests differ in something a validator reads. For callers
/// that only need to know whether an unvalidated step changed a function
/// (the codegen pipeline's post-allocation branch layout and the opt-in
/// CEGIS superoptimizer, recorded as uncovered when they do).
pub fn function_fingerprint(func: &MachFunction) -> u128 {
    function_digest(func)
}

/// Digest of everything the symbolic validators read: the entry, the layout,
/// every block's instruction list, every instruction's behavior-relevant
/// fields ([`hash_inst`]), the stack slots, the jump tables and the exception
/// call sites. The `preds`/`succs` lists are metadata the validators never
/// read (they derive control flow from the instructions) and are left out.
fn function_digest(func: &MachFunction) -> u128 {
    let mut h = Digest128::default();
    feed_function_body(func, &mut h);
    h.finish128()
}

/// Feed every field [`function_digest`] covers to `h`.
fn feed_function_body<H: Hasher>(func: &MachFunction, h: &mut H) {
    func.entry.0.hash(h);
    func.block_order.len().hash(h);
    for b in &func.block_order {
        b.0.hash(h);
    }
    func.blocks.len().hash(h);
    for block in &func.blocks {
        block.insts.len().hash(h);
        for id in &block.insts {
            id.0.hash(h);
        }
    }
    func.insts.len().hash(h);
    for inst in &func.insts {
        hash_inst(inst, h);
    }
    func.stack_slots.len().hash(h);
    for slot in &func.stack_slots {
        slot.size.hash(h);
        slot.align.hash(h);
        format!("{:?}", slot.allocation).hash(h);
    }
    func.jump_tables.len().hash(h);
    for table in &func.jump_tables {
        table.targets.len().hash(h);
        for t in &table.targets {
            t.0.hash(h);
        }
    }
    func.eh_metadata.call_sites.len().hash(h);
    for site in &func.eh_metadata.call_sites {
        site.call_block.0.hash(h);
        site.landing_pad_block.map(|b| b.0).hash(h);
    }
    // Modern call identity is semantic custody, not a layout-only hint.
    // Include the mode, order and every record so an identity-only mutation
    // cannot reuse a prior whole-function validation result.
    func.eh_metadata.call_site_bindings.hash(h);
}

/// Feed a machine function's interface to `state`: its name, signature,
/// stack-protector and stack-limit requirements (with the overflow block),
/// every field the validators read ([`function_digest`]: the entry, the
/// layout, every block's instruction list, every instruction's behavior
/// fields, the stack slots, the jump tables and the exception call sites
/// with their bindings), and the side tables a later stage check or the
/// encoder reads: the trap expansions (the post-allocation comparison's trap
/// records and the encoder's trap-expansion check), the call-site ABI facts
/// and incoming stack-argument extent (the post-allocation comparison's call
/// and frame model), the per-function target features (output-feature
/// checks), the `noalias` parameter claims (a pass premise), the selector's
/// fusion edges (the raw TV-3 check) and the profile-order bit (the static
/// branch layout).
///
/// This is the representation a composed transition chain names at each
/// machine-IR boundary: a caller hashes it with a cryptographic digest
/// ([`FunctionInterfaceDigest`]). Left out, because no stage relation reads
/// them as semantics and passes rewrite them without changing behavior: the
/// `preds`/`succs` lists (derived from the instructions), the ID counters
/// (`next_vreg`, the identity-admission cell), source locations, proof
/// annotations (`function_proofs`), the TV-1 lowering-provenance sidecar,
/// debug metadata and the code-alignment hint `text_align_log2` (padding
/// placement only; the bytes it shapes are the encoding link's terminal).
pub fn hash_function_interface<H: Hasher>(func: &MachFunction, state: &mut H) {
    func.name.hash(state);
    format!("{:?}", func.signature).hash(state);
    format!("{:?}", func.stack_protector).hash(state);
    format!("{:?}", func.stack_protector_slot).hash(state);
    func.stack_limit.hash(state);
    func.stack_limit_overflow_block.map(|b| b.0).hash(state);
    feed_function_body(func, state);
    func.trap_expansions.len().hash(state);
    for record in &func.trap_expansions {
        format!("{record:?}").hash(state);
    }
    func.call_abi_facts.len().hash(state);
    for (call, facts) in &func.call_abi_facts {
        call.0.hash(state);
        format!("{facts:?}").hash(state);
    }
    func.incoming_stack_arg_bytes.hash(state);
    func.function_target_features.hash(state);
    func.noalias_params.hash(state);
    func.source_fusion_targets.hash(state);
    func.profile_ordered.hash(state);
}

/// A fast non-cryptographic 128-bit digest: two independently mixed 64-bit
/// lanes fed a word at a time.
#[derive(Default)]
struct Digest128 {
    a: u64,
    b: u64,
}

impl Digest128 {
    fn word(&mut self, w: u64) {
        self.a = (self.a.rotate_left(5) ^ w).wrapping_mul(0x517c_c1b7_2722_0a95);
        self.b =
            ((self.b.rotate_left(23) ^ w).wrapping_mul(0x9e37_79b9_7f4a_7c15)) ^ (self.b >> 29);
    }

    fn finish128(&self) -> u128 {
        (u128::from(self.b) << 64) | u128::from(self.a)
    }
}

impl Hasher for Digest128 {
    fn finish(&self) -> u64 {
        self.a ^ self.b
    }

    fn write(&mut self, bytes: &[u8]) {
        for chunk in bytes.chunks(8) {
            let mut w = [0u8; 8];
            w[..chunk.len()].copy_from_slice(chunk);
            self.word(u64::from_le_bytes(w) ^ ((chunk.len() as u64) << 59));
        }
    }

    fn write_u8(&mut self, i: u8) {
        self.word(u64::from(i));
    }

    fn write_u16(&mut self, i: u16) {
        self.word(u64::from(i));
    }

    fn write_u32(&mut self, i: u32) {
        self.word(u64::from(i));
    }

    fn write_u64(&mut self, i: u64) {
        self.word(i);
    }

    fn write_usize(&mut self, i: usize) {
        self.word(i as u64);
    }

    fn write_i64(&mut self, i: i64) {
        self.word(i as u64);
    }

    fn write_i32(&mut self, i: i32) {
        self.word(i as u32 as u64);
    }
}

/// What [`PassValidationHook::snapshot`] took before a run.
pub(crate) struct RunSnapshot {
    /// The validator's input, when a validator runs on this pass.
    check: Option<PassSnapshot>,
    /// `check` was taken for the transition record only: the scope runs no
    /// validator on this pass, so its verdict stays out of the summary.
    composition_only: bool,
    /// Interface digest before the run, when transitions are recorded.
    before: Option<[u8; 32]>,
}

/// Validation driver used by the pass managers around each pass run, one
/// per driver call (it keeps a copy of the function between runs).
#[derive(Debug, Default)]
pub(crate) struct PassValidationHook {
    config: PassValidationConfig,
    /// A copy of the function as the last symbolic snapshot or unchanged run
    /// left it, with its digest: a later snapshot of an unchanged function
    /// reuses it instead of copying again.
    shadow: Option<(Box<MachFunction>, u128)>,
    /// Record a [`PassTransition`] for every run that changes the interface.
    transitions: Option<FunctionInterfaceDigest>,
}

impl PassValidationHook {
    pub(crate) fn new(config: PassValidationConfig) -> Self {
        Self {
            config,
            shadow: None,
            transitions: None,
        }
    }

    /// Also record transitions under `digest` (builder pattern).
    pub(crate) fn with_transitions(mut self, digest: Option<FunctionInterfaceDigest>) -> Self {
        self.transitions = digest;
        self
    }

    #[cfg(test)]
    pub(crate) fn config(&self) -> PassValidationConfig {
        self.config
    }

    /// The validator input the scope asks for on `pass_name`, if any.
    fn scoped_check(&mut self, pass_name: &str, func: &MachFunction) -> Option<PassSnapshot> {
        if !self.config.policy.is_active() {
            return None;
        }
        match (dedicated_validator(pass_name), self.config.scope) {
            // Stage comparisons are run by the codegen pipeline, not here.
            (Some(ValidatorKind::PostAllocationValueFlow), _) => None,
            (Some(ValidatorKind::DependencePreservation), _) => Some(PassSnapshot::Permutation(
                PermutationSnapshot::capture(func),
            )),
            (Some(_), PassValidationScope::Dedicated | PassValidationScope::AllPasses)
            | (None, PassValidationScope::AllPasses) => Some(self.function_snapshot(func)),
            (Some(_), PassValidationScope::Schedulers)
            | (None, PassValidationScope::Schedulers | PassValidationScope::Dedicated) => None,
        }
    }

    /// A copy of `func` with its digest, reusing the shadow copy when the
    /// function has not changed since it was taken.
    fn function_snapshot(&mut self, func: &MachFunction) -> PassSnapshot {
        let digest = function_digest(func);
        let before = match self.shadow.take() {
            Some((copy, shadow_digest)) if shadow_digest == digest => copy,
            _ => Box::new(func.clone()),
        };
        PassSnapshot::Function(before, digest)
    }

    /// Capture what `pass_name`'s validator needs, before the run, and the
    /// interface digest when transitions are recorded.
    pub(crate) fn snapshot(&mut self, pass_name: &str, func: &MachFunction) -> RunSnapshot {
        let scoped = self.scoped_check(pass_name, func);
        let Some(digest) = self.transitions else {
            return RunSnapshot {
                check: scoped,
                composition_only: false,
                before: None,
            };
        };
        let before = Some(digest(func));
        if scoped.is_some() {
            return RunSnapshot {
                check: scoped,
                composition_only: false,
                before,
            };
        }
        // The transition record validates every run the scope leaves
        // unchecked: the dedicated validator where one exists, otherwise the
        // generic region check.
        let check = match dedicated_validator(pass_name) {
            Some(ValidatorKind::PostAllocationValueFlow) => None,
            Some(ValidatorKind::DependencePreservation) => Some(PassSnapshot::Permutation(
                PermutationSnapshot::capture(func),
            )),
            _ => Some(self.function_snapshot(func)),
        };
        RunSnapshot {
            composition_only: check.is_some(),
            check,
            before,
        }
    }

    /// Run `pass_name`'s validator on one finished run: the validator used,
    /// its verdict, the instructions it examined and the input function when
    /// the verdict needs it for a failure dump.
    fn validate(
        &mut self,
        pass_name: &str,
        snapshot: PassSnapshot,
        changed: bool,
        func: &MachFunction,
    ) -> (
        ValidatorKind,
        ValidationVerdict,
        u64,
        Option<Box<MachFunction>>,
    ) {
        match snapshot {
            PassSnapshot::Permutation(before) => {
                let outcome = validate_permutation(&before, func);
                if changed {
                    (
                        ValidatorKind::DependencePreservation,
                        outcome.verdict,
                        outcome.examined,
                        None,
                    )
                } else {
                    // An unchanged report must leave the orders untouched.
                    let verdict = if before.matches(func) {
                        ValidationVerdict::Validated
                    } else {
                        ValidationVerdict::Refuted(
                            "the run reported no change but altered the function".to_string(),
                        )
                    };
                    (
                        ValidatorKind::UnchangedClaim,
                        verdict,
                        outcome.examined,
                        None,
                    )
                }
            }
            PassSnapshot::Function(before, digest) => {
                let examined = (before.insts.len() + func.insts.len()) as u64;
                if !changed {
                    if function_digest(func) == digest {
                        // Still the function the copy holds: keep it for the
                        // next snapshot.
                        self.shadow = Some((before, digest));
                        (
                            ValidatorKind::UnchangedClaim,
                            ValidationVerdict::Validated,
                            examined,
                            None,
                        )
                    } else {
                        (
                            ValidatorKind::UnchangedClaim,
                            ValidationVerdict::Refuted(
                                "the run reported no change but altered the function".to_string(),
                            ),
                            examined,
                            Some(before),
                        )
                    }
                } else if dedicated_validator(pass_name) == Some(ValidatorKind::HoistConditions) {
                    let outcome = hoist::validate_hoists(&before, func);
                    (
                        ValidatorKind::HoistConditions,
                        outcome.verdict,
                        examined + outcome.examined,
                        Some(before),
                    )
                } else {
                    let outcome = region::validate_regions(&before, func);
                    (
                        ValidatorKind::SymbolicRegionEquivalence,
                        outcome.verdict,
                        examined + outcome.examined,
                        Some(before),
                    )
                }
            }
        }
    }

    /// Validate one finished run and record the verdict, and its transition
    /// when transitions are recorded and the run changed the interface.
    pub(crate) fn conclude(
        &mut self,
        pass_name: &str,
        snapshot: RunSnapshot,
        changed: bool,
        func: &MachFunction,
        summary: &mut PassValidationSummary,
    ) {
        let RunSnapshot {
            check,
            composition_only,
            before,
        } = snapshot;
        let outcome = check.map(|check| self.validate(pass_name, check, changed, func));
        if self.config.policy.is_active() {
            match (&outcome, composition_only) {
                (Some((validator, verdict, examined, before_function)), false) => {
                    summary.examined_instructions =
                        summary.examined_instructions.saturating_add(*examined);
                    let record = PassValidationRecord {
                        pass_name: pass_name.to_string(),
                        function_name: func.name.clone(),
                        validator: Some(*validator),
                        verdict: verdict.clone(),
                    };
                    if !record.verdict.is_validated() {
                        dump_failure(&record, before_function.as_deref(), func);
                    }
                    summary.record(record, changed);
                }
                _ => {
                    if changed {
                        summary.record(
                            PassValidationRecord {
                                pass_name: pass_name.to_string(),
                                function_name: func.name.clone(),
                                validator: None,
                                verdict: ValidationVerdict::Uncovered,
                            },
                            true,
                        );
                    }
                }
            }
        }
        let (Some(before), Some(digest)) = (before, self.transitions) else {
            return;
        };
        let after = digest(func);
        if before == after {
            return;
        }
        let (validator, verdict) = match outcome {
            _ if !changed => (
                Some(ValidatorKind::UnchangedClaim),
                ValidationVerdict::Refuted(
                    "the run reported no change but altered the function's interface".to_string(),
                ),
            ),
            Some((validator, verdict, _, _)) => (Some(validator), verdict),
            None => (None, ValidationVerdict::Uncovered),
        };
        summary.transitions.push(PassTransition {
            pass_name: pass_name.to_string(),
            reported_change: changed,
            before,
            after,
            validator,
            verdict,
        });
    }
}

/// Run `pass` once on `func` with validation under `config`, recording the
/// verdict in `summary`. For passes driven outside a [`crate::PassManager`]
/// (the codegen pipeline's final scheduler). Returns the pass's change
/// report.
pub fn run_validated(
    config: PassValidationConfig,
    pass: &mut dyn crate::MachinePass,
    func: &mut MachFunction,
    summary: &mut PassValidationSummary,
) -> bool {
    run_validated_with_transitions(config, None, pass, func, summary)
}

/// [`run_validated`], also recording the run's [`PassTransition`] under
/// `transitions` when it changes the function's interface.
pub fn run_validated_with_transitions(
    config: PassValidationConfig,
    transitions: Option<FunctionInterfaceDigest>,
    pass: &mut dyn crate::MachinePass,
    func: &mut MachFunction,
    summary: &mut PassValidationSummary,
) -> bool {
    let mut hook = PassValidationHook::new(config).with_transitions(transitions);
    let snapshot = hook.snapshot(pass.name(), func);
    let changed = pass.run(func);
    hook.conclude(pass.name(), snapshot, changed, func, summary);
    changed
}

/// Record a changed run of a mutating step that no validator covers, so a
/// summary never omits a rewrite.
pub fn record_unvalidated_change(
    config: PassValidationConfig,
    pass_name: &str,
    func: &MachFunction,
    summary: &mut PassValidationSummary,
) {
    PassValidationHook::new(config).conclude(
        pass_name,
        RunSnapshot {
            check: None,
            composition_only: false,
            before: None,
        },
        true,
        func,
        summary,
    );
}

/// Record the transition of a mutating step no validator covers, run
/// outside a pass manager: `before` is its input's interface digest under
/// `transitions`. When the step changed the interface the transition is
/// [`ValidationVerdict::Uncovered`]; otherwise nothing is recorded. Without
/// transitions this does nothing (the caller records the change itself with
/// [`record_unvalidated_change`]).
pub fn record_unvalidated_transition(
    transitions: Option<FunctionInterfaceDigest>,
    pass_name: &str,
    before: Option<[u8; 32]>,
    func: &MachFunction,
    summary: &mut PassValidationSummary,
) {
    let (Some(digest), Some(before)) = (transitions, before) else {
        return;
    };
    let after = digest(func);
    if before != after {
        summary.transitions.push(PassTransition {
            pass_name: pass_name.to_string(),
            reported_change: true,
            before,
            after,
            validator: None,
            verdict: ValidationVerdict::Uncovered,
        });
    }
}

/// Feed every behavior-relevant field of `inst` to `state`.
///
/// Source locations and proof annotations are metadata, not behavior, and
/// are left out.
pub(crate) fn hash_inst<H: Hasher>(inst: &MachInst, state: &mut H) {
    (inst.opcode as u32).hash(state);
    inst.flags.bits().hash(state);
    inst.operands.len().hash(state);
    for operand in &inst.operands {
        hash_operand(operand, state);
    }
    inst.implicit_defs.len().hash(state);
    for preg in inst.implicit_defs {
        preg.encoding().hash(state);
    }
    inst.implicit_uses.len().hash(state);
    for preg in inst.implicit_uses {
        preg.encoding().hash(state);
    }
}

fn hash_operand<H: Hasher>(operand: &MachOperand, state: &mut H) {
    match operand {
        MachOperand::VReg(v) => {
            0u8.hash(state);
            v.id.hash(state);
            (v.class as u8).hash(state);
        }
        MachOperand::PReg(p) => {
            1u8.hash(state);
            p.encoding().hash(state);
        }
        MachOperand::Imm(v) => {
            2u8.hash(state);
            v.hash(state);
        }
        MachOperand::FImm(v) => {
            3u8.hash(state);
            v.to_bits().hash(state);
        }
        MachOperand::Block(b) => {
            4u8.hash(state);
            b.0.hash(state);
        }
        MachOperand::StackSlot(s) => {
            5u8.hash(state);
            s.0.hash(state);
        }
        MachOperand::FrameIndex(f) => {
            6u8.hash(state);
            f.0.hash(state);
        }
        MachOperand::MemOp { base, offset } => {
            7u8.hash(state);
            base.encoding().hash(state);
            offset.hash(state);
        }
        MachOperand::Special(s) => {
            8u8.hash(state);
            (*s as u8).hash(state);
        }
        MachOperand::Symbol(name) => {
            9u8.hash(state);
            name.hash(state);
        }
        MachOperand::ExactModuleSymbol(name) => {
            10u8.hash(state);
            name.hash(state);
        }
        MachOperand::JumpTableIndex(i) => {
            11u8.hash(state);
            i.hash(state);
        }
        MachOperand::IncomingArg(o) => {
            12u8.hash(state);
            o.hash(state);
        }
    }
}

#[cfg(test)]
mod eh_identity_tests;
#[cfg(test)]
mod tests;
