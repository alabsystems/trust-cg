// trust-cg-irmid/report.rs - what the mid-end did to one module
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! [`IrmidReport`]: per-module evidence of the mid-end — passes run,
//! functions changed, rollbacks with their reasons, skipped functions,
//! proof-table transport and interpreter-differential coverage. Every count is
//! of what happened on this compile; nothing here is a proof.

use std::collections::{BTreeMap, BTreeSet};

use crate::MidProfile;

/// The detailed rollbacks kept in a report; the rest are only counted.
pub const ROLLBACK_LIST_MAX: usize = 16;

/// One pass over one module.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PassStats {
    pub name: &'static str,
    /// Function-passes whose rewrite was validated and kept: one per function
    /// per run of this pass. A pass the pipeline runs more than once
    /// (`copy_prop` eight times, `dce` four times, `ptr_gep` three times and
    /// `sroa` twice on wasm32) adds up every run, so this can exceed the
    /// module's function count; the distinct functions changed (and those
    /// argument promotion appended) are [`IrmidReport::functions_changed`].
    pub functions_changed: usize,
    /// Kept rewrites checked exact.
    pub exact: usize,
    /// Kept rewrites checked as refinements of the source rather than exact
    /// equivalents: a dead instruction that may raise undefined behaviour
    /// removed (`dce`), the stores of a slot nothing reads removed
    /// (`dead_slot`), a table promoted to read-only data (`ctp`, where a
    /// read of a byte before its store now sees the table's byte), a load
    /// or store of a slot replaced by SSA values (`sroa`, where the access
    /// may have been misaligned), a call site inlined (`inline`, where the
    /// call's own checks go away: a poison argument or result, an argument of
    /// another pointer type), or a call redirected to a clone with promoted
    /// arguments (`argpromo`).
    pub refinements: usize,
    /// Rewrites rolled back.
    pub rollbacks: usize,
    /// Kept rewrites by rule, for a pass whose witness names its rules (the
    /// range rules: `icmp`, `add_overflow`, `sub_overflow`, `mul_overflow`,
    /// `select`, `assert`, `condbr`, and the blocks the folded branches left
    /// unreachable as `removed_block`); empty for every other pass. Pending
    /// the owner's sign-off on the mid-end's evidence: an additive field
    /// nothing outside this crate reads yet.
    pub rules: BTreeMap<&'static str, usize>,
    /// The claimed rewrites by rule of the candidates rolled back (by the
    /// witness check, the differential or the proof-table transaction).
    /// Pending sign-off, as [`Self::rules`].
    pub rules_rolled_back: BTreeMap<&'static str, usize>,
}

/// One rolled-back rewrite.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rollback {
    pub pass: &'static str,
    pub function: String,
    /// `witness`, `differential` or `proof_table`, then the detail.
    pub reason: String,
}

/// Proof-table transport, one transaction per pass that changed a function.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ProofTableStats {
    pub transactions: usize,
    pub validated: usize,
    pub rejected: usize,
    pub preserved: usize,
    pub remapped: usize,
    pub invalidated: usize,
}

/// One pass's interpreter-differential coverage.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PassCoverage {
    /// Candidate rewrites the differential ran on (every run of the pass).
    pub candidates: usize,
    /// Of those, the ones compared ([`TvCoverage::function_passes_compared`]).
    pub compared: usize,
    /// The rest, by reason ([`TvCoverage::not_compared`]).
    pub not_compared: BTreeMap<String, usize>,
}

/// Interpreter-differential coverage. A function-pass is one candidate
/// rewrite of one function. Each candidate is counted once: compared, or
/// under exactly one reason in [`Self::not_compared`].
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TvCoverage {
    /// Candidate rewrites the differential ran on.
    pub function_passes: usize,
    /// Of those, the ones with at least one compared input
    /// ([`Self::samples_compared`]), or rolled back on a disagreement on
    /// which the candidate returned, panicked or raised undefined behaviour.
    pub function_passes_compared: usize,
    /// Of those, the ones whose inputs are memory a driver builds (a
    /// parameter that is not a scalar).
    pub function_passes_driven: usize,
    /// Inputs compared: both runs finished on a defined input and agree on
    /// something observed (results, a panic, or memory the input provided).
    pub samples_compared: usize,
    /// Of those, the inputs whose memory (bytes of the objects the input
    /// provided, after the call) was compared too.
    pub samples_memory_compared: usize,
    /// Of those, the ones that read back only the bytes the source left
    /// initialised (the function left some bytes of an object
    /// uninitialised).
    pub samples_memory_narrowed: usize,
    /// Of [`Self::samples_compared`], the inputs that bind two or more
    /// memory parameters into one object.
    pub samples_aliased_compared: usize,
    /// Inputs on which both runs returned with nothing to compare (no
    /// result, no memory read back): not counted as compared.
    pub samples_nothing_observed: usize,
    /// Inputs excluded because the source raised undefined behaviour.
    pub samples_ub_excluded: usize,
    /// Inputs the interpreter could not finish on the source.
    pub samples_not_executed: usize,
    /// Inputs whose bytes are not a value of a parameter's type (never run).
    pub samples_invalid: usize,
    /// Inputs not run because the module's step budget was spent.
    pub samples_over_budget: usize,
    /// Candidate rewrites of functions none of whose inputs can be built
    /// (checked by the witness alone); also under `not_synthesizable:*` in
    /// [`Self::not_compared`].
    pub function_passes_not_synthesizable: usize,
    /// Candidate rewrites checked by the witness alone because the module's
    /// step budget was spent; also `over_budget` in [`Self::not_compared`].
    pub function_passes_over_budget: usize,
    /// Why each candidate that is not compared is not:
    /// `not_synthesizable:<what>` (a parameter type no input is built for),
    /// `over_budget`, `nothing_observed` (both returned on some input, with
    /// no result and no memory read back), `not_executed:<code>` (the
    /// interpreter could not finish the source on any input: the most
    /// frequent reason, such as `call_to_declaration`, `type_error` or
    /// `out_of_fuel`), `all_inputs_undefined` (the source raised undefined
    /// behaviour on every valid input), `no_valid_input`, or
    /// `mismatch:target_<outcome>` (rolled back on a disagreement on which
    /// the candidate's run did not finish).
    pub not_compared: BTreeMap<String, usize>,
    /// [`Self::samples_not_executed`] by reason.
    pub not_executed: BTreeMap<&'static str, usize>,
    /// Per pass.
    pub by_pass: BTreeMap<&'static str, PassCoverage>,
    /// Interpreter steps spent (an upper bound).
    pub steps: u64,
}

/// What the mid-end did to one module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IrmidReport {
    pub profile: &'static str,
    /// Whether the passes ran.
    pub enabled: bool,
    /// Why they did not, when they did not.
    pub not_run: Option<String>,
    /// Defined functions in the module.
    pub functions: usize,
    /// Functions whose final body differs from the input's.
    pub functions_changed: usize,
    /// `alloca` instructions in the defined functions of the input and of
    /// the output (store forwarding and dead-slot removal leave slots that
    /// dead-code elimination removes; promotion turns one into a global).
    pub allocas_before: usize,
    pub allocas_after: usize,
    /// Read-only globals constant-table promotion added.
    pub globals_added: usize,
    /// The link symbols of the callees the inliner spliced into a kept
    /// rewrite (a caller may withhold them from a re-run; not part of the
    /// JSON rendering, whose pass statistics count the sites).
    pub inlined: BTreeSet<String>,
    /// Functions the passes did not touch, by reason.
    pub skipped: BTreeMap<&'static str, usize>,
    pub passes: Vec<PassStats>,
    /// Passes of the profile's pipeline the caller withheld, with why (see
    /// [`crate::MidConfig::promote_constant_tables`]).
    pub passes_withheld: BTreeMap<&'static str, String>,
    /// Rollbacks by `pass:kind`.
    pub rollback_reasons: BTreeMap<String, usize>,
    /// The first [`ROLLBACK_LIST_MAX`] rollbacks, in order.
    pub rollbacks: Vec<Rollback>,
    pub proof_table: ProofTableStats,
    pub tv: TvCoverage,
    /// Whether the optimized module is the one the caller emitted. A caller
    /// that re-validates the module and falls back to the input says why in
    /// [`Self::fallback`].
    pub applied: bool,
    pub fallback: Option<String>,
}

impl IrmidReport {
    /// A report for a module the passes did not run on.
    pub fn not_run(profile: MidProfile, why: impl Into<String>) -> Self {
        Self {
            profile: profile.as_str(),
            enabled: false,
            not_run: Some(why.into()),
            functions: 0,
            functions_changed: 0,
            allocas_before: 0,
            allocas_after: 0,
            globals_added: 0,
            inlined: BTreeSet::new(),
            skipped: BTreeMap::new(),
            passes: Vec::new(),
            passes_withheld: BTreeMap::new(),
            rollback_reasons: BTreeMap::new(),
            rollbacks: Vec::new(),
            proof_table: ProofTableStats::default(),
            tv: TvCoverage::default(),
            applied: false,
            fallback: None,
        }
    }

    pub(crate) fn started(profile: MidProfile) -> Self {
        Self {
            enabled: true,
            not_run: None,
            ..Self::not_run(profile, "")
        }
    }

    /// Total rollbacks.
    pub fn rollback_count(&self) -> usize {
        self.rollback_reasons.values().sum()
    }

    /// Total skipped functions.
    pub fn skipped_count(&self) -> usize {
        self.skipped.values().sum()
    }

    pub(crate) fn record_rollback(&mut self, pass: &'static str, function: &str, reason: String) {
        let kind = reason.split(':').next().unwrap_or("other").to_string();
        *self
            .rollback_reasons
            .entry(format!("{pass}:{kind}"))
            .or_default() += 1;
        if let Some(stats) = self.passes.iter_mut().find(|p| p.name == pass) {
            stats.rollbacks += 1;
        }
        if self.rollbacks.len() < ROLLBACK_LIST_MAX {
            self.rollbacks.push(Rollback {
                pass,
                function: function.to_string(),
                reason,
            });
        }
    }

    /// The caller emitted the input module instead of the optimized one.
    pub fn fall_back(&mut self, why: impl Into<String>) {
        self.applied = false;
        self.fallback = Some(why.into());
    }

    /// Canonical JSON rendering.
    pub fn to_json(&self) -> serde_json::Value {
        let passes: Vec<_> = self
            .passes
            .iter()
            .map(|p| {
                let mut pass = serde_json::json!({
                    "name": p.name,
                    "functions_changed": p.functions_changed,
                    "exact": p.exact,
                    "refinements": p.refinements,
                    "rollbacks": p.rollbacks,
                });
                // Only a pass whose witness names rules carries the counts,
                // so every other pass's rendering is unchanged.
                if !p.rules.is_empty() || !p.rules_rolled_back.is_empty() {
                    pass["rules"] = serde_json::json!(p.rules);
                    pass["rules_rolled_back"] = serde_json::json!(p.rules_rolled_back);
                }
                pass
            })
            .collect();
        let rollbacks: Vec<_> = self
            .rollbacks
            .iter()
            .map(|r| {
                serde_json::json!({
                    "pass": r.pass,
                    "function": r.function,
                    "reason": r.reason,
                })
            })
            .collect();
        let by_pass: serde_json::Map<String, serde_json::Value> = self
            .tv
            .by_pass
            .iter()
            .map(|(pass, c)| {
                (
                    (*pass).to_string(),
                    serde_json::json!({
                        "candidates": c.candidates,
                        "compared": c.compared,
                        "not_compared": c.not_compared,
                    }),
                )
            })
            .collect();
        serde_json::json!({
            "means": "trust-ir to trust-ir rewrites, each kept only when its independent witness \
                      checker accepts it and the reference-interpreter differential on seeded \
                      inputs (memory built for pointer, slice and aggregate parameters, module \
                      callees run through the call) finds no disagreement in results, input \
                      memory or panics (inputs on which the source raises undefined behaviour \
                      excluded). tv counts each candidate rewrite once: compared, or under one \
                      not_compared reason. A pass's functions_changed counts function-passes, \
                      summed over every run of that pass in the pipeline; refinements are \
                      rewrites checked as refinements rather than exact (dead UB-raising \
                      instructions removed, the stores of an unread slot removed, a table \
                      promoted to read-only data, the loads and stores of a slot replaced by \
                      SSA values, call sites inlined, where the call's poison and exact-type \
                      checks go away with the call, calls redirected to clones with promoted \
                      arguments). Structural and differential evidence, not a \
                      proof; the differential covers only the counted inputs",
            "profile": self.profile,
            "enabled": self.enabled,
            "not_run": self.not_run,
            "functions": self.functions,
            "functions_changed": self.functions_changed,
            "allocas_before": self.allocas_before,
            "allocas_after": self.allocas_after,
            "globals_added": self.globals_added,
            "skipped": self.skipped,
            "skipped_count": self.skipped_count(),
            "passes": passes,
            "passes_withheld": self.passes_withheld,
            "rollback_count": self.rollback_count(),
            "rollback_reasons": self.rollback_reasons,
            "rollbacks": rollbacks,
            "proof_table": {
                "transactions": self.proof_table.transactions,
                "validated": self.proof_table.validated,
                "rejected": self.proof_table.rejected,
                "preserved": self.proof_table.preserved,
                "remapped": self.proof_table.remapped,
                "invalidated": self.proof_table.invalidated,
            },
            "tv": {
                "function_passes": self.tv.function_passes,
                "function_passes_compared": self.tv.function_passes_compared,
                "function_passes_driven": self.tv.function_passes_driven,
                "samples_compared": self.tv.samples_compared,
                "samples_memory_compared": self.tv.samples_memory_compared,
                "samples_memory_narrowed": self.tv.samples_memory_narrowed,
                "samples_aliased_compared": self.tv.samples_aliased_compared,
                "samples_nothing_observed": self.tv.samples_nothing_observed,
                "samples_ub_excluded": self.tv.samples_ub_excluded,
                "samples_not_executed": self.tv.samples_not_executed,
                "samples_invalid": self.tv.samples_invalid,
                "samples_over_budget": self.tv.samples_over_budget,
                "function_passes_not_synthesizable": self.tv.function_passes_not_synthesizable,
                "function_passes_over_budget": self.tv.function_passes_over_budget,
                "not_compared": self.tv.not_compared,
                "not_executed": self.tv.not_executed,
                "by_pass": by_pass,
                "steps": self.tv.steps,
            },
            "applied": self.applied,
            "fallback": self.fallback,
        })
    }
}
