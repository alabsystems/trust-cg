// trust-cg-irmid/manager.rs - snapshot, check, roll back
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The pass manager (see the crate docs). Invariants:
//!
//! * a function's body changes only to a candidate whose witness
//!   `trust_ir_mid_tv::check_pass` accepted and whose interpreter differential
//!   found no disagreement; any failure leaves the snapshot;
//! * the differential runs each input of the function's harness
//!   (`trust_ir_mid_tv::Harness`) on its current body once, and the candidate
//!   only on the inputs that body finished (returned or panicked): an input
//!   on which it raised undefined behaviour is excluded for the rest of the
//!   pipeline (the refinement rule, by transitivity), and one it could not
//!   run or finish cannot be compared. Every candidate is counted as
//!   compared or under exactly one reason
//!   ([`crate::report::TvCoverage::not_compared`]): compared means at least
//!   one input on which both bodies finished and agreed on something
//!   observed (results, a panic, or bytes of the memory the input provided;
//!   both returning with nothing to compare is `nothing_observed`), or a
//!   disagreement on which the candidate reached a verdict of its own
//!   (returned, panicked or raised undefined behaviour);
//! * after each pass the module before and after it are related by a
//!   validated trust-ir `ProofTableTransformTransaction` in which every
//!   obligation is `Preserved`, or every function the pass changed is restored;
//! * only function bodies (and the debug names of removed values) change,
//!   and the types and globals a kept rewrite's witness appends
//!   (`PassWitness::module_additions`: constant-table promotion's read-only
//!   globals) and the signatures and functions it appends
//!   (`PassWitness::function_additions`: argument promotion's clones), which
//!   leave with the rewrite when it is rolled back. An appended function is
//!   eligible for every later pass once its pass's proof-table transaction
//!   is validated.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use trust_cg_verify::trust_ir_mid_tv::{
    Harness, InputOutcome, InputRun, InputVerdict, NotSynthesized, Observed, PassWitness,
    check_pass, compare_input, interpretable, interpretable_module, run_inputs, run_target,
};
use trust_ir::proof::{
    ProofObligationDisposition, ProofObligationTransform, ProofTableTransformTransaction,
    ProofTableTransformValidation, ProofTransform, ProofTransformStage,
};
use trust_ir::{FuncId, Function, Module};

use crate::passes::{MidPass, PassContext};
use crate::report::{IrmidReport, PassStats, TvCoverage};
use crate::{MidConfig, MidProfile};

/// The producer named in every proof-table transaction.
const PRODUCER: &str = "trust-cg-irmid";

/// Why a function is not touched, or `None` when it is eligible.
fn ineligible(
    func: &Function,
    named: &BTreeSet<FuncId>,
    protect_all: Option<&'static str>,
) -> Option<&'static str> {
    if let Some(reason) = protect_all {
        return Some(reason);
    }
    if named.contains(&func.id) {
        return Some("module_obligation");
    }
    if !func.proofs.is_empty()
        || func
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| !n.proofs.is_empty() || n.proof_context.is_some())
    {
        return Some("proof_annotations");
    }
    if func.summary.is_some() {
        return Some("summary");
    }
    if func.source_provenance.is_some() {
        return Some("source_provenance");
    }
    if func.body_gate.is_some() {
        return Some("body_gate");
    }
    None
}

/// A function's harness and its current body's runs, per function index.
enum Samples {
    /// No input of the function can be built.
    Unsynthesizable(NotSynthesized),
    /// The harness, and the current body's runs once computed.
    Ready(Box<Harness>, Option<Vec<InputRun>>),
}

/// Why a candidate rewrite has no compared input, from the outcomes of its
/// source's runs: inputs on which both bodies returned but nothing was read
/// to compare (no result, no memory: `nothing_observed`), else an input the
/// interpreter could not finish (the most frequent reason), else one the
/// budget left unrun, else one on which the source raised undefined
/// behaviour, else invalid inputs only.
fn not_compared_reason(source: &[InputRun], terminated: bool) -> String {
    if terminated {
        return "nothing_observed".to_string();
    }
    let mut not_executed: BTreeMap<&'static str, usize> = BTreeMap::new();
    let (mut over_budget, mut undefined) = (false, false);
    for run in source {
        match run.outcome {
            InputOutcome::NotExecuted(code) => *not_executed.entry(code).or_default() += 1,
            InputOutcome::OverBudget => over_budget = true,
            InputOutcome::Undefined => undefined = true,
            _ => {}
        }
    }
    if let Some((code, _)) = not_executed
        .iter()
        .max_by(|a, b| a.1.cmp(b.1).then_with(|| b.0.cmp(a.0)))
    {
        format!("not_executed:{code}")
    } else if over_budget {
        "over_budget".to_string()
    } else if undefined {
        "all_inputs_undefined".to_string()
    } else {
        "no_valid_input".to_string()
    }
}

/// Why a candidate's run that disagrees with its source did not reach a
/// verdict of its own (`None` when it returned, panicked or raised undefined
/// behaviour).
pub(crate) fn unfinished(target: &InputOutcome) -> Option<String> {
    match target {
        InputOutcome::Returned { .. } | InputOutcome::Panicked(..) | InputOutcome::Undefined => {
            None
        }
        InputOutcome::NotExecuted(code) => Some(format!("mismatch:target_not_executed:{code}")),
        InputOutcome::OverBudget => Some("mismatch:target_over_budget".to_string()),
        InputOutcome::Invalid => Some("mismatch:target_invalid".to_string()),
    }
}

/// The rewrites by rule a witness claims (empty for a pass whose witness
/// names no rules).
fn rule_counts(witness: &PassWitness) -> BTreeMap<&'static str, usize> {
    match witness {
        PassWitness::Range(w) => w.counts(),
        _ => BTreeMap::new(),
    }
}

/// Add `counts` into `into`.
fn add_counts(into: &mut BTreeMap<&'static str, usize>, counts: &BTreeMap<&'static str, usize>) {
    for (rule, n) in counts {
        *into.entry(rule).or_default() += n;
    }
}

/// Count `witness`'s rules as rolled back under `pass`.
fn rules_rolled_back(report: &mut IrmidReport, pass: &'static str, witness: &PassWitness) {
    let counts = rule_counts(witness);
    if counts.is_empty() {
        return;
    }
    if let Some(stats) = report.passes.iter_mut().find(|p| p.name == pass) {
        add_counts(&mut stats.rules_rolled_back, &counts);
    }
}

/// Count one candidate's verdict under `pass` (and the module totals).
fn count_candidate(tv: &mut TvCoverage, pass: &'static str, reason: Option<String>) {
    let entry = tv.by_pass.entry(pass).or_default();
    entry.candidates += 1;
    match reason {
        None => {
            entry.compared += 1;
            tv.function_passes_compared += 1;
        }
        Some(reason) => {
            if reason.starts_with("not_synthesizable") {
                tv.function_passes_not_synthesizable += 1;
            } else if reason == "over_budget" {
                tv.function_passes_over_budget += 1;
            }
            *entry.not_compared.entry(reason.clone()).or_default() += 1;
            *tv.not_compared.entry(reason).or_default() += 1;
        }
    }
}

pub(crate) fn run(
    module: &Module,
    config: &MidConfig,
    passes: &[&dyn MidPass],
) -> (Module, IrmidReport) {
    let mut report = IrmidReport::started(MidProfile::Wasm32);
    report.profile = config.profile.as_str();
    let pointer_bits = module.pointer_bits();
    let mut working = module.clone();

    // ---- Eligibility (fixed for the whole pipeline).
    let mut named = BTreeSet::new();
    let mut protect_all = None;
    for obligation in &module.proof_obligations {
        match (obligation.function, obligation.site.as_ref()) {
            (Some(function), site) => {
                named.insert(function);
                if let Some(site) = site {
                    named.insert(site.function);
                }
            }
            (None, Some(site)) => {
                named.insert(site.function);
            }
            (None, None) => protect_all = Some("unscoped_obligation"),
        }
    }
    if !module.spec_modules.is_empty() {
        protect_all = Some("spec_modules");
    }
    let mut eligible = Vec::new();
    for (index, func) in module.functions.iter().enumerate() {
        if func.is_declaration() {
            continue;
        }
        report.functions += 1;
        match ineligible(func, &named, protect_all) {
            Some(reason) => *report.skipped.entry(reason).or_default() += 1,
            None => eligible.push(index),
        }
    }

    let mut samples: HashMap<usize, Samples> = HashMap::new();
    let mut steps_left = config.module_step_budget;
    // The module the differential interprets: `working` in the interpreter's
    // view of the lane's idioms (`trust_ir_mid_tv::interpretable`), built at
    // the first candidate and kept in step with `working` from then on.
    let mut view: Option<Module> = None;

    for pass in passes {
        let name = pass.name();
        if !report.passes.iter().any(|p| p.name == name) {
            report.passes.push(PassStats {
                name,
                ..PassStats::default()
            });
        }
        let mut changed: Vec<(usize, Function)> = Vec::new();
        let mut kept = PassStats::default();
        // The module tables before the pass: a rejected transaction restores
        // them with the functions.
        let tables_before = (working.types.len(), working.globals.len());
        let functions_before = (working.func_types.len(), working.functions.len());
        let order = if pass.callee_first() {
            crate::passes::callee_first_order(&working, &eligible)
        } else {
            eligible.clone()
        };
        for &index in &order {
            let cx = PassContext {
                module: &working,
                pointer_bits,
            };
            let source = &working.functions[index];
            let Some((target, witness)) = pass.run(&cx, source) else {
                continue;
            };
            if &target == source {
                continue;
            }
            let verdict = match check_pass(&working, pointer_bits, source, &target, &witness) {
                Ok(verdict) => verdict,
                Err(error) => {
                    let function = source.name.clone();
                    report.record_rollback(name, &function, format!("witness: {error}"));
                    rules_rolled_back(&mut report, name, &witness);
                    continue;
                }
            };
            // The entries the rewrite appends join the module now, so the
            // differential runs the target against them; they leave again
            // when it is rolled back.
            let (new_types, new_globals) = witness.module_additions();
            let (new_func_types, new_functions) = witness.function_additions();
            let tables = (working.types.len(), working.globals.len());
            let functions = (working.func_types.len(), working.functions.len());
            working.types.extend(new_types.iter().cloned());
            working.globals.extend(new_globals.iter().cloned());
            working.func_types.extend(new_func_types.iter().cloned());
            working.functions.extend(new_functions.iter().cloned());
            let view = view.get_or_insert_with(|| interpretable_module(&working));
            if view.types.len() < working.types.len() {
                view.types.extend(new_types.iter().cloned());
            }
            if view.globals.len() < working.globals.len() {
                view.globals.extend(new_globals.iter().cloned());
            }
            if view.func_types.len() < working.func_types.len() {
                view.func_types.extend(new_func_types.iter().cloned());
            }
            if view.functions.len() < working.functions.len() {
                for added in new_functions {
                    let added = interpretable(view, added).unwrap_or_else(|| added.clone());
                    view.functions.push(added);
                }
            }
            let mut target_view = interpretable(view, &target).unwrap_or_else(|| target.clone());
            // ---- Interpreter differential.
            let entry = samples.entry(index).or_insert_with(|| {
                match Harness::build(
                    view,
                    &view.functions[index],
                    pointer_bits,
                    config.samples_per_function,
                    seed_of(&working.functions[index].name),
                    config.differential,
                    config.harness_limits,
                ) {
                    Ok(harness) => Samples::Ready(Box::new(harness), None),
                    Err(why) => Samples::Unsynthesizable(why),
                }
            });
            report.tv.function_passes += 1;
            match entry {
                Samples::Unsynthesizable(why) => {
                    let reason = format!("not_synthesizable:{}", why.reason);
                    count_candidate(&mut report.tv, name, Some(reason));
                }
                Samples::Ready(..) if steps_left == 0 => {
                    count_candidate(&mut report.tv, name, Some("over_budget".to_string()));
                }
                Samples::Ready(harness, current) => {
                    if harness.driven() {
                        report.tv.function_passes_driven += 1;
                    }
                    if current.is_none() {
                        let inputs: Vec<usize> = (0..harness.inputs()).collect();
                        let before = steps_left;
                        let runs = run_inputs(
                            view,
                            harness,
                            &inputs,
                            &[],
                            config.differential,
                            &mut steps_left,
                        );
                        report.tv.steps = report.tv.steps.saturating_add(before - steps_left);
                        *current = Some(runs.into_iter().map(|(_, run)| run).collect());
                    }
                    let source_runs = current.as_deref().unwrap_or_default();
                    // The candidate runs in the function's place.
                    std::mem::swap(&mut view.functions[index], &mut target_view);
                    let before = steps_left;
                    let target_runs = run_target(
                        view,
                        harness,
                        source_runs,
                        config.differential,
                        &mut steps_left,
                    );
                    std::mem::swap(&mut view.functions[index], &mut target_view);
                    report.tv.steps = report.tv.steps.saturating_add(before - steps_left);
                    let mut mismatch: Option<(String, Option<String>)> = None;
                    let mut compared = false;
                    let mut terminated = false;
                    for (i, source) in source_runs.iter().enumerate() {
                        let target = target_runs
                            .get(i)
                            .and_then(Option::as_ref)
                            .map_or(&InputOutcome::OverBudget, |run| &run.outcome);
                        match compare_input(&source.outcome, target) {
                            InputVerdict::Compared {
                                observed: Observed::Termination,
                            } => {
                                terminated = true;
                                report.tv.samples_nothing_observed += 1;
                            }
                            InputVerdict::Compared { observed } => {
                                compared = true;
                                report.tv.samples_compared += 1;
                                if observed == Observed::Memory {
                                    report.tv.samples_memory_compared += 1;
                                    if source.reading.narrowed() {
                                        report.tv.samples_memory_narrowed += 1;
                                    }
                                }
                                if harness.is_aliased(i) {
                                    report.tv.samples_aliased_compared += 1;
                                }
                            }
                            InputVerdict::Excluded(outcome) => match outcome {
                                InputOutcome::Undefined => report.tv.samples_ub_excluded += 1,
                                InputOutcome::Invalid => report.tv.samples_invalid += 1,
                                InputOutcome::OverBudget => report.tv.samples_over_budget += 1,
                                InputOutcome::NotExecuted(code) => {
                                    report.tv.samples_not_executed += 1;
                                    *report.tv.not_executed.entry(code).or_default() += 1;
                                }
                                _ => {}
                            },
                            InputVerdict::Mismatch(why) => {
                                if mismatch.is_none() {
                                    mismatch =
                                        Some((format!("input {i}: {why}"), unfinished(target)));
                                }
                            }
                        }
                    }
                    if let Some((mismatch, unfinished)) = mismatch {
                        let function = working.functions[index].name.clone();
                        // Compared and found to disagree when the candidate's
                        // run reached a verdict; otherwise counted by why not.
                        let reason = unfinished.filter(|_| !compared);
                        count_candidate(&mut report.tv, name, reason);
                        report.record_rollback(
                            name,
                            &function,
                            format!("differential: {mismatch}"),
                        );
                        rules_rolled_back(&mut report, name, &witness);
                        working.types.truncate(tables.0);
                        working.globals.truncate(tables.1);
                        working.func_types.truncate(functions.0);
                        working.functions.truncate(functions.1);
                        view.types.truncate(tables.0);
                        view.globals.truncate(tables.1);
                        view.func_types.truncate(functions.0);
                        view.functions.truncate(functions.1);
                        continue;
                    }
                    let reason = (!compared).then(|| not_compared_reason(source_runs, terminated));
                    count_candidate(&mut report.tv, name, reason);
                    // The candidate's runs become the current body's; an
                    // input it was not run on keeps the source's outcome.
                    let merged: Vec<InputRun> = source_runs
                        .iter()
                        .zip(target_runs)
                        .map(|(source, target)| target.unwrap_or_else(|| source.clone()))
                        .collect();
                    *current = Some(merged);
                }
            }
            kept.functions_changed += 1;
            kept.exact += verdict.exact;
            kept.refinements += verdict.refinements;
            add_counts(&mut kept.rules, &rule_counts(&witness));
            view.functions[index] = target_view;
            if let PassWitness::Inline(w) = &witness {
                for site in &w.sites {
                    if let Some(callee) = working.function_by_id(site.callee) {
                        report.inlined.insert(callee.name.clone());
                    }
                }
            }
            let old = std::mem::replace(&mut working.functions[index], target);
            changed.push((index, old));
        }
        if changed.is_empty() {
            continue;
        }
        // ---- Proof-table transport for the whole pass.
        let mut before = working.clone();
        for (index, old) in &changed {
            before.functions[*index] = old.clone();
        }
        report.proof_table.transactions += 1;
        before.func_types.truncate(functions_before.0);
        before.functions.truncate(functions_before.1);
        match transport(&before, &working, name, preserved_rows(&before)) {
            Ok(validation) => {
                // The functions the pass appended join every later pass.
                eligible.extend(functions_before.1..working.functions.len());
                report.proof_table.validated += 1;
                report.proof_table.preserved += validation.preserved;
                report.proof_table.remapped += validation.remapped;
                report.proof_table.invalidated += validation.invalidated;
                if let Some(stats) = report.passes.iter_mut().find(|p| p.name == name) {
                    stats.functions_changed += kept.functions_changed;
                    stats.exact += kept.exact;
                    stats.refinements += kept.refinements;
                    add_counts(&mut stats.rules, &kept.rules);
                }
            }
            Err(why) => {
                report.proof_table.rejected += 1;
                if let Some(stats) = report.passes.iter_mut().find(|p| p.name == name) {
                    add_counts(&mut stats.rules_rolled_back, &kept.rules);
                }
                working.types.truncate(tables_before.0);
                working.globals.truncate(tables_before.1);
                working.func_types.truncate(functions_before.0);
                working.functions.truncate(functions_before.1);
                if let Some(view) = view.as_mut() {
                    view.types.truncate(tables_before.0);
                    view.globals.truncate(tables_before.1);
                    view.func_types.truncate(functions_before.0);
                    view.functions.truncate(functions_before.1);
                }
                samples.retain(|index, _| *index < functions_before.1);
                for (index, old) in changed {
                    let function = old.name.clone();
                    if let Some(view) = view.as_mut() {
                        view.functions[index] =
                            interpretable(view, &old).unwrap_or_else(|| old.clone());
                    }
                    working.functions[index] = old;
                    samples.remove(&index);
                    report.record_rollback(name, &function, format!("proof_table: {why}"));
                }
            }
        }
    }

    // Functions changed, and those appended (argument promotion's clones).
    report.functions_changed = module
        .functions
        .iter()
        .zip(&working.functions)
        .filter(|(a, b)| a != b)
        .count()
        + (working.functions.len() - module.functions.len());
    report.allocas_before = allocas(module);
    report.allocas_after = allocas(&working);
    report.globals_added = working.globals.len() - module.globals.len();
    (working, report)
}

/// Every obligation of `before`, `Preserved` under its own id: the only
/// disposition this mid-end produces, because it never touches a function an
/// obligation names.
pub(crate) fn preserved_rows(before: &Module) -> Vec<ProofObligationTransform> {
    before
        .proof_obligations
        .iter()
        .map(|obligation| ProofObligationTransform {
            source: obligation.id,
            disposition: ProofObligationDisposition::Preserved {
                target: obligation.id,
            },
        })
        .collect()
}

/// The pass's proof-table transaction from `before` to `after` with `rows`,
/// validated by trust-ir (with its rejecting authority: no new strong fact).
pub(crate) fn transport(
    before: &Module,
    after: &Module,
    pass: &str,
    rows: Vec<ProofObligationTransform>,
) -> Result<ProofTableTransformValidation, String> {
    let transform = ProofTransform::new(
        ProofTransformStage::TrustIrOptimization,
        format!("irmid:{pass}"),
        PRODUCER,
        env!("CARGO_PKG_VERSION"),
    );
    ProofTableTransformTransaction::new(transform, before, after, rows, Vec::new())
        .validate(before, after)
        .map_err(|errors| {
            errors
                .first()
                .map_or_else(|| "rejected".to_string(), ToString::to_string)
        })
}

/// The `alloca` instructions of `module`'s functions.
fn allocas(module: &Module) -> usize {
    module
        .functions
        .iter()
        .flat_map(|f| &f.blocks)
        .flat_map(|b| &b.body)
        .filter(|n| matches!(n.inst, trust_ir::Inst::Alloca { .. }))
        .count()
}

/// A per-function seed, so a function's inputs do not depend on its position.
fn seed_of(name: &str) -> u64 {
    // FNV-1a.
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    for byte in name.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0100_0000_01b3);
    }
    hash
}
