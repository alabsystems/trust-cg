// trust-cg-codegen/wasm/mid.rs - the trust-ir mid-end on the wasm32 lane
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Runs `trust_cg_irmid` (profile `Wasm32`) on a module this lane has already
//! admitted, at O1 and above, and decides whether its output is emitted.
//!
//! The optimized module is used only when
//!
//! 1. trust-ir's validator (`trust_ir_build::validate_module`) reports no
//!    finding kind more often on it than on the input, and, when it reports
//!    any finding at all, function-local validation
//!    (`trust_ir_build::validate_function`) of each function the mid-end
//!    changed reports no finding (compared by its full text) that it does not
//!    report on that function's input — so a finding a rewrite introduces in
//!    one function is not offset by one a removal drops in another, and a
//!    module the producer handed over with findings the admission tolerates
//!    gains none;
//! 2. it passes the same codegen admission and contract-surface refusals the
//!    input passed (the caller's `admit`), so no rewrite can turn a refused
//!    construct into an admitted one — the input itself was admitted first,
//!    and a refused input never reaches the mid-end; and
//! 3. the lane lowers it, its static data fits the memory layout the input
//!    was given (below), and the CFG structural invariant is not refuted on
//!    its bytes (the caller lowers the input instead on any lowering error,
//!    misfit or refutation).
//!
//! **Static data.** Constant-table promotion moves a table from a frame into
//! new static data. In memory the module owns, static data sits below the
//! shadow stack, so it would shorten the stack the input was given, and in a
//! host-reserved region it would write past what the host reserved. It
//! therefore runs only where the layout is fitted to the module emitted: an
//! object (the linker places data and stack apart) and the sized closed
//! module (`compile_sized_closed_module_*`, the CLI's route), whose pages are
//! grown so that the optimized module keeps at least the input's stack.
//! Under a caller's fixed policy it is withheld, and an optimized module
//! whose static data still outgrows the input's falls back to the input.
//!
//! The caller also lowers the INPUT whenever the mid-end changed something,
//! and returns its refusal: the lane refuses a construct even in dead code or
//! an unreachable block, and removing that code must not make the program
//! compile. So the admission and lowering refusals are the same with and
//! without the mid-end: every check the optimized module must pass falls back
//! to the input rather than refusing, and every such refusal is the input's.
//! An entry that reports the CFG structural invariant also checks it on that
//! lowering of the input (its baseline bodies, without the local emission
//! pass) when it emits the optimized module, and fails the compile when it is
//! refuted there; without the mid-end the invariant is checked on the
//! emitted bytes, local emission included.
//!
//! A function the mid-end appends (argument promotion's clones, after the
//! input's functions) has no input to compare with: rule 1 then requires
//! that function-local validation reports no finding in it at all.
//!
//! When rule 1 or 2 refuses an output, the mid-end runs again, each step at
//! most once and in this order, withdrawing only what may have caused it:
//!
//! 1. if argument promotion appended clones (a clone copies its callee's
//!    body, validation findings included, and a promoted caller's slot
//!    passes on to scalar replacement): with the callees left unpromoted of
//!    every clone whose own body carries a finding (function-local, or
//!    module-level with every other body removed), or that a function with a
//!    new function-local finding calls. No such callee skips the step;
//! 2. if the inliner spliced any call (a splice copies its callee's body,
//!    validation findings included; the refusal need not come from a
//!    splice): with every spliced callee whose own body carries a finding
//!    left called. No such callee skips the step;
//! 3. if a loop pass (closed-form induction, full or interval-bounded
//!    unrolling, invariant code motion, strength reduction), block merging,
//!    field-access lowering or the select-branch rules changed a function (they copy instructions, move them to another
//!    block or give a result a new type, validation findings included, and
//!    a finding's text names its block): once without them
//!    ([`MidConfig::loop_passes`]); that output is emitted when it passes,
//!    and otherwise the steps below go on from the refused one, the loop
//!    passes kept;
//! 4. if the inliner still spliced a call: without the inliner;
//! 5. if the output still has clones: without argument promotion.
//!
//! Steps 1 and 2 come first because they withdraw the least: field-access
//! lowering makes callees inlinable whose other findings a splice then
//! copies, and leaving those callees called keeps the loop passes.
//! A refusal no clone is blamed for withdraws the inliner's splices
//! before the whole of argument promotion. The final report names every
//! withdrawal of every run in `passes_withheld` (`loop_passes`,
//! `argpromo_callees`, `inline_callees`, `inline`, `argpromo`), and only the
//! last output's refusal falls back to the input.
//!
//! Each fallback is recorded in the report; none refuses the program. At O0,
//! or with the mid-end switched off by the caller ([`WasmOptOptions`]), the
//! input is lowered unchanged and the bytes are those of the lane without a
//! mid-end.

use std::collections::{BTreeMap, BTreeSet};

use trust_cg_irmid::{IrmidReport, MidConfig, MidProfile, optimize_module};
use trust_ir::Module;

use super::lower::WasmLowerError;
use crate::pipeline::OptLevel;

/// What a wasm32 compile optimizes: the level selects both the trust-ir
/// mid-end and the local emission pass (O0 runs neither); `mid_end: false`
/// switches the mid-end off at any level (the bridge's `no-wasm-irmid` knob).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WasmOptOptions {
    pub level: OptLevel,
    pub mid_end: bool,
}

impl WasmOptOptions {
    /// Everything `level` runs.
    pub const fn at(level: OptLevel) -> Self {
        Self {
            level,
            mid_end: true,
        }
    }
}

/// The producer's side table beside the module, for what trust-ir has no
/// field for: the link symbols of the functions the mid-end's inliner never
/// splices (the rustc bridge fills it with every `#[inline(never)]` and
/// every `#[cold]` function of the session; a call of one stays a call), and
/// whether the session withholds the `multivalue` target feature.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct WasmInlineHints {
    pub never_inline: BTreeSet<String>,
    /// The producer's session withholds the `multivalue` target feature
    /// (rustc's `-C target-cpu=mvp` without a later `+multivalue`, or a
    /// last `-C target-feature=-multivalue`): the object lane then plans no
    /// internal multi-value ABI, every function keeps its C form and the
    /// object declares no `+multivalue`. The default (`false`) lets the lane
    /// use the feature at O1 and above.
    ///
    /// Pending owner sign-off: a new public field (P6 stage B), not a final
    /// contract.
    pub without_multivalue: bool,
}

/// Whether the memory layout a compile emits can grow its static data.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum StaticDataRoom {
    /// The layout is fitted to the module emitted: an object, whose data the
    /// linker places, or a closed module whose memory is sized for its own
    /// static data plus the input's stack.
    Grows,
    /// The caller fixed the layout; the reason a new static datum would not
    /// fit (it would come out of the stack, or overrun a host's region).
    Fixed(&'static str),
}

/// The optimized module to lower, if the mid-end changed something and its
/// output passed the re-validation above, and the report.
///
/// `static_data` says whether the caller's memory layout can take static data
/// the input does not have; when it cannot, constant-table promotion (the one
/// pass that adds any) is withheld and the report says why. `hints` names
/// the functions the inliner leaves called.
pub(super) fn optimize(
    module: &Module,
    options: WasmOptOptions,
    static_data: StaticDataRoom,
    hints: &WasmInlineHints,
    admit: impl Fn(&Module) -> Result<(), WasmLowerError>,
) -> (Option<Module>, IrmidReport) {
    if options.level == OptLevel::O0 {
        return (
            None,
            IrmidReport::not_run(MidProfile::Wasm32, "O0 runs no mid-end"),
        );
    }
    if !options.mid_end {
        return (
            None,
            IrmidReport::not_run(MidProfile::Wasm32, "switched off by the caller"),
        );
    }
    let mut config = MidConfig {
        promote_constant_tables: static_data == StaticDataRoom::Grows,
        never_inline: hints.never_inline.clone(),
        ..MidConfig::wasm32()
    };
    let run = |config: &MidConfig| {
        let (candidate, mut report) = optimize_module(module, config);
        if let StaticDataRoom::Fixed(why) = static_data {
            // This policy withholds the passes that append static data
            // (constant-table promotion and the CRC-table rewrite), not every
            // independently withheld pass or its original reason.
            for pass in ["ctp", "crc_table"] {
                if let Some(reason) = report.passes_withheld.get_mut(pass) {
                    *reason = why.to_string();
                }
            }
        }
        (candidate, report)
    };
    let (mut candidate, mut report) = run(&config);
    // At most six runs: with argument promotion and the inliner, without
    // the unclean clones' callees, without the unclean inlined callees,
    // without the loop passes, without the inliner, without argument
    // promotion (module docs).
    // Each run's report replaces the last, so the withdrawals made so far are
    // carried into every later one.
    let mut excluded = false;
    let mut clones_excluded = false;
    let mut loops_tried = false;
    let mut withdrawn: Vec<(&'static str, String)> = Vec::new();
    let refusal_of = |candidate: &Module| match new_validation_finding(module, candidate) {
        Some(kind) => Some(format!(
            "trust-ir's validator reports a finding on the optimized module that the input \
             lacks: {kind}"
        )),
        None => admit(candidate)
            .err()
            .map(|error| format!("the codegen admission refused the optimized module: {error}")),
    };
    loop {
        if report.functions_changed == 0 {
            return (None, report);
        }
        let Some(why) = refusal_of(&candidate) else {
            return (Some(candidate), report);
        };
        let clones = config.arg_promotion && candidate.functions.len() > module.functions.len();
        // Step 1: a clone copies its callee's body, validation findings
        // included, and its callers' slots become promotable. The mid-end
        // runs again with the callees of the clones blamed for a finding
        // left unpromoted; when no clone is blamed, the step is skipped.
        if clones && !clones_excluded {
            clones_excluded = true;
            let unclean = unclean_clone_callees(module, &candidate);
            if !unclean.is_empty() {
                let names: Vec<&str> = unclean.iter().map(String::as_str).collect();
                let note = format!(
                    "callees left unpromoted ({}) after an output with their clones was \
                     refused: {why}",
                    names.join(", ")
                );
                config.no_arg_promotion.extend(unclean);
                withdrawn.push(("argpromo_callees", note));
                (candidate, report) = run(&config);
                report.passes_withheld.extend(withdrawn.iter().cloned());
                continue;
            }
        }
        // Step 2: a splice copies its callee's body, validation findings
        // included. The mid-end runs again with every spliced callee whose
        // own body carries a finding left called; when none does, the step
        // is skipped.
        if config.inline && !excluded && !report.inlined.is_empty() {
            excluded = true;
            let unclean = findings_of(module, &report.inlined);
            if !unclean.is_empty() {
                let names: Vec<&str> = unclean.iter().map(String::as_str).collect();
                let note = format!(
                    "callees whose bodies carry a validation finding left called ({}) after \
                     an output with them was refused: {why}",
                    names.join(", ")
                );
                config.never_inline.extend(unclean);
                withdrawn.push(("inline_callees", note));
                (candidate, report) = run(&config);
                report.passes_withheld.extend(withdrawn.iter().cloned());
                continue;
            }
        }
        // Step 3: the loop passes, block merging and field-access lowering
        // copy instructions, move them to another block or retype a result,
        // findings included. One run without them is tried; it is emitted
        // when it passes, and otherwise the steps below go on from this
        // output with them kept.
        if config.loop_passes && !loops_tried && loop_passes_changed(&report) {
            loops_tried = true;
            let alt_config = MidConfig {
                loop_passes: false,
                ..config.clone()
            };
            let (alt, mut alt_report) = run(&alt_config);
            if alt_report.functions_changed > 0 && refusal_of(&alt).is_none() {
                alt_report.passes_withheld.extend(withdrawn.iter().cloned());
                alt_report.passes_withheld.insert(
                    "loop_passes",
                    format!("withdrawn after an output with them was refused: {why}"),
                );
                return (Some(alt), alt_report);
            }
        }
        // Step 4: without the inliner, while it spliced something.
        if config.inline && !report.inlined.is_empty() {
            excluded = true;
            config.inline = false;
            withdrawn.push((
                "inline",
                format!("withdrawn after an output with it was refused: {why}"),
            ));
            (candidate, report) = run(&config);
            report.passes_withheld.extend(withdrawn.iter().cloned());
            continue;
        }
        // Step 5: without argument promotion, before the input is emitted
        // instead.
        if clones {
            config.arg_promotion = false;
            withdrawn.push((
                "argpromo",
                format!("withdrawn after an output with its clones was refused: {why}"),
            ));
            (candidate, report) = run(&config);
            report.passes_withheld.extend(withdrawn.iter().cloned());
            continue;
        }
        report.fall_back(why);
        return (None, report);
    }
}

/// Whether a pass [`MidConfig::loop_passes`] withholds changed a function.
fn loop_passes_changed(report: &IrmidReport) -> bool {
    report.passes.iter().any(|p| {
        p.functions_changed > 0
            && matches!(
                p.name,
                "loop_cf"
                    | "unroll"
                    | "bounded_unroll"
                    | "licm"
                    | "iv_sr"
                    | "merge"
                    | "field_access"
                    | "select_branch"
            )
    })
}

/// The callees of the clones (functions `candidate` appends after `source`'s,
/// named `<prefix>.tcg.ap<h>.tcg.crate.<tag>` for callee
/// `<prefix>.tcg.crate.<tag>`) whose own body carries a validation finding
/// (function-local, or module-level with every other body removed, such as
/// an `EntryParamsMismatch` that needs the module's signatures), or that a
/// function with a new function-local finding calls.
fn unclean_clone_callees(source: &Module, candidate: &Module) -> BTreeSet<String> {
    use trust_cg_verify::trust_ir_mid_tv::ARGPROMO_CLONE_MARK;
    use trust_cg_verify::wasm_internal_abi::CRATE_PRIVATE_MARK;
    let callee_of = |clone: &str| -> Option<String> {
        let at = clone.rfind(ARGPROMO_CLONE_MARK)?;
        let rest = &clone[at + ARGPROMO_CLONE_MARK.len()..];
        let tail = rest.find(CRATE_PRIVATE_MARK)?;
        Some(format!("{}{}", &clone[..at], &rest[tail..]))
    };
    let inputs: BTreeMap<_, _> = source.functions.iter().map(|f| (f.id, f)).collect();
    let clones: BTreeMap<_, _> = candidate
        .functions
        .iter()
        .filter(|f| !inputs.contains_key(&f.id))
        .filter_map(|f| Some((f.id, callee_of(&f.name)?)))
        .collect();
    let clone_names: BTreeSet<String> = candidate
        .functions
        .iter()
        .filter(|f| clones.contains_key(&f.id))
        .map(|f| f.name.clone())
        .collect();
    let unclean_clones = findings_of(candidate, &clone_names);
    let mut out: BTreeSet<String> = candidate
        .functions
        .iter()
        .filter(|f| unclean_clones.contains(&f.name))
        .filter_map(|f| clones.get(&f.id).cloned())
        .collect();
    for output in &candidate.functions {
        let mut allowed: BTreeMap<String, usize> = BTreeMap::new();
        if let Some(input) = inputs.get(&output.id) {
            if *input == output {
                continue;
            }
            for error in trust_ir_build::validate_function(input) {
                *allowed.entry(format!("{error:?}")).or_default() += 1;
            }
        }
        let new = trust_ir_build::validate_function(output)
            .iter()
            .any(|error| match allowed.get_mut(&format!("{error:?}")) {
                Some(count) if *count > 0 => {
                    *count -= 1;
                    false
                }
                _ => true,
            });
        if !new {
            continue;
        }
        if let Some(callee) = clones.get(&output.id) {
            out.insert(callee.clone());
        }
        for node in output.blocks.iter().flat_map(|b| &b.body) {
            if let trust_ir::Inst::Call { callee, .. } = &node.inst
                && let Some(name) = clones.get(callee)
            {
                out.insert(name.clone());
            }
        }
    }
    out
}

/// The functions named in `names` whose own body (in `module`) trust-ir's
/// validator reports a finding in: validated with every other body removed,
/// compared by kind with the module with every body removed.
fn findings_of(module: &Module, names: &BTreeSet<String>) -> BTreeSet<String> {
    let census = |module: &Module| {
        let mut kinds: BTreeMap<String, usize> = BTreeMap::new();
        for error in trust_ir_build::validate_module(module) {
            *kinds.entry(finding_kind(&error)).or_default() += 1;
        }
        kinds
    };
    let mut bare = module.clone();
    for func in &mut bare.functions {
        func.blocks.clear();
    }
    let baseline = census(&bare);
    let mut out = BTreeSet::new();
    for (index, func) in module.functions.iter().enumerate() {
        if !names.contains(&func.name) || func.is_declaration() {
            continue;
        }
        let mut one = bare.clone();
        one.functions[index] = func.clone();
        let found = census(&one);
        if found
            .iter()
            .any(|(kind, n)| baseline.get(kind).copied().unwrap_or(0) < *n)
        {
            out.insert(func.name.clone());
        }
    }
    out
}

/// The variant name of a validation finding (its `Debug` spelling up to the
/// first non-identifier character).
fn finding_kind(error: &trust_ir_build::ValidationError) -> String {
    let text = format!("{error:?}");
    text.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .next()
        .unwrap_or_default()
        .to_string()
}

/// A validation finding `candidate` has that `source` does not (rule 1 of
/// the module documentation), described for the fallback reason.
fn new_validation_finding(source: &Module, candidate: &Module) -> Option<String> {
    let census = |module: &Module| {
        let mut kinds: BTreeMap<String, usize> = BTreeMap::new();
        for error in trust_ir_build::validate_module(module) {
            *kinds.entry(finding_kind(&error)).or_default() += 1;
        }
        kinds
    };
    // The input is validated only when the output has a finding to compare:
    // a clean output (the common case) costs one validation.
    let after = census(candidate);
    if after.is_empty() {
        return None;
    }
    let before = census(source);
    if let Some((kind, _)) = after
        .into_iter()
        .find(|(kind, count)| before.get(kind).copied().unwrap_or(0) < *count)
    {
        return Some(format!("`{kind}` (more often on the module)"));
    }
    new_function_local_finding(source, candidate)
}

/// A function-local validation finding (by full text) that a function the
/// mid-end changed has in `candidate` and not in `source`, or any finding in
/// a function it appended. Functions are paired by id; the mid-end removes
/// none, and appends only argument promotion's clones.
fn new_function_local_finding(source: &Module, candidate: &Module) -> Option<String> {
    let inputs: BTreeMap<_, _> = source.functions.iter().map(|f| (f.id, f)).collect();
    for output in &candidate.functions {
        let Some(input) = inputs.get(&output.id) else {
            if let Some(error) = trust_ir_build::validate_function(output).first() {
                return Some(format!(
                    "`{}` in appended function `{}`",
                    finding_kind(error),
                    output.name
                ));
            }
            continue;
        };
        if *input == output {
            continue;
        }
        let mut allowed: BTreeMap<String, usize> = BTreeMap::new();
        for error in trust_ir_build::validate_function(input) {
            *allowed.entry(format!("{error:?}")).or_default() += 1;
        }
        for error in trust_ir_build::validate_function(output) {
            match allowed.get_mut(&format!("{error:?}")) {
                Some(count) if *count > 0 => *count -= 1,
                _ => {
                    return Some(format!(
                        "`{}` in function `{}`",
                        finding_kind(&error),
                        output.name
                    ));
                }
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    const HEADER: &str = "; TrustIr text format v1\nmodule \"mid\"\n\
                          target \"wasm32-unknown-unknown\" 4 little\n\n\
                          functy.0 = (i32) -> (i32)\n\n";
    const CLEAN: &str = "bb0(%0: i32):\n    ret %0\n";
    /// `bb1` is unreachable: trust-ir's validator reports `UnreachableBlock(1)`.
    const DEAD_BLOCK: &str = "bb0(%0: i32):\n    ret %0\nbb1:\n    ret %0\n";

    fn module(a: &str, b: &str) -> Module {
        let text = format!("{HEADER}fn @a(functy.0) {{\n{a}}}\n\nfn @b(functy.0) {{\n{b}}}\n");
        trust_ir::parser::parse_module(&text)
            .unwrap_or_else(|e| panic!("test module failed to parse: {e}\n{text}"))
    }

    /// A finding introduced in one function is not offset by an identical
    /// one removed from another: the module-wide census is unchanged, the
    /// per-function comparison refuses it.
    #[test]
    fn a_new_finding_offset_by_a_removed_one_is_refused() {
        let source = module(CLEAN, DEAD_BLOCK);
        let moved = module(DEAD_BLOCK, CLEAN);
        let census = |m: &Module| {
            let mut kinds: Vec<String> = trust_ir_build::validate_module(m)
                .iter()
                .map(finding_kind)
                .collect();
            kinds.sort();
            kinds
        };
        assert_eq!(census(&source), census(&moved));
        assert!(census(&source).contains(&"UnreachableBlock".to_string()));
        let found = new_validation_finding(&source, &moved).expect("refused");
        assert!(
            found.contains("UnreachableBlock") && found.contains("`a`"),
            "{found}"
        );
    }

    /// Removing a finding, or changing nothing, is accepted.
    #[test]
    fn removing_a_finding_is_accepted() {
        let source = module(CLEAN, DEAD_BLOCK);
        assert_eq!(new_validation_finding(&source, &source), None);
        assert_eq!(new_validation_finding(&source, &module(CLEAN, CLEAN)), None);
    }

    /// `@a` calls `@b`, whose input body carries a validation finding (an
    /// unreachable block), and then the clean `@c`; both are tiny.
    fn caller_of_an_unclean_and_a_clean_callee() -> Module {
        let text = format!(
            "{HEADER}fn @a(functy.0) {{\nbb0(%0: i32):\n    %1 = call @func.1(%0)\n    \
             %2 = call @func.2(%1)\n    ret %2\n}}\n\n\
             fn @b(functy.0) {{\n{DEAD_BLOCK}}}\n\n\
             fn @c(functy.0) {{\nbb0(%0: i32):\n    %1 = mul i32 %0, %0\n    ret %1\n}}\n"
        );
        trust_ir::parser::parse_module(&text)
            .unwrap_or_else(|e| panic!("test module failed to parse: {e}\n{text}"))
    }

    /// Whether `@a` of `module` still calls `@b` (func.1).
    fn a_calls_b(module: &Module) -> bool {
        let a = module.functions.iter().find(|f| f.name == "a").unwrap();
        a.blocks.iter().flat_map(|b| &b.body).any(|n| {
            matches!(&n.inst, trust_ir::Inst::Call { callee, .. }
                if *callee == trust_ir::FuncId::new(1))
        })
    }

    fn refusal() -> WasmLowerError {
        WasmLowerError::UnsupportedInst("refused by the test's admission".into())
    }

    #[test]
    fn fixed_static_room_preserves_independent_withholding_reasons() {
        let m = caller_of_an_unclean_and_a_clean_callee();
        let snapshot = m.clone();
        let why = "the caller reserved no additional static bytes";
        let (_, report) = optimize(
            &m,
            WasmOptOptions::at(OptLevel::O2),
            StaticDataRoom::Fixed(why),
            &WasmInlineHints::default(),
            |_| Ok(()),
        );
        assert_eq!(report.passes_withheld["ctp"], why);
        assert_eq!(report.passes_withheld["crc_table"], why);
        assert!(report.passes_withheld["fill_call"].contains("source-bound helper"));
        assert_ne!(report.passes_withheld["fill_call"], why);
        assert!(report.passes_withheld["mem_cmp"].contains("OD-164"));
        assert_ne!(report.passes_withheld["mem_cmp"], why);
        assert_eq!(m, snapshot);
    }

    /// An output refused because of a splice is tried again with the
    /// spliced callee whose body carries a finding left called; the clean
    /// callee stays spliced, and the report names the withdrawal.
    #[test]
    fn a_refused_splice_reruns_without_the_unclean_callee() {
        let m = caller_of_an_unclean_and_a_clean_callee();
        let (out, report) = optimize(
            &m,
            WasmOptOptions::at(OptLevel::O2),
            StaticDataRoom::Grows,
            &WasmInlineHints::default(),
            |candidate| {
                if a_calls_b(candidate) {
                    Ok(())
                } else {
                    Err(refusal())
                }
            },
        );
        let out = out.expect("the second run's output is admitted");
        assert!(a_calls_b(&out));
        assert_eq!(report.fallback, None);
        assert_eq!(report.inlined, BTreeSet::from(["c".to_string()]));
        let note = report
            .passes_withheld
            .get("inline_callees")
            .expect("the withdrawal is named");
        assert!(note.contains("(b)") && note.contains("refused"), "{note}");
        assert!(!report.passes_withheld.contains_key("inline"));
    }

    /// When the output without the unclean callees is refused too, the
    /// third run has no inliner, and its report names both withdrawals
    /// (each run's report replaces the last); its refusal falls back to the
    /// input.
    #[test]
    fn a_third_run_keeps_both_withdrawals_and_falls_back() {
        let m = caller_of_an_unclean_and_a_clean_callee();
        let (out, report) = optimize(
            &m,
            WasmOptOptions::at(OptLevel::O2),
            StaticDataRoom::Grows,
            &WasmInlineHints::default(),
            |_| Err(refusal()),
        );
        assert!(out.is_none());
        assert!(report.inlined.is_empty(), "{:?}", report.inlined);
        let callees = report
            .passes_withheld
            .get("inline_callees")
            .expect("the second run's withdrawal is kept");
        assert!(callees.contains("(b)"), "{callees}");
        let inline = report
            .passes_withheld
            .get("inline")
            .expect("the third run's withdrawal is named");
        assert!(inline.starts_with("withdrawn"), "{inline}");
        assert!(
            report.functions_changed == 0 || report.fallback.is_some(),
            "{report:?}"
        );
    }

    /// `@f` passes a slot to `@g`, a crate-private hidden callee the
    /// inliner leaves (named in the side table) whose body reads it and
    /// adds an `i32` to a `u32` constant at `u32`: trust-ir's validator
    /// reports that operation (`BinOpTypeMismatch`), no pass respells it,
    /// and a clone of `@g` copies the finding.
    fn caller_of_a_promotable_unclean_callee() -> Module {
        let text = "; TrustIr text format v1\nmodule \"mid\"\n\
                    target \"wasm32-unknown-unknown\" 4 little\n\n\
                    functy.0 = (ptr) -> (u32)\nfuncty.1 = (i32) -> (u32)\n\n\
                    fn @g.tcg.crate.0000000000000001(functy.0) {\n    ; #visibility: hidden\n\
                    bb0(%0: ptr):\n    %1 = load i32, ptr %0\n    %3 = const u32 5\n    \
                    %2 = add u32 %1, %3\n    ret %2\n}\n\n\
                    fn @f(functy.1) {\nbb0(%0: i32):\n    %1 = alloca i32\n    \
                    store i32 %0, ptr %1\n    %2 = call @func.0(%1)\n    ret %2\n}\n";
        trust_ir::parser::parse_module(text)
            .unwrap_or_else(|e| panic!("test module failed to parse: {e}\n{text}"))
    }

    /// An output refused because a clone copied its callee's finding is
    /// tried again with that callee left unpromoted; the report names the
    /// withdrawal and the output appends no function.
    #[test]
    fn a_refused_clone_reruns_without_its_callee() {
        let m = caller_of_a_promotable_unclean_callee();
        let hints = WasmInlineHints {
            never_inline: BTreeSet::from(["g.tcg.crate.0000000000000001".to_string()]),
            ..WasmInlineHints::default()
        };
        let (out, report) = optimize(
            &m,
            WasmOptOptions::at(OptLevel::O2),
            StaticDataRoom::Grows,
            &hints,
            |_| Ok(()),
        );
        let note = report
            .passes_withheld
            .get("argpromo_callees")
            .expect("the withdrawal is named");
        assert!(
            note.contains("(g.tcg.crate.0000000000000001)") && note.contains("BinOpTypeMismatch"),
            "{note}"
        );
        assert!(!report.passes_withheld.contains_key("argpromo"));
        assert_eq!(report.fallback, None);
        if let Some(out) = out {
            assert_eq!(
                out.functions.len(),
                m.functions.len(),
                "no clone is appended"
            );
        }
    }

    /// `@a` calls `@b`, whose body carries a validation finding (the
    /// inliner splices it), and `@f` passes a slot to the clean
    /// crate-private `@g`, which the inliner leaves (argument promotion
    /// clones it).
    fn caller_of_an_unclean_splice_and_a_clean_promotion() -> Module {
        let text = format!(
            "; TrustIr text format v1\nmodule \"mid\"\n\
             target \"wasm32-unknown-unknown\" 4 little\n\n\
             functy.0 = (i32) -> (i32)\nfuncty.1 = (ptr) -> (i32)\n\n\
             fn @a(functy.0) {{\nbb0(%0: i32):\n    %1 = call @func.1(%0)\n    ret %1\n}}\n\n\
             fn @b(functy.0) {{\n{DEAD_BLOCK}}}\n\n\
             fn @g.tcg.crate.0000000000000001(functy.1) {{\n    ; #visibility: hidden\n\
             bb0(%0: ptr):\n    %1 = load i32, ptr %0\n    ret %1\n}}\n\n\
             fn @f(functy.0) {{\nbb0(%0: i32):\n    %1 = alloca i32\n    \
             store i32 %0, ptr %1\n    %2 = call @func.2(%1)\n    ret %2\n}}\n"
        );
        trust_ir::parser::parse_module(&text)
            .unwrap_or_else(|e| panic!("test module failed to parse: {e}\n{text}"))
    }

    /// A refusal no clone is blamed for withdraws the inliner's unclean
    /// callee first and keeps argument promotion: the output keeps its
    /// clone, and the report names `inline_callees` and neither argument
    /// promotion key.
    #[test]
    fn a_refusal_no_clone_is_blamed_for_keeps_argument_promotion() {
        let m = caller_of_an_unclean_splice_and_a_clean_promotion();
        let hints = WasmInlineHints {
            never_inline: BTreeSet::from(["g.tcg.crate.0000000000000001".to_string()]),
            ..WasmInlineHints::default()
        };
        let (out, report) = optimize(
            &m,
            WasmOptOptions::at(OptLevel::O2),
            StaticDataRoom::Grows,
            &hints,
            |candidate| {
                if a_calls_b(candidate) {
                    Ok(())
                } else {
                    Err(refusal())
                }
            },
        );
        let out = out.expect("the second run's output is admitted");
        assert!(a_calls_b(&out));
        assert_eq!(report.fallback, None);
        assert_eq!(
            out.functions.len(),
            m.functions.len() + 1,
            "the clone is kept: {:?}",
            report.passes_withheld
        );
        let note = report
            .passes_withheld
            .get("inline_callees")
            .expect("the inliner's withdrawal is named");
        assert!(note.contains("(b)"), "{note}");
        assert!(!report.passes_withheld.contains_key("argpromo"));
        assert!(!report.passes_withheld.contains_key("argpromo_callees"));
    }

    /// When the output stays refused after the inliner's withdrawal (here,
    /// any output with a clone), argument promotion is withdrawn last, and
    /// the report names both.
    #[test]
    fn argument_promotion_is_withdrawn_after_the_inliner() {
        let m = caller_of_an_unclean_splice_and_a_clean_promotion();
        let hints = WasmInlineHints {
            never_inline: BTreeSet::from(["g.tcg.crate.0000000000000001".to_string()]),
            ..WasmInlineHints::default()
        };
        let (out, report) = optimize(
            &m,
            WasmOptOptions::at(OptLevel::O2),
            StaticDataRoom::Grows,
            &hints,
            |candidate| {
                if candidate.functions.len() > 4 {
                    Err(refusal())
                } else {
                    Ok(())
                }
            },
        );
        for key in ["inline_callees", "argpromo"] {
            assert!(
                report.passes_withheld.contains_key(key),
                "{key}: {:?}",
                report.passes_withheld
            );
        }
        assert!(!report.passes_withheld.contains_key("argpromo_callees"));
        assert_eq!(report.fallback, None);
        // The last run changes nothing (no splice, no clone): the input is
        // lowered, and no fallback is recorded.
        if let Some(out) = out {
            assert_eq!(out.functions.len(), m.functions.len(), "no clone");
        }
    }

    /// A clone whose entry parameter is of another pointer type than its
    /// declared one carries `EntryParamsMismatch`, which trust-ir reports
    /// only with the module's signatures; its callee is still blamed.
    #[test]
    fn a_clone_with_a_module_level_finding_blames_its_callee() {
        let base = "; TrustIr text format v1\nmodule \"mid\"\n\
                    target \"wasm32-unknown-unknown\" 4 little\n\n\
                    functy.0 = (ptr) -> (i32)\nfuncty.1 = (i32) -> (i32)\n\n\
                    fn @g.tcg.crate.0000000000000001(functy.0) {\n    ; #visibility: hidden\n\
                    bb0(%0: ptr):\n    %1 = load i32, ptr %0\n    ret %1\n}\n\n\
                    fn @f(functy.1) {\nbb0(%0: i32):\n    ret %0\n}\n";
        let clone = "\nfn @g.tcg.ap0000abcd.tcg.crate.0000000000000001(functy.0) {\n    \
                     ; #visibility: hidden\nbb0(%0: &mut i32):\n    %1 = const i32 7\n    \
                     ret %1\n}\n";
        let parse = |text: &str| {
            trust_ir::parser::parse_module(text)
                .unwrap_or_else(|e| panic!("test module failed to parse: {e}\n{text}"))
        };
        let source = parse(base);
        let candidate = parse(&format!("{base}{clone}"));
        let appended = candidate.functions.last().expect("the clone");
        let kinds = |errors: Vec<trust_ir_build::ValidationError>| -> Vec<String> {
            errors.iter().map(finding_kind).collect()
        };
        assert!(
            !kinds(trust_ir_build::validate_function(appended))
                .contains(&"EntryParamsMismatch".to_string()),
            "function-local validation does not see it"
        );
        assert!(
            kinds(trust_ir_build::validate_module(&candidate))
                .contains(&"EntryParamsMismatch".to_string())
        );
        assert_eq!(
            unclean_clone_callees(&source, &candidate),
            BTreeSet::from(["g.tcg.crate.0000000000000001".to_string()])
        );
    }
}
