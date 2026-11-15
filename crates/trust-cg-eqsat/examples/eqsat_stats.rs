// crates/trust-cg-eqsat/examples/eqsat_stats.rs - measures the Tier E engine over the interim corpus
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Runs the engine over every function of every module the corpus manifest
//! takes (`tests/corpus/MANIFEST.tsv`, docs/eqsat-tier-e.md section 9) and
//! prints what it did.
//!
//! ```text
//! eqsat_stats [--corpus DIR] [--reps N] [--json]
//! ```
//!
//! For each function: `optimize_function` with the shipped integer-identity
//! rules and `EngineConfig::default()`, the same with `RuleSet::empty()`, and
//! `round_trip`; each of the first and the last `N` times (default 5) for
//! timing and a determinism comparison. The report gives decline counts by
//! class, rewritten and unchanged functions, which rewrites name a rule in
//! their derivation and which need none (copy removal, hash-consing), rule
//! matches by rule, static costs (section 6) before and after, forms per
//! e-class, and the static cost of the no-rule round trip (the round-trip
//! body re-read by the engine's own reader). Rewritten and round-trip bodies
//! are substituted into their module and the module re-validated.
//!
//! Every line is a deterministic function of the corpus and the engine,
//! except the lines marked `[host-dependent]` (wall-clock time, measured with
//! `Instant` here in the example; the engine itself reads no clock). With
//! `--json` the same numbers are printed as one JSON object, the timing under
//! `host_dependent`.
//!
//! What this measures, and what not: the engine's own counters and its own
//! static cost model on this interim corpus. It does not run the checker
//! (`trust-cg-eqsat-check`), does not execute any body, and the derivation
//! walk below reads only the section 7.2 section sizes; none of it is
//! evidence that a rewrite is correct.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::{Duration, Instant};

use trust_cg_eqsat::rules::{INTEGER_IDENTITIES, RuleSet};
use trust_cg_eqsat::{Decline, EngineConfig, Optimized, optimize_function, round_trip};
use trust_ir::Function;

const MANIFEST_HEADER: &str = "status\tfile\tsource\treason";

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("eqsat_stats: {message}");
            ExitCode::from(2)
        }
    }
}

struct Args {
    corpus: PathBuf,
    /// How the report names the corpus: the crate-relative default, or the
    /// `--corpus` argument as given (never a host-specific absolute path the
    /// user did not type).
    corpus_label: String,
    reps: usize,
    json: bool,
}

fn arguments() -> Result<Args, String> {
    let usage = "usage: eqsat_stats [--corpus DIR] [--reps N] [--json]";
    let mut parsed = Args {
        corpus: Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus"),
        corpus_label: "crates/trust-cg-eqsat/tests/corpus".to_owned(),
        reps: 5,
        json: false,
    };
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--corpus" => {
                let corpus = args.next().ok_or(usage)?;
                parsed.corpus = PathBuf::from(&corpus);
                parsed.corpus_label = corpus;
            }
            "--reps" => {
                parsed.reps = args
                    .next()
                    .and_then(|n| n.parse().ok())
                    .filter(|n| *n >= 1)
                    .ok_or("--reps takes a positive integer")?;
            }
            "--json" => parsed.json = true,
            _ => return Err(format!("unexpected argument {arg:?}; {usage}")),
        }
    }
    Ok(parsed)
}

/// The `file` column of every `taken` row, in manifest order.
fn taken_files(corpus: &Path) -> Result<Vec<String>, String> {
    let path = corpus.join("MANIFEST.tsv");
    let text =
        std::fs::read_to_string(&path).map_err(|e| format!("read {}: {e}", path.display()))?;
    let mut lines = text.lines().filter(|line| !line.starts_with('#'));
    if lines.next() != Some(MANIFEST_HEADER) {
        return Err(format!(
            "{}: the header is not {MANIFEST_HEADER:?}",
            path.display()
        ));
    }
    let mut files = Vec::new();
    for line in lines {
        let fields: Vec<&str> = line.split('\t').collect();
        match fields.as_slice() {
            ["taken", file, _, _] => files.push((*file).to_owned()),
            ["left", "-", _, _] => {}
            _ => return Err(format!("{}: bad row {line:?}", path.display())),
        }
    }
    Ok(files)
}

/// Section sizes of a section 7.2 derivation: (rules, terms, proofs, claims).
/// Reads only enough of each entry to skip it; `None` when the bytes do not
/// have the version 1 layout.
fn derivation_shape(bytes: &[u8]) -> Option<[u64; 4]> {
    struct Cursor<'b>(&'b [u8]);
    impl Cursor<'_> {
        fn take(&mut self, n: usize) -> Option<&[u8]> {
            if self.0.len() < n {
                return None;
            }
            let (head, tail) = self.0.split_at(n);
            self.0 = tail;
            Some(head)
        }
        fn u8(&mut self) -> Option<u8> {
            self.take(1).map(|b| b[0])
        }
        fn u32(&mut self) -> Option<u32> {
            let b = self.take(4)?;
            Some(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
        }
        fn count(&mut self) -> Option<usize> {
            usize::try_from(self.u32()?).ok()
        }
        fn str(&mut self) -> Option<()> {
            let n = self.count()?;
            self.take(n).map(|_| ())
        }
        /// An operator descriptor; returns its arity.
        fn opdesc(&mut self) -> Option<usize> {
            let (payload, arity) = match self.u8()? {
                0x01 => (2, 2),
                0x02 => (2, 1),
                0x03 => (2, 2),
                0x04 => (3, 1),
                0x05 => (1, 3),
                _ => return None,
            };
            self.take(payload).map(|_| arity)
        }
    }
    let mut c = Cursor(bytes);
    if c.take(8)? != trust_cg_eqsat::derivation::MAGIC.as_slice()
        || c.u32()? != trust_cg_eqsat::derivation::VERSION
    {
        return None;
    }
    c.str()?;
    let rules = c.count()?;
    for _ in 0..rules {
        c.str()?;
        c.take(32)?;
    }
    let terms = c.count()?;
    for _ in 0..terms {
        let skip = match c.u8()? {
            0x01 => 8,
            0x02 => 12,
            0x03 => 17,
            0x04 => 4 * c.opdesc()?,
            _ => return None,
        };
        c.take(skip)?;
    }
    let proofs = c.count()?;
    for _ in 0..proofs {
        match c.u8()? {
            0x01 | 0x02 => c.take(4).map(|_| ())?,
            0x03 => c.take(8).map(|_| ())?,
            0x04 => {
                let arity = c.opdesc()?;
                c.take(4 * arity)?;
            }
            0x05 => {
                c.take(5)?;
                for _ in 0..c.count()? {
                    c.str()?;
                    c.take(4)?;
                }
                let conditions = c.count()?;
                c.take(4 * conditions)?;
            }
            _ => return None,
        }
    }
    let claims = c.count()?;
    c.take(4 * claims)?;
    if !c.0.is_empty() {
        return None;
    }
    let wide = |n: usize| u64::try_from(n).unwrap_or(u64::MAX);
    Some([wide(rules), wide(terms), wide(proofs), wide(claims)])
}

#[derive(Default)]
struct Family {
    modules: u64,
    functions: u64,
    declined: u64,
    declined_by_class: BTreeMap<String, u64>,
    rewritten: u64,
    unchanged: u64,
    cost_before: u64,
    cost_after: u64,
}

#[derive(Default)]
struct Totals {
    modules: u64,
    functions: u64,
    bodies: u64,
    declined: BTreeMap<String, u64>,
    unsupported: BTreeMap<String, u64>,
    analyzed: u64,
    rewritten: u64,
    unchanged: u64,
    rule_justified: u64,
    no_rule: u64,
    rule_matches: BTreeMap<String, u64>,
    budget_hits: u64,
    cost_before: u64,
    cost_after: u64,
    rewritten_cost_before: u64,
    rewritten_cost_after: u64,
    graph_instructions: u64,
    see_through_copies: u64,
    skeleton_instructions: u64,
    frontier_instructions: u64,
    ids: u64,
    nodes: u64,
    classes: u64,
    forms: BTreeMap<String, (u64, u64)>,
    derivation_bytes: u64,
    derivation_sections: [u64; 4],
    undecodable_derivations: u64,
    empty_rules_rewritten: u64,
    empty_rules_cost_before: u64,
    empty_rules_cost_after: u64,
    round_trip_declined: BTreeMap<String, u64>,
    round_trip_analyzed: u64,
    round_trip_cost_before: u64,
    round_trip_cost_after: u64,
    round_trip_cheaper: u64,
    round_trip_equal: u64,
    round_trip_costlier: u64,
    round_trip_unreadable: u64,
    invalid_rewritten_modules: u64,
    invalid_round_trip_modules: u64,
    nondeterministic: u64,
    families: BTreeMap<String, Family>,
}

/// Per-function mean wall time over the repetitions, with the function's name.
#[derive(Default)]
struct Timing {
    means: Vec<(Duration, String)>,
}

impl Timing {
    fn push(&mut self, samples: &[Duration], name: &str) {
        let total: Duration = samples.iter().sum();
        let count = u32::try_from(samples.len()).unwrap_or(u32::MAX).max(1);
        self.means.push((total / count, name.to_owned()));
    }
    fn summary(&self) -> (Duration, Duration, Duration, String) {
        let total: Duration = self.means.iter().map(|(d, _)| *d).sum();
        let count = u32::try_from(self.means.len()).unwrap_or(u32::MAX).max(1);
        let (max, name) = self
            .means
            .iter()
            .max_by_key(|(d, _)| *d)
            .cloned()
            .unwrap_or_default();
        (total, total / count, max, name)
    }
}

fn add(map: &mut BTreeMap<String, u64>, key: &str, n: u64) {
    *map.entry(key.to_owned()).or_insert(0) += n;
}

fn digits_as_n(text: &str) -> String {
    let mut out = String::new();
    let mut in_digits = false;
    for c in text.chars() {
        if c.is_ascii_digit() {
            if !in_digits {
                out.push('N');
            }
            in_digits = true;
        } else {
            out.push(c);
            in_digits = false;
        }
    }
    out
}

fn same(a: &Result<Optimized, Decline>, b: &Result<Optimized, Decline>) -> bool {
    match (a, b) {
        (Ok(a), Ok(b)) => {
            a.function == b.function
                && a.derivation == b.derivation
                && a.rewritten == b.rewritten
                && a.stats == b.stats
        }
        (Err(a), Err(b)) => a == b,
        _ => false,
    }
}

struct Measured {
    totals: Totals,
    optimize: Timing,
    round_trip: Timing,
    wall: Duration,
}

fn measure(corpus: &Path, files: &[String], reps: usize) -> Result<Measured, String> {
    let rules =
        RuleSet::parse(INTEGER_IDENTITIES).map_err(|e| format!("the shipped rules: {e:?}"))?;
    let empty = RuleSet::empty();
    let config = EngineConfig::default();
    let mut totals = Totals::default();
    let mut optimize_timing = Timing::default();
    let mut round_trip_timing = Timing::default();
    let started = Instant::now();
    for file in files {
        let path = corpus.join(file);
        let text =
            std::fs::read_to_string(&path).map_err(|e| format!("read {}: {e}", path.display()))?;
        let module = trust_ir::parser::parse_module(&text)
            .map_err(|e| format!("parse {}: {e}", path.display()))?;
        let family_name = Path::new(file)
            .file_name()
            .and_then(|n| n.to_str())
            .and_then(|n| n.split("__").next())
            .unwrap_or("?")
            .to_owned();
        totals.modules += 1;
        totals
            .families
            .entry(family_name.clone())
            .or_default()
            .modules += 1;
        let mut rewritten_module = module.clone();
        let mut round_trip_module = module.clone();
        let (mut any_rewritten, mut any_round_trip) = (false, false);
        for (index, function) in module.functions.iter().enumerate() {
            let name = format!("{file}:@{}", function.name);
            totals.functions += 1;
            if !function.is_declaration() {
                totals.bodies += 1;
            }
            let family = totals.families.entry(family_name.clone()).or_default();
            family.functions += 1;

            let mut samples = Vec::with_capacity(reps);
            let mut first: Option<Result<Optimized, Decline>> = None;
            let mut deterministic = true;
            for _ in 0..reps {
                let clock = Instant::now();
                let result = optimize_function(&module, function, &rules, &config);
                samples.push(clock.elapsed());
                match &first {
                    None => first = Some(result),
                    Some(earlier) => deterministic &= same(earlier, &result),
                }
            }
            optimize_timing.push(&samples, &name);

            let mut samples = Vec::with_capacity(reps);
            let mut first_round_trip: Option<Result<Function, Decline>> = None;
            for _ in 0..reps {
                let clock = Instant::now();
                let result = round_trip(&module, function);
                samples.push(clock.elapsed());
                match &first_round_trip {
                    None => first_round_trip = Some(result),
                    Some(earlier) => deterministic &= *earlier == result,
                }
            }
            round_trip_timing.push(&samples, &name);
            if !deterministic {
                totals.nondeterministic += 1;
            }

            let Some(result) = first else {
                return Err("no repetitions".to_owned());
            };
            match result {
                Err(decline) => {
                    add(&mut totals.declined, decline.class(), 1);
                    if let Decline::Unsupported(reason) = &decline {
                        add(&mut totals.unsupported, &digits_as_n(reason), 1);
                    }
                    family.declined += 1;
                    add(&mut family.declined_by_class, decline.class(), 1);
                }
                Ok(optimized) => {
                    let stats = &optimized.stats;
                    totals.analyzed += 1;
                    totals.cost_before += stats.cost_before;
                    totals.cost_after += stats.cost_after;
                    family.cost_before += stats.cost_before;
                    family.cost_after += stats.cost_after;
                    for (rule, n) in &stats.rule_matches {
                        add(&mut totals.rule_matches, rule, *n);
                    }
                    totals.budget_hits += stats.budget_hits;
                    let wide = |n: usize| u64::try_from(n).unwrap_or(u64::MAX);
                    totals.graph_instructions += wide(stats.graph_instructions);
                    totals.see_through_copies += wide(stats.see_through_copies);
                    totals.skeleton_instructions += wide(stats.skeleton_instructions);
                    totals.frontier_instructions += wide(stats.frontier_instructions);
                    totals.ids += wide(stats.ids);
                    totals.nodes += wide(stats.nodes);
                    totals.classes += wide(stats.classes);
                    for (class, (classes, nodes)) in &stats.forms_by_class {
                        let slot = totals.forms.entry(class.clone()).or_insert((0, 0));
                        slot.0 += classes;
                        slot.1 += nodes;
                    }
                    if optimized.rewritten {
                        totals.rewritten += 1;
                        family.rewritten += 1;
                        totals.rewritten_cost_before += stats.cost_before;
                        totals.rewritten_cost_after += stats.cost_after;
                        totals.derivation_bytes += wide(optimized.derivation.len());
                        match derivation_shape(&optimized.derivation) {
                            Some(sections) => {
                                for (sum, n) in totals.derivation_sections.iter_mut().zip(sections)
                                {
                                    *sum += n;
                                }
                                if sections[0] > 0 {
                                    totals.rule_justified += 1;
                                } else {
                                    totals.no_rule += 1;
                                }
                            }
                            None => totals.undecodable_derivations += 1,
                        }
                        if let Some(slot) = rewritten_module.functions.get_mut(index) {
                            *slot = optimized.function;
                            any_rewritten = true;
                        }
                    } else {
                        totals.unchanged += 1;
                        family.unchanged += 1;
                    }
                }
            }

            let no_rules = optimize_function(&module, function, &empty, &config);
            if let Ok(no_rules) = &no_rules {
                totals.empty_rules_cost_before += no_rules.stats.cost_before;
                totals.empty_rules_cost_after += no_rules.stats.cost_after;
                if no_rules.rewritten {
                    totals.empty_rules_rewritten += 1;
                }
            }

            let Some(round_trip_result) = first_round_trip else {
                return Err("no repetitions".to_owned());
            };
            match round_trip_result {
                Err(decline) => add(&mut totals.round_trip_declined, decline.class(), 1),
                Ok(body) => {
                    totals.round_trip_analyzed += 1;
                    // The round-trip body's static cost, as the engine's own
                    // reader counts it on re-reading that body.
                    let reread = optimize_function(&module, &body, &empty, &config);
                    match (&no_rules, reread) {
                        (Ok(input), Ok(reread)) => {
                            let (before, after) =
                                (input.stats.cost_before, reread.stats.cost_before);
                            totals.round_trip_cost_before += before;
                            totals.round_trip_cost_after += after;
                            match after.cmp(&before) {
                                std::cmp::Ordering::Less => totals.round_trip_cheaper += 1,
                                std::cmp::Ordering::Equal => totals.round_trip_equal += 1,
                                std::cmp::Ordering::Greater => totals.round_trip_costlier += 1,
                            }
                        }
                        _ => totals.round_trip_unreadable += 1,
                    }
                    if let Some(slot) = round_trip_module.functions.get_mut(index) {
                        *slot = body;
                        any_round_trip = true;
                    }
                }
            }
        }
        if any_rewritten && !trust_ir_build::validate_module(&rewritten_module).is_empty() {
            totals.invalid_rewritten_modules += 1;
        }
        if any_round_trip && !trust_ir_build::validate_module(&round_trip_module).is_empty() {
            totals.invalid_round_trip_modules += 1;
        }
    }
    Ok(Measured {
        totals,
        optimize: optimize_timing,
        round_trip: round_trip_timing,
        wall: started.elapsed(),
    })
}

fn signed_delta(before: u64, after: u64) -> String {
    if after >= before {
        format!("+{}", after - before)
    } else {
        format!("-{}", before - after)
    }
}

fn percent(part: u64, whole: u64) -> String {
    if whole == 0 {
        return "n/a".to_owned();
    }
    // Integer arithmetic keeps the text identical on every host.
    let basis_points = (u128::from(part) * 10_000 + u128::from(whole) / 2) / u128::from(whole);
    format!("{}.{:02}%", basis_points / 100, basis_points % 100)
}

fn ratio(numerator: u64, denominator: u64) -> String {
    if denominator == 0 {
        return "n/a".to_owned();
    }
    let hundredths =
        (u128::from(numerator) * 100 + u128::from(denominator) / 2) / u128::from(denominator);
    format!("{}.{:02}", hundredths / 100, hundredths % 100)
}

fn micros(d: Duration) -> u128 {
    d.as_micros()
}

fn text_report(corpus_label: &str, reps: usize, rule_count: usize, m: &Measured) -> String {
    let t = &m.totals;
    let config = EngineConfig::default();
    let mut out = String::new();
    let mut line = |s: String| {
        out.push_str(&s);
        out.push('\n');
    };
    line(format!("eqsat_stats: corpus {corpus_label}/MANIFEST.tsv"));
    line(format!(
        "rules: integer_identities ({rule_count} rules); EngineConfig::default(): \
         max_rewrite_depth {}, max_matches_per_node {}, max_ids_per_instruction {}; \
         repetitions {reps}",
        config.max_rewrite_depth, config.max_matches_per_node, config.max_ids_per_instruction
    ));
    line(String::new());
    line(format!(
        "modules                                  {}",
        t.modules
    ));
    line(format!(
        "functions                                {}",
        t.functions
    ));
    line(format!(
        "functions with a body                    {}",
        t.bodies
    ));
    line(String::new());
    line("optimize_function (integer identities)".to_owned());
    line(format!(
        "  declined                               {}",
        t.declined.values().sum::<u64>()
    ));
    for (class, n) in &t.declined {
        line(format!("    {class:<36} {n}"));
    }
    line(format!(
        "  analyzed (not declined)                {}",
        t.analyzed
    ));
    line(format!(
        "    rewritten                            {}",
        t.rewritten
    ));
    line(format!(
        "      rule-justified (derivation names a rule)   {}",
        t.rule_justified
    ));
    line(format!(
        "      no rule needed (copy removal, hash-consing) {}",
        t.no_rule
    ));
    if t.undecodable_derivations > 0 {
        line(format!(
            "      derivation not in the version 1 layout   {}",
            t.undecodable_derivations
        ));
    }
    line(format!(
        "    unchanged                            {}",
        t.unchanged
    ));
    line(format!(
        "  static cost, analyzed functions        before {} after {} delta {} ({})",
        t.cost_before,
        t.cost_after,
        signed_delta(t.cost_before, t.cost_after),
        percent(
            t.cost_before - t.cost_after.min(t.cost_before),
            t.cost_before
        )
    ));
    line(format!(
        "  static cost, rewritten functions       before {} after {} delta {}",
        t.rewritten_cost_before,
        t.rewritten_cost_after,
        signed_delta(t.rewritten_cost_before, t.rewritten_cost_after)
    ));
    let [rules, terms, proofs, claims] = t.derivation_sections;
    line(format!(
        "  derivations of rewritten functions     bytes {} rule entries {rules} terms {terms} \
         proofs {proofs} claims {claims}",
        t.derivation_bytes
    ));
    line("  rule matches (unions and directed edges recorded, all analyzed functions)".to_owned());
    if t.rule_matches.is_empty() {
        line("    (none)".to_owned());
    }
    for (rule, n) in &t.rule_matches {
        line(format!("    {rule:<36} {n}"));
    }
    line(format!(
        "  budget hits                            {}",
        t.budget_hits
    ));
    line(format!(
        "  reader classes (analyzed functions)    graph {} see-through copies {} skeleton {} \
         of which frontier {}",
        t.graph_instructions,
        t.see_through_copies,
        t.skeleton_instructions,
        t.frontier_instructions
    ));
    line(format!(
        "  graph size                             ids {} nodes {} classes {}",
        t.ids, t.nodes, t.classes
    ));
    let (all_classes, all_nodes) = t
        .forms
        .values()
        .fold((0, 0), |(c, n), (dc, dn)| (c + dc, n + dn));
    line(format!(
        "  forms per class (nodes/classes)        overall {} ({all_nodes}/{all_classes})",
        ratio(all_nodes, all_classes)
    ));
    for (class, (classes, nodes)) in &t.forms {
        line(format!(
            "    {class:<36} {} ({nodes}/{classes})",
            ratio(*nodes, *classes)
        ));
    }
    if !t.unsupported.is_empty() {
        line("  unsupported declines by reason (digit runs as N)".to_owned());
        for (reason, n) in &t.unsupported {
            line(format!("    {n:>6}  {reason}"));
        }
    }
    line(String::new());
    line("optimize_function with no rules (RuleSet::empty())".to_owned());
    line(format!(
        "  rewritten                              {}",
        t.empty_rules_rewritten
    ));
    line(format!(
        "  static cost, analyzed functions        before {} after {} delta {}",
        t.empty_rules_cost_before,
        t.empty_rules_cost_after,
        signed_delta(t.empty_rules_cost_before, t.empty_rules_cost_after)
    ));
    line(String::new());
    line("round_trip (no rules, always elaborated)".to_owned());
    line(format!(
        "  declined                               {}{}",
        t.round_trip_declined.values().sum::<u64>(),
        if t.round_trip_declined == t.declined {
            " (the same classes as optimize_function)"
        } else {
            " (DIFFERENT from optimize_function)"
        }
    ));
    for (class, n) in &t.round_trip_declined {
        line(format!("    {class:<36} {n}"));
    }
    line(format!(
        "  analyzed                               {}",
        t.round_trip_analyzed
    ));
    line(format!(
        "  static cost of the round-trip body     before {} after {} delta {}",
        t.round_trip_cost_before,
        t.round_trip_cost_after,
        signed_delta(t.round_trip_cost_before, t.round_trip_cost_after)
    ));
    line(format!(
        "  functions cheaper / equal / costlier   {} / {} / {}",
        t.round_trip_cheaper, t.round_trip_equal, t.round_trip_costlier
    ));
    line(format!(
        "  round-trip bodies the reader refuses   {}",
        t.round_trip_unreadable
    ));
    line(String::new());
    line("checks".to_owned());
    line(format!(
        "  modules failing validate_module with the rewritten bodies   {}",
        t.invalid_rewritten_modules
    ));
    line(format!(
        "  modules failing validate_module with the round-trip bodies  {}",
        t.invalid_round_trip_modules
    ));
    line(format!(
        "  functions whose repeated runs differ                        {}",
        t.nondeterministic
    ));
    line(String::new());
    line(
        "by family (module file prefix): modules functions declined rewritten unchanged \
         cost_before cost_after"
            .to_owned(),
    );
    for (name, f) in &t.families {
        line(format!(
            "  {name:<18} {:>5} {:>6} {:>6} {:>5} {:>6} {:>8} {:>8}",
            f.modules,
            f.functions,
            f.declined,
            f.rewritten,
            f.unchanged,
            f.cost_before,
            f.cost_after
        ));
    }
    line("declines by family and class".to_owned());
    for (name, f) in &t.families {
        if f.declined_by_class.is_empty() {
            continue;
        }
        let classes: Vec<String> = f
            .declined_by_class
            .iter()
            .map(|(class, n)| format!("{class} {n}"))
            .collect();
        line(format!("  {name:<18} {}", classes.join(", ")));
    }
    line(String::new());
    for (label, timing) in [
        ("optimize_function", &m.optimize),
        ("round_trip", &m.round_trip),
    ] {
        let (total, mean, max, name) = timing.summary();
        line(format!(
            "[host-dependent] {label:<17} per-function mean over {reps} repetitions: total {} us, \
             mean {} us, max {} us ({name})",
            micros(total),
            micros(mean),
            micros(max)
        ));
    }
    line(format!(
        "[host-dependent] whole measurement      {} ms",
        m.wall.as_millis()
    ));
    out
}

fn json_string(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if u32::from(c) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", u32::from(c));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn json_map(map: &BTreeMap<String, u64>) -> String {
    let fields: Vec<String> = map
        .iter()
        .map(|(k, v)| format!("{}:{v}", json_string(k)))
        .collect();
    format!("{{{}}}", fields.join(","))
}

fn json_report(reps: usize, rule_count: usize, m: &Measured) -> String {
    let t = &m.totals;
    let config = EngineConfig::default();
    let forms: Vec<String> = t
        .forms
        .iter()
        .map(|(k, (c, n))| format!("{}:{{\"classes\":{c},\"nodes\":{n}}}", json_string(k)))
        .collect();
    let families: Vec<String> = t
        .families
        .iter()
        .map(|(k, f)| {
            format!(
                "{}:{{\"modules\":{},\"functions\":{},\"declined\":{},\"declined_by_class\":{},\
                 \"rewritten\":{},\"unchanged\":{},\"cost_before\":{},\"cost_after\":{}}}",
                json_string(k),
                f.modules,
                f.functions,
                f.declined,
                json_map(&f.declined_by_class),
                f.rewritten,
                f.unchanged,
                f.cost_before,
                f.cost_after
            )
        })
        .collect();
    let timing = |timing: &Timing| {
        let (total, mean, max, name) = timing.summary();
        format!(
            "{{\"total_us\":{},\"mean_us\":{},\"max_us\":{},\"max_function\":{}}}",
            micros(total),
            micros(mean),
            micros(max),
            json_string(&name)
        )
    };
    let [rules, terms, proofs, claims] = t.derivation_sections;
    let mut out = String::from("{");
    let mut field = |name: &str, value: String| {
        if out.len() > 1 {
            out.push(',');
        }
        let _ = write!(out, "{}:{value}", json_string(name));
    };
    field("rule_count", rule_count.to_string());
    field("max_rewrite_depth", config.max_rewrite_depth.to_string());
    field(
        "max_matches_per_node",
        config.max_matches_per_node.to_string(),
    );
    field(
        "max_ids_per_instruction",
        config.max_ids_per_instruction.to_string(),
    );
    field("repetitions", reps.to_string());
    field("modules", t.modules.to_string());
    field("functions", t.functions.to_string());
    field("functions_with_body", t.bodies.to_string());
    field("declined", json_map(&t.declined));
    field("unsupported_reasons", json_map(&t.unsupported));
    field("analyzed", t.analyzed.to_string());
    field("rewritten", t.rewritten.to_string());
    field("rule_justified", t.rule_justified.to_string());
    field("no_rule_needed", t.no_rule.to_string());
    field(
        "undecodable_derivations",
        t.undecodable_derivations.to_string(),
    );
    field("unchanged", t.unchanged.to_string());
    field("cost_before", t.cost_before.to_string());
    field("cost_after", t.cost_after.to_string());
    field("rewritten_cost_before", t.rewritten_cost_before.to_string());
    field("rewritten_cost_after", t.rewritten_cost_after.to_string());
    field(
        "derivations",
        format!(
            "{{\"bytes\":{},\"rules\":{rules},\"terms\":{terms},\"proofs\":{proofs},\"claims\":{claims}}}",
            t.derivation_bytes
        ),
    );
    field("rule_matches", json_map(&t.rule_matches));
    field("budget_hits", t.budget_hits.to_string());
    field(
        "reader",
        format!(
            "{{\"graph\":{},\"see_through_copies\":{},\"skeleton\":{},\"frontier\":{},\"ids\":{},\
             \"nodes\":{},\"classes\":{}}}",
            t.graph_instructions,
            t.see_through_copies,
            t.skeleton_instructions,
            t.frontier_instructions,
            t.ids,
            t.nodes,
            t.classes
        ),
    );
    field("forms_by_class", format!("{{{}}}", forms.join(",")));
    field(
        "no_rules",
        format!(
            "{{\"rewritten\":{},\"cost_before\":{},\"cost_after\":{}}}",
            t.empty_rules_rewritten, t.empty_rules_cost_before, t.empty_rules_cost_after
        ),
    );
    field(
        "round_trip",
        format!(
            "{{\"declined\":{},\"analyzed\":{},\"cost_before\":{},\"cost_after\":{},\"cheaper\":{},\
             \"equal\":{},\"costlier\":{},\"unreadable\":{}}}",
            json_map(&t.round_trip_declined),
            t.round_trip_analyzed,
            t.round_trip_cost_before,
            t.round_trip_cost_after,
            t.round_trip_cheaper,
            t.round_trip_equal,
            t.round_trip_costlier,
            t.round_trip_unreadable
        ),
    );
    field(
        "checks",
        format!(
            "{{\"invalid_rewritten_modules\":{},\"invalid_round_trip_modules\":{},\
             \"nondeterministic_functions\":{}}}",
            t.invalid_rewritten_modules, t.invalid_round_trip_modules, t.nondeterministic
        ),
    );
    field("families", format!("{{{}}}", families.join(",")));
    field(
        "host_dependent",
        format!(
            "{{\"optimize_function\":{},\"round_trip\":{},\"wall_ms\":{}}}",
            timing(&m.optimize),
            timing(&m.round_trip),
            m.wall.as_millis()
        ),
    );
    out.push('}');
    out
}

fn run() -> Result<(), String> {
    let args = arguments()?;
    let files = taken_files(&args.corpus)?;
    let rule_count = RuleSet::parse(INTEGER_IDENTITIES)
        .map_err(|e| format!("the shipped rules: {e:?}"))?
        .rules()
        .len();
    let measured = measure(&args.corpus, &files, args.reps)?;
    if args.json {
        println!("{}", json_report(args.reps, rule_count, &measured));
    } else {
        print!(
            "{}",
            text_report(&args.corpus_label, args.reps, rule_count, &measured)
        );
    }
    Ok(())
}
