// crates/trust-cg-eqsat/src/saturate.rs - Tier S: budgeted equality saturation of bounded regions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Tier S (`docs/eqsat-tier-s.md`, PKG-U4): equality saturation of a bounded
//! [`Region`] of total operators, with a derivation for every result.
//!
//! # What this module is, and is not
//!
//! * **Discovery only, untrusted.** [`saturate`] loads a region into an
//!   e-graph with congruence closure, e-matches the rules of each
//!   [`Stage`] and applies them until nothing changes or a budget is spent.
//!   [`Saturation::extract`] then picks a form of every root and writes a
//!   version-2 derivation; [`Saturation::justify`] writes one for a form
//!   the caller names. A fault here loses a form or yields a derivation
//!   `trust_cg_eqsat_check::check_region` refuses.
//! * **Rules grant no proof authority.** A Tier S rule is the same
//!   [`crate::rules::Rule`] object Tier E fires: a statement with a name and
//!   a statement digest, stated and not proved. Nothing a rule justifies
//!   here is established until PKG-U2's registry holds a discharge record
//!   for that digest and refuses a rule without one. That one type is where
//!   PKG-U2 attaches what it needs; this module reads a rule only through
//!   its sides, domain, side conditions, name and digest.
//! * **Every budget counts.** A stage stops after a number of matches, the
//!   graph stops growing at a number of terms, the extractor stops after a
//!   number of trial evaluations. No clock is read, so equal inputs give
//!   byte-identical regions and derivations.
//! * **Never costlier.** The input region is always a candidate: when the
//!   chosen form is not strictly cheaper by the static cost of section 5,
//!   which prices a shared node once, the input is returned unchanged.
//! * **No recursion on region depth.** Loading, congruence closure,
//!   explanation, extraction and the encoders keep their own stacks, so a
//!   deep region is a matter of memory and of the count budgets, never of
//!   the thread's stack.
//! * **Order-free nodes.** An order-free node is a leaf with an operand and
//!   a family of orders. Its implementations are one-way edges to pinned
//!   reductions, never merges: no class ever holds both an order-free
//!   result and a reduction that implements it, and extraction elaborates a
//!   node to at most one implementation.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

mod egraph;
mod extract;
mod matching;
pub mod region;

use crate::derivation::{self, ProofRef};
use crate::proof::{EngineError, EngineResult, invariant};
use crate::rules::{Rule, RuleSet};
use crate::vocab::{GraphWidths, OpDesc};

use egraph::{Graph, TNode, Tid};
use matching::Snapshot;
pub use region::{LeafName, NodeId, OrderFree, Region, RegionError, RegionNode};

/// One step of a [`Schedule`]: the rules it fires, by name, and how many
/// matches it may examine.
///
/// The rules are [`crate::rules::Rule`] objects of the rule set given to
/// [`saturate`]; they grant no proof authority until PKG-U2's registry
/// discharges them (module docs).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stage {
    /// The names of the rules this stage fires. They fire in the rule
    /// set's file order, whatever the order here.
    pub rules: Vec<String>,
    /// The complete matches this stage examines before it stops. Every
    /// match a round finds is counted, also one an earlier round already
    /// applied and one that changes nothing (section 4.2).
    pub max_matches: u64,
}

/// A declared schedule (section 4.3): the stages run once each, in order,
/// each to its fixpoint or its match budget.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Schedule {
    /// The stages, in the order they run.
    pub stages: Vec<Stage>,
    /// No rule is applied once the graph holds this many concrete terms
    /// (several terms can be one e-node; [`SaturationStats`] reports both).
    pub max_terms: usize,
    /// The trials the extractor's two searches may spend together (section
    /// 5): a re-priced single-class change, or an option tried by the
    /// branch-and-bound search.
    pub max_extraction_trials: u64,
}

impl Schedule {
    /// The default bound on extraction trials.
    pub const DEFAULT_EXTRACTION_TRIALS: u64 = 4096;

    /// One stage that fires every `equiv` rule of `rules`. A `refines` rule
    /// of the set is left out: Tier S merges classes, so it cannot fire one
    /// (section 4.2), and a stage that names one is refused.
    #[must_use]
    pub fn single(rules: &RuleSet, max_matches: u64, max_terms: usize) -> Self {
        Self {
            stages: vec![Stage {
                rules: rules
                    .rules()
                    .iter()
                    .filter(|rule| rule.is_equiv())
                    .map(|rule| rule.name().to_owned())
                    .collect(),
                max_matches,
            }],
            max_terms,
            max_extraction_trials: Self::DEFAULT_EXTRACTION_TRIALS,
        }
    }
}

/// Why a stage stopped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stop {
    /// A whole round found no match that changed the graph.
    Fixpoint,
    /// The stage's match budget was spent.
    MatchBudget,
    /// The graph reached `max_terms`.
    TermBudget,
}

/// What one stage did.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StageStats {
    /// Rounds of matching.
    pub rounds: u64,
    /// Complete matches examined.
    pub matches: u64,
    /// Matches that merged two classes.
    pub applied: u64,
    /// Why the stage stopped.
    pub stop: Stop,
}

/// What a saturation saw and did.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SaturationStats {
    /// One entry per stage of the schedule.
    pub stages: Vec<StageStats>,
    /// Concrete terms in the graph.
    pub terms: usize,
    /// Classes.
    pub classes: usize,
    /// E-nodes (leaves and constants included).
    pub enodes: usize,
    /// Matches that merged two classes, by rule name.
    pub rule_applications: BTreeMap<String, u64>,
}

impl SaturationStats {
    /// Whether every stage reached its fixpoint.
    #[must_use]
    pub fn saturated(&self) -> bool {
        self.stages.iter().all(|stage| stage.stop == Stop::Fixpoint)
    }
}

/// Why [`saturate`] or a [`Saturation`] call fails.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SaturateError {
    /// A stage names a rule the rule set does not hold.
    UnknownRule(String),
    /// A stage names a `refines` rule. Tier S merges classes only, so it
    /// fires `equiv` rules only (section 4.2).
    RefinesRule(String),
    /// The target of [`Saturation::justify`] is not the input region with
    /// other roots.
    TargetMismatch(String),
    /// An engine invariant did not hold; nothing is returned from a graph
    /// the engine cannot explain.
    Engine(String),
}

impl fmt::Display for SaturateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SaturateError::UnknownRule(name) => write!(f, "a stage names unknown rule `{name}`"),
            SaturateError::RefinesRule(name) => {
                write!(f, "a stage names `{name}`, a refines rule")
            }
            SaturateError::TargetMismatch(detail) => write!(f, "target region: {detail}"),
            SaturateError::Engine(detail) => f.write_str(detail),
        }
    }
}

impl std::error::Error for SaturateError {}

impl From<EngineError> for SaturateError {
    fn from(error: EngineError) -> Self {
        SaturateError::Engine(error.to_string())
    }
}

impl From<RegionError> for SaturateError {
    fn from(error: RegionError) -> Self {
        SaturateError::Engine(error.to_string())
    }
}

/// An order-free node as the graph holds it.
#[derive(Debug, Clone)]
pub(crate) struct FreeNode {
    pub(crate) leaf: Tid,
    pub(crate) operand: Tid,
    /// Each order of the family with the term of the reduction pinned at
    /// that order over the operand.
    pub(crate) pinned: Vec<(u32, Tid)>,
}

/// The result of [`Saturation::extract`].
#[derive(Debug, Clone)]
pub struct Extracted {
    /// The returned region (the input when `rewritten` is false).
    pub region: Region,
    /// The version-2 derivation (header-only when nothing changed).
    pub derivation: Vec<u8>,
    /// Whether the region changed.
    pub rewritten: bool,
    /// Static cost of the input region.
    pub cost_before: u64,
    /// Static cost of the returned region.
    pub cost_after: u64,
    /// Static cost of the form the per-class tree-cost choice gives, priced
    /// like every other form (a shared node once). It can exceed
    /// `cost_before`; the returned region never does.
    pub tree_choice_cost: u64,
    /// Trials the extractor's searches spent.
    pub trials: u64,
    /// Whether the extractor's branch-and-bound search ended before the
    /// trial budget did. When it did, no acyclic choice of one option per
    /// class is cheaper than the form the search chose; the returned region
    /// is that form, or the input when the form is not strictly cheaper or
    /// cannot be written as a region.
    pub search_complete: bool,
    /// The order-free nodes the returned region implements by a pinned
    /// reduction, each with the order chosen, in the input's table order.
    /// Empty when the region is the input.
    pub implemented: Vec<(LeafName, u32)>,
}

/// A saturated (or budget-stopped) graph of one region.
pub struct Saturation {
    input: Region,
    graph: Graph,
    free: Vec<FreeNode>,
    roots: Vec<Tid>,
    stats: SaturationStats,
    max_extraction_trials: u64,
}

fn resolve<'r>(rules: &'r RuleSet, stage: &Stage) -> Result<Vec<&'r Rule>, SaturateError> {
    let wanted: BTreeSet<&str> = stage.rules.iter().map(String::as_str).collect();
    for name in &wanted {
        match rules.rules().iter().find(|rule| rule.name() == *name) {
            None => return Err(SaturateError::UnknownRule((*name).to_owned())),
            Some(rule) if !rule.is_equiv() => {
                return Err(SaturateError::RefinesRule((*name).to_owned()));
            }
            Some(_) => {}
        }
    }
    Ok(rules
        .rules()
        .iter()
        .filter(|rule| wanted.contains(rule.name()))
        .collect())
}

/// Load `region` into an e-graph and run `schedule` over it (section 4).
///
/// # Errors
/// A stage that names an unknown or a `refines` rule, or an engine
/// invariant that did not hold.
pub fn saturate(
    region: &Region,
    rules: &RuleSet,
    schedule: &Schedule,
) -> Result<Saturation, SaturateError> {
    let mut staged = Vec::with_capacity(schedule.stages.len());
    for stage in &schedule.stages {
        staged.push((resolve(rules, stage)?, stage.max_matches));
    }
    let widths = region.widths();
    let mut graph = Graph::new(region.name());
    let (free, roots) = load(region, &mut graph)?;
    graph.rebuild()?;

    let mut rule_applications: BTreeMap<String, u64> = BTreeMap::new();
    let mut stages = Vec::with_capacity(staged.len());
    for (stage_rules, max_matches) in &staged {
        stages.push(run_stage(
            &mut graph,
            widths,
            stage_rules,
            *max_matches,
            schedule.max_terms,
            &mut rule_applications,
        )?);
    }
    let classes = graph.classes()?;
    let stats = SaturationStats {
        stages,
        terms: graph.len(),
        classes: classes.len(),
        enodes: classes.iter().map(|class| class.enodes.len()).sum(),
        rule_applications,
    };
    Ok(Saturation {
        input: region.clone(),
        graph,
        free,
        roots,
        stats,
        max_extraction_trials: schedule.max_extraction_trials,
    })
}

fn load(region: &Region, graph: &mut Graph) -> EngineResult<(Vec<FreeNode>, Vec<Tid>)> {
    for (leaf, ty) in region.leaves() {
        graph.declare_leaf(leaf, ty)?;
    }
    // Node ids are in creation order, so children come first.
    let mut terms: BTreeMap<NodeId, Tid> = BTreeMap::new();
    for id in region.reachable() {
        let term = match region.node(id) {
            Some(RegionNode::Leaf(leaf)) => match graph.lookup(&TNode::Leaf(*leaf)) {
                Some(term) => term,
                None => return invariant("a region leaf that was not declared"),
            },
            Some(RegionNode::Const(ty, residue)) => graph.add(TNode::Const(*ty, *residue))?,
            Some(RegionNode::Op(desc, args)) => {
                let mut mapped = Vec::with_capacity(args.len());
                for arg in args {
                    match terms.get(arg) {
                        Some(term) => mapped.push(*term),
                        None => return invariant("a region node used before it is defined"),
                    }
                }
                graph.add(TNode::Op(*desc, mapped))?
            }
            None => return invariant("a region node that does not exist"),
        };
        terms.insert(id, term);
    }
    let term_of = |id: &NodeId| match terms.get(id) {
        Some(term) => Ok(*term),
        None => invariant("a region node that was not loaded"),
    };
    let mut free = Vec::with_capacity(region.order_free().len());
    for entry in region.order_free() {
        let (leaf, operand) = (term_of(&entry.leaf)?, term_of(&entry.operand)?);
        let ty = graph.ty(leaf)?;
        let mut pinned = Vec::with_capacity(entry.orders.len());
        for order in &entry.orders {
            pinned.push((
                *order,
                graph.add(TNode::Op(OpDesc::Pinned(*order, ty), vec![operand]))?,
            ));
        }
        free.push(FreeNode {
            leaf,
            operand,
            pinned,
        });
    }
    let mut roots = Vec::with_capacity(region.roots().len());
    for root in region.roots() {
        roots.push(term_of(root)?);
    }
    Ok((free, roots))
}

fn run_stage(
    graph: &mut Graph,
    widths: GraphWidths,
    rules: &[&Rule],
    max_matches: u64,
    max_terms: usize,
    rule_applications: &mut BTreeMap<String, u64>,
) -> EngineResult<StageStats> {
    let mut stats = StageStats {
        rounds: 0,
        matches: 0,
        applied: 0,
        stop: Stop::Fixpoint,
    };
    loop {
        let remaining = max_matches.saturating_sub(stats.matches);
        // One more than the budget allows, so a round that would exceed it
        // is told apart from one that exactly spends it.
        let cap = usize::try_from(remaining)
            .unwrap_or(usize::MAX)
            .saturating_add(1);
        let snapshot = Snapshot::take(graph)?;
        let found = snapshot.matches(rules, widths, cap)?;
        drop(snapshot);
        stats.rounds += 1;
        let mut changed = false;
        let mut stopped = None;
        for one in &found {
            if stats.matches >= max_matches {
                stopped = Some(Stop::MatchBudget);
                break;
            }
            if graph.len() >= max_terms {
                stopped = Some(Stop::TermBudget);
                break;
            }
            stats.matches += 1;
            let Some(rule) = rules.get(one.rule) else {
                return invariant("a match of a rule outside the stage");
            };
            if matching::apply(graph, widths, rule, one)? {
                changed = true;
                stats.applied += 1;
                *rule_applications.entry(rule.name().to_owned()).or_insert(0) += 1;
            }
        }
        graph.rebuild()?;
        if let Some(stop) = stopped {
            stats.stop = stop;
            return Ok(stats);
        }
        if !changed {
            return Ok(stats);
        }
    }
}

impl Saturation {
    /// What the saturation saw and did.
    #[must_use]
    pub fn stats(&self) -> &SaturationStats {
        &self.stats
    }

    /// The region that was saturated.
    #[must_use]
    pub fn input(&self) -> &Region {
        &self.input
    }

    /// The number of distinct terms the class of root `root` represents, or
    /// `None` when there is no such root, the class represents infinitely
    /// many terms (it reaches itself) or the count does not fit.
    pub fn forms(&mut self, root: usize) -> Option<u128> {
        let term = *self.roots.get(root)?;
        let class = self.graph.find(term);
        let table = extract::Table::build(&mut self.graph, &self.free).ok()?;
        table.forms(class)
    }

    fn derivation(&self, claims: &[ProofRef]) -> Vec<u8> {
        let mut builder = self.graph.prover.builder().clone();
        for claim in claims {
            builder.claim(*claim);
        }
        builder.finish()
    }

    /// Choose a form of every root (section 5) and write its derivation.
    /// The result is never costlier than the input: when the chosen form is
    /// not strictly cheaper, or it cannot be written as a well-formed
    /// region, the input is returned unchanged with the header-only
    /// derivation.
    ///
    /// # Errors
    /// An engine invariant that did not hold.
    pub fn extract(&mut self) -> Result<Extracted, SaturateError> {
        let cost_before = self.input.cost();
        let unchanged =
            |tree_choice_cost: u64, trials: u64, search_complete: bool, input: &Region| Extracted {
                region: input.clone(),
                derivation: derivation::region_header_only(input.name()),
                rewritten: false,
                cost_before,
                cost_after: cost_before,
                tree_choice_cost,
                trials,
                search_complete,
                implemented: Vec::new(),
            };
        let table = extract::Table::build(&mut self.graph, &self.free)?;
        let mut root_classes = Vec::with_capacity(self.roots.len());
        for root in &self.roots {
            root_classes.push(self.graph.find(*root));
        }
        let Some(chosen) = table.choose(&root_classes, self.max_extraction_trials) else {
            return Ok(unchanged(cost_before, 0, false, &self.input));
        };
        let emitted = extract::emit(
            &mut self.graph,
            &self.input,
            &self.free,
            &self.roots,
            &table,
            &chosen.choice,
        )?;
        let Some(emitted) = emitted else {
            return Ok(unchanged(
                chosen.tree_choice_cost,
                chosen.trials,
                chosen.search_complete,
                &self.input,
            ));
        };
        let cost_after = emitted.region.cost();
        if cost_after >= cost_before {
            return Ok(unchanged(
                chosen.tree_choice_cost,
                chosen.trials,
                chosen.search_complete,
                &self.input,
            ));
        }
        let mut implemented = Vec::with_capacity(emitted.implemented.len());
        for (entry, order) in &emitted.implemented {
            let leaf = self
                .input
                .order_free()
                .get(*entry)
                .and_then(|node| self.input.node(node.leaf));
            let Some(RegionNode::Leaf(name)) = leaf else {
                return Err(SaturateError::Engine(
                    "an implemented order-free node the input does not have".to_owned(),
                ));
            };
            implemented.push((*name, *order));
        }
        Ok(Extracted {
            derivation: self.derivation(&emitted.claims),
            region: emitted.region,
            rewritten: true,
            cost_before,
            cost_after,
            tree_choice_cost: chosen.tree_choice_cost,
            trials: chosen.trials,
            search_complete: chosen.search_complete,
            implemented,
        })
    }

    /// The term of every node of `target` the graph represents (no class is
    /// made). Node ids are in creation order, so one pass over the nodes
    /// the target reaches sees every operand before its operator.
    fn represent(&mut self, target: &Region) -> EngineResult<BTreeMap<NodeId, Tid>> {
        let mut terms: BTreeMap<NodeId, Tid> = BTreeMap::new();
        for id in target.reachable() {
            let term = match target.node(id) {
                Some(RegionNode::Leaf(leaf)) => self.graph.lookup(&TNode::Leaf(*leaf)),
                Some(RegionNode::Const(ty, residue)) => {
                    self.graph.lookup(&TNode::Const(*ty, *residue))
                }
                Some(RegionNode::Op(desc, args)) => {
                    let mapped: Option<Vec<Tid>> =
                        args.iter().map(|arg| terms.get(arg).copied()).collect();
                    match mapped {
                        Some(mapped) if self.graph.lookup_enode(*desc, &mapped).is_some() => {
                            Some(self.graph.add(TNode::Op(*desc, mapped))?)
                        }
                        _ => None,
                    }
                }
                None => return invariant("a target node that does not exist"),
            };
            if let Some(term) = term {
                terms.insert(id, term);
            }
        }
        Ok(terms)
    }

    /// The derivation that takes the input region to `target`, which must
    /// be the input with other roots (same name, pointer width, leaves,
    /// order-free nodes and number of roots). `None` when some root of
    /// `target` is not a form the graph holds in the class of the matching
    /// input root (a missing form).
    ///
    /// # Errors
    /// A `target` that is not the input with other roots, or an engine
    /// invariant that did not hold.
    pub fn justify(&mut self, target: &Region) -> Result<Option<Vec<u8>>, SaturateError> {
        let mismatch = |what: &str| Err(SaturateError::TargetMismatch(what.to_owned()));
        if target.name() != self.input.name() || target.pointer_bits() != self.input.pointer_bits()
        {
            return mismatch("another name or pointer width");
        }
        if target.leaves().collect::<Vec<_>>() != self.input.leaves().collect::<Vec<_>>() {
            return mismatch("other leaves");
        }
        if target.roots().len() != self.roots.len() {
            return mismatch("another number of roots");
        }
        if target.order_free().len() != self.free.len() {
            return mismatch("other order-free nodes");
        }
        let terms = self.represent(target)?;
        for (entry, ours) in target.order_free().iter().zip(&self.free) {
            let orders: Vec<u32> = ours.pinned.iter().map(|(order, _)| *order).collect();
            if terms.get(&entry.leaf) != Some(&ours.leaf)
                || terms.get(&entry.operand) != Some(&ours.operand)
                || entry.orders != orders
            {
                return mismatch("other order-free nodes");
            }
        }
        let mut claims = Vec::new();
        for (root, ours) in target.roots().iter().zip(self.roots.clone()) {
            let Some(term) = terms.get(root).copied() else {
                return Ok(None);
            };
            if self.graph.find(term) != self.graph.find(ours) {
                return Ok(None);
            }
            if term != ours {
                claims.push(self.graph.explain(ours, term)?);
            }
        }
        Ok(Some(self.derivation(&claims)))
    }
}
