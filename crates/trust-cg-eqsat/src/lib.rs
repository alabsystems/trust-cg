// crates/trust-cg-eqsat/src/lib.rs - Tier E eager acyclic e-graph over trust-ir function bodies
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Tier E (`docs/eqsat-tier-e.md`, PKG-U1): an eager acyclic e-graph over one
//! trust-ir function body, with derivations an independent checker replays.
//!
//! # What this crate is, and is not
//!
//! * **Discovery only, untrusted.** [`optimize_function`] reads the body
//!   (only total integer and boolean operators on defined operands enter the
//!   graph, section 2), fires the rules of a [`rules::RuleSet`] eagerly when
//!   nodes are created, extracts the cheapest form of every skeleton operand
//!   from that operand's own Id tree, elaborates a new body, and writes a
//!   derivation (section 7) claiming, for every skeleton operand whose term
//!   changed, `(input term, output term, equiv | refines)`.
//! * **No claim of its own.** A fault here loses a form or produces a
//!   derivation `trust-cg-eqsat-check` refuses. Rules are statements, not
//!   theorems (PKG-U2 discharges them). Nothing calls this crate from the
//!   compiler (PKG-U3).
//! * **Never costlier.** When the elaborated body is not strictly cheaper by
//!   the static cost of section 6, the input is returned unchanged with the
//!   header-only derivation.
//! * **Deterministic.** Vectors and `BTreeMap`s only, rules fire in file
//!   order, no clock, no randomness: equal inputs give byte-identical
//!   derivations and equal bodies.
//!
//! Before returning a rewritten body the engine re-reads it and checks that
//! its skeleton is the input skeleton with only value operands changed, and
//! that the selector trace of every `exhaustive_enum_unreachable` switch is
//! the input's (`selector`); a body that fails that is never returned
//! (fail-closed decline).

#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::fmt;

use trust_ir::{Function, Module};

mod cfg;
pub mod derivation;
mod elaborate;
pub mod eval;
mod extract;
mod graph;
mod proof;
mod remap;
mod rewrite;
pub mod rules;
pub mod saturate;
mod selector;
mod to_graph;
pub mod vocab;

use crate::graph::{Entry, Node};
use crate::proof::EngineError;
use crate::rewrite::Engine;
use crate::rules::RuleSet;
use crate::to_graph::{InstClass, Reading};
use crate::vocab::GraphWidths;

/// Budgets of the eager engine (section 6). All count events (matches,
/// creation depth, arena entries), never time, so a run is deterministic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EngineConfig {
    /// Rules fire on a node created at depth `d` only while
    /// `d <= max_rewrite_depth`; a node of an input instruction has depth 0
    /// and a node created by instantiating a rhs on a depth-`d` node has
    /// depth `d + 1`.
    pub max_rewrite_depth: u32,
    /// The complete lhs matches examined per new node, over all rules.
    pub max_matches_per_node: u32,
    /// The arena bound per input instruction: once the arena holds
    /// `max_ids_per_instruction * (input instructions + 1)` entries, no rule
    /// fires any more (hash-consing and extraction continue), so the graph
    /// and the work per function are linear in the function's size. Each
    /// firing skipped for it is counted in [`Stats::budget_hits`].
    pub max_ids_per_instruction: u32,
}

impl Default for EngineConfig {
    /// `max_ids_per_instruction` 256, measured under the other two defaults
    /// with the integer identities: no function of the interim corpus
    /// exceeds 1.1 arena entries per (instruction + 1); the densest inputs
    /// found are chains, which saturate under the depth and match budgets at
    /// about 132 (`x = add x, c` with one shared constant, the
    /// 1500-instruction chain of `tests/engine_optimize.rs`) and 94
    /// (`x = add x, x`). The bound is about twice the densest, so it changes
    /// none of those outputs, and it still makes the arena of any rule set
    /// linear in the function's size. 128 would cut that 1500-instruction
    /// chain at the bound (cost 66 instead of 26).
    fn default() -> Self {
        Self {
            max_rewrite_depth: 3,
            max_matches_per_node: 64,
            max_ids_per_instruction: 256,
        }
    }
}

/// Why the engine does not touch a function. Every variant but
/// `Unsupported` is a section 2.5 refusal (the trust-cg-irmid ineligibility
/// classes) and [`Decline::class`] is its section 2.5 class name;
/// `Unsupported` is a shape the reader refuses fail-closed (a malformed body
/// as section 2.5 lists, a shape outside section 2, or an engine invariant
/// that did not hold).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decline {
    /// The function has no body.
    NoBody,
    /// `Function::proofs` is not empty.
    FunctionProofs,
    /// The function has a `summary`.
    Summary,
    /// The function has a `body_gate`.
    BodyGate,
    /// The function has `source_provenance`.
    SourceProvenance,
    /// An instruction has `proofs` or a `proof_context`.
    InstructionProofs,
    /// A module proof obligation names the function by `function` or
    /// `site.function`.
    ModuleObligation,
    /// A module proof obligation names no function (it refuses every
    /// function of the module).
    UnscopedObligation,
    /// The module has `spec_modules` (refuses every function).
    SpecModules,
    /// The module has refinement `predicates` (refuses every function):
    /// trust-ir-build's refinement check derives a fact for each value from
    /// its defining instruction, so replacing any graph instruction can change
    /// its verdict.
    RefinementPredicates,
    /// A block is not reachable from the entry block.
    UnreachableBlock,
    /// A shape the reader refuses, with the reason.
    Unsupported(String),
}

impl Decline {
    /// The section 2.5 class name, or `unsupported`.
    #[must_use]
    pub fn class(&self) -> &'static str {
        match self {
            Decline::NoBody => "no_body",
            Decline::FunctionProofs => "function_proofs",
            Decline::Summary => "summary",
            Decline::BodyGate => "body_gate",
            Decline::SourceProvenance => "source_provenance",
            Decline::InstructionProofs => "instruction_proofs",
            Decline::ModuleObligation => "module_obligation",
            Decline::UnscopedObligation => "unscoped_obligation",
            Decline::SpecModules => "spec_modules",
            Decline::RefinementPredicates => "refinement_predicates",
            Decline::UnreachableBlock => "unreachable_block",
            Decline::Unsupported(_) => "unsupported",
        }
    }
}

impl fmt::Display for Decline {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Decline::Unsupported(reason) => write!(f, "unsupported: {reason}"),
            other => f.write_str(other.class()),
        }
    }
}

impl std::error::Error for Decline {}

impl From<EngineError> for Decline {
    fn from(error: EngineError) -> Self {
        Decline::Unsupported(error.to_string())
    }
}

/// What the engine saw and did on one function.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Stats {
    /// Blocks of the body.
    pub blocks: usize,
    /// Graph instructions of the input (section 2.3).
    pub graph_instructions: usize,
    /// See-through copies of the input.
    pub see_through_copies: usize,
    /// Skeleton instructions of the input.
    pub skeleton_instructions: usize,
    /// Skeleton instructions of a graph form with a maybe-poison operand.
    pub frontier_instructions: usize,
    /// Arena entries (nodes, unions, directed edges).
    pub ids: usize,
    /// Concrete nodes.
    pub nodes: usize,
    /// Union-find classes of the concrete nodes.
    pub classes: usize,
    /// Matches that produced a union or directed edge, by rule name.
    pub rule_matches: BTreeMap<String, u64>,
    /// Budget exhaustions: a node whose rules did not fire for the rewrite
    /// depth or the arena bound, and a firing cut short by the match or the
    /// arena bound.
    pub budget_hits: u64,
    /// Static cost of the input body.
    pub cost_before: u64,
    /// Static cost of the returned body.
    pub cost_after: u64,
    /// By the operator class of a class's oldest concrete member: (classes,
    /// distinct concrete nodes in them).
    pub forms_by_class: BTreeMap<String, (u64, u64)>,
}

/// The result of [`optimize_function`].
#[derive(Debug, Clone)]
pub struct Optimized {
    /// The returned body (the input clone when `rewritten` is false).
    pub function: Function,
    /// The section 7.2 derivation (header-only when nothing changed).
    pub derivation: Vec<u8>,
    /// Whether the body changed.
    pub rewritten: bool,
    /// What the engine saw and did.
    pub stats: Stats,
}

struct Run<'r> {
    engine: Engine<'r>,
    reading: Reading,
    elaborated: elaborate::Elaborated,
    stats: Stats,
}

fn run<'r>(
    module: &Module,
    function: &Function,
    rules: &'r RuleSet,
    config: &EngineConfig,
) -> Result<Run<'r>, Decline> {
    let widths = GraphWidths::new(module.pointer_bits());
    let instructions = function.blocks.iter().map(|block| block.body.len()).sum();
    let mut engine = Engine::new(&function.name, rules.rules(), *config, widths, instructions);
    let reading = to_graph::read(module, function, &mut engine)?;
    let choices = extract::choose(&engine.graph)?;
    let elaborated = elaborate::elaborate(function, &reading, &mut engine, &choices)?;
    let stats = stats(&mut engine, &reading, function);
    check_skeleton(module, function, &reading, &elaborated.function)?;
    Ok(Run {
        engine,
        reading,
        elaborated,
        stats,
    })
}

/// Optimize one function body with `rules` (section 6) and write the
/// derivation of section 7.
///
/// # Errors
/// A [`Decline`] when the function is refused by section 2.5 or its body is
/// a shape the reader refuses.
pub fn optimize_function(
    module: &Module,
    function: &Function,
    rules: &RuleSet,
    config: &EngineConfig,
) -> Result<Optimized, Decline> {
    let Run {
        engine,
        reading,
        elaborated,
        mut stats,
    } = run(module, function, rules, config)?;
    if elaborated.cost_after < reading.cost_before {
        stats.cost_after = elaborated.cost_after;
        Ok(Optimized {
            function: elaborated.function,
            derivation: engine.prover.into_builder().finish(),
            rewritten: true,
            stats,
        })
    } else {
        stats.cost_after = reading.cost_before;
        Ok(Optimized {
            function: function.clone(),
            derivation: derivation::header_only(&function.name),
            rewritten: false,
            stats,
        })
    }
}

/// Read the body into a graph with no rules and elaborate it back, always
/// (even when it is not cheaper), so the converters are exercised. The
/// result keeps the skeleton and computes the same values.
///
/// # Errors
/// As [`optimize_function`].
pub fn round_trip(module: &Module, function: &Function) -> Result<Function, Decline> {
    let rules = RuleSet::empty();
    let run = run(module, function, &rules, &EngineConfig::default())?;
    Ok(run.elaborated.function)
}

fn stats(engine: &mut Engine<'_>, reading: &Reading, function: &Function) -> Stats {
    let mut by_root: BTreeMap<graph::Id, (graph::Id, u64)> = BTreeMap::new();
    let mut nodes = 0usize;
    let len = engine.graph.len();
    for raw in 0..len {
        let Ok(raw) = u32::try_from(raw) else {
            break;
        };
        let id = graph::id_from_raw(raw);
        if !matches!(engine.graph.entry(id), Ok(Entry::Node(_))) {
            continue;
        }
        nodes += 1;
        let root = engine.graph.find(id);
        let slot = by_root.entry(root).or_insert((id, 0));
        slot.0 = slot.0.min(id);
        slot.1 += 1;
    }
    let mut forms_by_class: BTreeMap<String, (u64, u64)> = BTreeMap::new();
    for (oldest, count) in by_root.values() {
        let name = match engine.graph.entry(*oldest) {
            Ok(Entry::Node(Node::Leaf { .. })) => "leaf",
            Ok(Entry::Node(Node::Const { .. })) => "const",
            Ok(Entry::Node(Node::Op { desc, .. })) => desc.class_name(),
            _ => "unknown",
        };
        let slot = forms_by_class.entry(name.to_owned()).or_insert((0, 0));
        slot.0 += 1;
        slot.1 += count;
    }
    Stats {
        blocks: function.blocks.len(),
        graph_instructions: reading.graph_instructions,
        see_through_copies: reading.see_through_copies,
        skeleton_instructions: reading.skeleton_instructions,
        frontier_instructions: reading.frontier_instructions,
        ids: len,
        nodes,
        classes: by_root.len(),
        rule_matches: engine.rule_matches.clone(),
        budget_hits: engine.budget_hits,
        cost_before: reading.cost_before,
        cost_after: reading.cost_before,
        forms_by_class,
    }
}

/// Re-read `output` and check its skeleton is `input`'s with only value
/// operands changed: per block the same skeleton instructions, each equal to
/// the input one with the output's operands substituted; and that every
/// flagged switch's selector trace is the input's (`selector` module doc).
fn check_skeleton(
    module: &Module,
    input: &Function,
    reading: &Reading,
    output: &Function,
) -> Result<(), Decline> {
    let empty = RuleSet::empty();
    let widths = GraphWidths::new(module.pointer_bits());
    let mut engine = Engine::new(
        &output.name,
        empty.rules(),
        EngineConfig::default(),
        widths,
        0,
    );
    let reread = to_graph::read(module, output, &mut engine).map_err(|decline| {
        Decline::Unsupported(format!("the output body is refused: {decline}"))
    })?;
    let mismatch = |what: &str| Decline::Unsupported(format!("output skeleton check: {what}"));
    if input.blocks.len() != output.blocks.len() {
        return Err(mismatch("block count"));
    }
    for (index, (before, after)) in input.blocks.iter().zip(&output.blocks).enumerate() {
        if before.id != after.id || before.params != after.params {
            return Err(mismatch("block identity or parameters"));
        }
        let skeleton = |reading: &Reading, block: &trust_ir::Block| {
            block
                .body
                .iter()
                .enumerate()
                .filter(|(position, _)| {
                    matches!(
                        reading.classes.get(index).and_then(|c| c.get(*position)),
                        Some(InstClass::Skeleton { .. })
                    )
                })
                .map(|(_, node)| node.clone())
                .collect::<Vec<_>>()
        };
        let old = skeleton(reading, before);
        let new = skeleton(&reread, after);
        if old.len() != new.len() {
            return Err(mismatch("skeleton instruction count"));
        }
        for (old, new) in old.iter().zip(&new) {
            let mut expected = old.clone();
            if !remap::replace_operands(&mut expected.inst, &remap::operands(&new.inst))
                || expected != *new
            {
                return Err(mismatch(
                    "a skeleton instruction changed beyond its operands",
                ));
            }
        }
    }
    if selector::traces(input) != selector::traces(output) {
        return Err(mismatch("an exhaustive switch's selector trace changed"));
    }
    Ok(())
}
