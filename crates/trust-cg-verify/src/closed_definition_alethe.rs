// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Untrusted Alethe construction from closed defining equations.
//!
//! This is not a solver, compiler, semantic normalization or proof authority.
//! The ONLY assumption is the complete, unchanged negated-equivalence formula.
//! Every original premise is projected from it. Actual operator/dependency
//! correspondence, not occurrence names or stage ordinals, supplies candidate
//! congruence steps. Independent checking against the ORIGINAL raw problem is
//! mandatory; a candidate never grants Valid, a receipt or native authority.

use crate::lowering_proof::ProofObligation;
use crate::smt::{EvalEnv, SmtExpr as E, SmtSort};
use crate::smt_raw_print::{
    CompactPrintRefusal, MAX_DEPTH, MAX_EDGES, MAX_NODES, MAX_OUTPUT_BYTES, MAX_PAYLOAD_BYTES,
    MAX_PREFIX_ATTEMPTS, MAX_SCRIPT_BYTES, checked_sort, preflight,
};
use std::collections::{HashMap, HashSet};
use std::convert::Infallible;
use std::fmt::{self, Write};
use std::sync::Arc;

#[path = "closed_definition_alethe_guard.rs"]
mod guard;

// Unsupported by the current captured checker: construction/diagnostics only.
#[cfg(test)]
#[path = "closed_definition_alethe_polynomial.rs"]
mod polynomial;

#[cfg(test)]
#[path = "closed_definition_alethe_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "closed_definition_alethe_guard_tests.rs"]
mod guard_tests;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum ClosedDefinitionRefusal {
    #[error("closed-definition candidate unsupported: {0}")]
    Unsupported(&'static str),
    #[error("closed-definition candidate malformed: {0}")]
    Malformed(&'static str),
    #[error("closed-definition candidate resource limit: {0}")]
    Budget(&'static str),
}

impl From<CompactPrintRefusal> for ClosedDefinitionRefusal {
    fn from(error: CompactPrintRefusal) -> Self {
        match error {
            CompactPrintRefusal::Budget(reason) => Self::Budget(reason),
            CompactPrintRefusal::Unsupported(reason) => Self::Unsupported(reason),
            CompactPrintRefusal::Sort(reason) => Self::Malformed(reason),
        }
    }
}

/// Untrusted text and construction census ONLY. No checked constructor exists.
#[derive(Debug)]
pub(crate) struct ClosedDefinitionCandidate {
    pub(crate) text: String,
    pub(crate) premises: usize,
    pub(crate) definitions: usize,
    /// Number of `step` commands, excluding the sole original `assume`.
    pub(crate) steps: usize,
}

type Id = usize;
type Pair = (Id, Id);

/// Actual OR edges and terminal leaves, never a normalized replacement goal.
struct OrForest {
    parents: HashMap<Id, (Id, usize)>,
    leaves: Vec<Id>,
}

struct Node<'a> {
    original: &'a E,
    /// Shallow exact operator/metadata with typed, positional child aliases.
    head: E,
    children: Vec<Id>,
    sort: SmtSort,
    /// Selection data ONLY: a bottom-up literal leaf from shallow literal
    /// children or an actual acyclic definition. Every use still needs a proof
    /// from the original equations; never evaluate an expanded DAG.
    literal: Option<E>,
    spelling: Option<E>,
}

impl Node<'_> {
    fn spelled(&self) -> &E {
        self.spelling.as_ref().unwrap_or(self.original)
    }
}

#[derive(Clone, Copy)]
struct Definition {
    rhs: Id,
    premise: Id,
}

struct Graph<'a> {
    nodes: Vec<Node<'a>>,
    pointers: HashMap<*const E, Id>,
    definitions: HashMap<Id, Definition>,
}

impl<'a> Graph<'a> {
    fn new(formula: &'a E) -> Result<Self, ClosedDefinitionRefusal> {
        let bounded = preflight(formula)?;
        let mut nodes: Vec<Node<'a>> = Vec::new();
        let mut pointers = HashMap::<*const E, Id>::new();
        // Hash/equality visit only a shallow shell and numeric child IDs, NEVER
        // an expanded subtree. Equal symbols/operators need not share an Arc.
        let mut interned = HashMap::<(E, Vec<Id>), Id>::new();
        let mut symbols = HashMap::<String, (bool, SmtSort)>::new();
        for original in bounded.order {
            let mut children = Vec::<Id>::new();
            original.for_each_child(&mut |child| children.push(pointers[&(child as *const E)]));
            let mut position = 0usize;
            let head = original
                .try_map_children::<Infallible>(&mut |_| {
                    let sort = nodes[children[position]].sort.clone();
                    let alias = E::uf(format!("slot{position}"), vec![], sort);
                    position += 1;
                    Ok(Arc::new(alias))
                })
                .unwrap_or_else(|never| match never {});
            let sort = checked_sort(&head)?;
            let symbol = match original {
                E::Var { name, .. } => Some((name, false)),
                E::UF { name, args, .. } if args.is_empty() => Some((name, true)),
                E::UF { .. } => {
                    return Err(ClosedDefinitionRefusal::Unsupported(
                        "argumented uninterpreted function",
                    ));
                }
                _ => None,
            };
            if let Some((name, uninterpreted)) = symbol {
                let declaration = (uninterpreted, sort.clone());
                if symbols.get(name).is_some_and(|old| *old != declaration) {
                    return Err(ClosedDefinitionRefusal::Malformed(
                        "conflicting symbol declaration",
                    ));
                }
                symbols.entry(name.clone()).or_insert(declaration);
            }
            if let E::BvConst { value, width } = original
                && *width < 64
                && *value >= 1u64 << width
            {
                return Err(ClosedDefinitionRefusal::Malformed(
                    "noncanonical bitvector literal",
                ));
            }
            let key = (head.clone(), children.clone());
            let id = match interned.get(&key) {
                Some(id) => *id,
                None => {
                    let id = nodes.len();
                    let literal = literal_value(
                        original,
                        &sort,
                        children.iter().map(|child| nodes[*child].literal.clone()),
                    );
                    nodes.push(Node {
                        original,
                        head,
                        children,
                        sort,
                        literal,
                        spelling: None,
                    });
                    interned.insert(key, id);
                    id
                }
            };
            pointers.insert(original as *const E, id);
        }
        Ok(Self {
            nodes,
            pointers,
            definitions: HashMap::new(),
        })
    }

    fn sharing(
        &mut self,
        obligation: &ProofObligation,
        text: &mut Text,
    ) -> Result<(), ClosedDefinitionRefusal> {
        // Proof-local nullary definitions are exact parser macros, NOT query
        // declarations, new inputs, equality premises or extra assumptions.
        // Include unused declarations and quoted symbols in the freshness scan.
        let prefix = (0..MAX_PREFIX_ATTEMPTS).map(|i| format!("tcg!cd{i}_"))
            .find(|prefix| {
                !obligation.inputs.iter().any(|(name, _)| name.contains(prefix))
                    && !obligation.fp_inputs.iter().any(|(name, _, _)| name.contains(prefix))
                    && !self.nodes.iter().any(|node| matches!(node.original, E::Var { name, .. } | E::UF { name, .. } if name.contains(prefix)))
            })
            .ok_or(ClosedDefinitionRefusal::Budget("fresh-name attempts"))?;
        for id in 0..self.nodes.len() {
            if self.nodes[id].children.is_empty() {
                continue;
            }
            let mut position = 0usize;
            let body = self.nodes[id]
                .original
                .try_map_children::<Infallible>(&mut |_| {
                    let child = self.nodes[id].children[position];
                    position += 1;
                    Ok(Arc::new(self.nodes[child].spelled().clone()))
                })
                .unwrap_or_else(|never| match never {});
            let name = format!("{prefix}{id}");
            let sort = self.nodes[id].sort.clone();
            text.write(format_args!("(define-fun {name} () {sort} {body})\n"))?;
            self.nodes[id].spelling = Some(E::uf(name, vec![], sort));
        }
        Ok(())
    }

    fn definition(&mut self, id: Id, premise: Id) -> Result<(), ClosedDefinitionRefusal> {
        let node = &self.nodes[id];
        if !matches!(node.original, E::Eq { .. }) {
            return Ok(());
        }
        let [lhs, rhs] = node.children.as_slice() else {
            return Err(ClosedDefinitionRefusal::Malformed(
                "definition equality arity",
            ));
        };
        if !matches!(self.nodes[*lhs].original, E::UF { args, .. } if args.is_empty()) {
            return Ok(());
        }
        if self
            .definitions
            .insert(*lhs, Definition { rhs: *rhs, premise })
            .is_some()
        {
            return Err(ClosedDefinitionRefusal::Malformed("duplicate definition"));
        }
        Ok(())
    }

    fn acyclic(&self, mut order: Option<&mut Vec<Id>>) -> Result<(), ClosedDefinitionRefusal> {
        // Add only actual definition-to-RHS edges to the already bounded AST.
        // Global validation covers even equations unused by the final goal.
        let mut color = vec![0u8; self.nodes.len()];
        for root in 0..self.nodes.len() {
            let mut pending = vec![(root, false)];
            while let Some((id, ready)) = pending.pop() {
                if ready {
                    color[id] = 2;
                    if let Some(order) = &mut order {
                        order.push(id);
                    }
                    continue;
                }
                match color[id] {
                    2 => continue,
                    1 => return Err(ClosedDefinitionRefusal::Malformed("cyclic definitions")),
                    _ => {}
                }
                color[id] = 1;
                pending.push((id, true));
                if let Some(definition) = self.definitions.get(&id) {
                    pending.push((definition.rhs, false));
                } else {
                    pending.extend(
                        self.nodes[id]
                            .children
                            .iter()
                            .rev()
                            .map(|child| (*child, false)),
                    );
                }
            }
        }
        Ok(())
    }

    /// Values select possible proof paths, not new facts. The dependency order
    /// includes only genuine, globally validated original defining equations.
    /// Unknown operators or symbolic children keep the value unknown.
    fn prepare_literals(
        &mut self,
        order: &[Id],
        visits: &mut usize,
        edges: &mut usize,
    ) -> Result<(), ClosedDefinitionRefusal> {
        for &id in order {
            reserve_visits(visits, 1)?;
            let literal = if let Some(definition) = self.definitions.get(&id) {
                reserve_work::<Id>(&[], edges, 1)?;
                self.nodes[definition.rhs].literal.clone()
            } else {
                let node = &self.nodes[id];
                reserve_work::<Id>(&[], edges, node.children.len())?;
                literal_value(
                    node.original,
                    &node.sort,
                    node.children
                        .iter()
                        .map(|child| self.nodes[*child].literal.clone()),
                )
            };
            self.nodes[id].literal = literal;
        }
        Ok(())
    }

    /// Selection keys ONLY, never a fact or a rewritten query. The actual
    /// original-term equality engine must justify every selected correspondence.
    fn canonical_keys(&self, order: &[Id]) -> Result<(Vec<Id>, usize), ClosedDefinitionRefusal> {
        let mut keys: Vec<Option<Id>> = vec![None; self.nodes.len()];
        let mut interned = HashMap::<(E, Vec<Id>), Id>::new();
        let mut edges = 0usize;
        for &id in order {
            let key = if let Some(definition) = self.definitions.get(&id) {
                edges += 1;
                keys[definition.rhs]
                    .ok_or(ClosedDefinitionRefusal::Malformed("definition key order"))?
            } else {
                edges = edges
                    .checked_add(self.nodes[id].children.len())
                    .ok_or(ClosedDefinitionRefusal::Budget("definition key edges"))?;
                let node = &self.nodes[id];
                let shape = if let Some(literal) = &node.literal {
                    (literal.clone(), vec![])
                } else {
                    let children = node
                        .children
                        .iter()
                        .map(|child| {
                            keys[*child]
                                .ok_or(ClosedDefinitionRefusal::Malformed("definition key order"))
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    (node.head.clone(), children)
                };
                let next = interned.len();
                *interned.entry(shape).or_insert(next)
            };
            if edges > MAX_EDGES {
                return Err(ClosedDefinitionRefusal::Budget("definition key edges"));
            }
            keys[id] = Some(key);
        }
        let keys = keys
            .into_iter()
            .map(|key| key.ok_or(ClosedDefinitionRefusal::Malformed("missing definition key")))
            .collect::<Result<Vec<_>, _>>()?;
        Ok((keys, edges))
    }
}

// Evaluate ONLY a closed subset already modeled by the shared evaluator and
// supported by the ordinary Alethe `evaluate` rule. No variable assignment,
// memory model, arithmetic rewrite, inferred equality or solver is introduced.
fn literal_operator(node: &E) -> bool {
    matches!(
        node,
        E::BvConst { width: 1..=64, .. }
            | E::BoolConst(_)
            | E::BvAdd { width: 1..=64, .. }
            | E::BvMul { width: 1..=64, .. }
            | E::BvAnd { width: 1..=64, .. }
            | E::BvOr { width: 1..=64, .. }
            | E::BvXor { width: 1..=64, .. }
            | E::BvNeg { width: 1..=64, .. }
            | E::Concat { width: 1..=64, .. }
            | E::ZeroExtend { width: 1..=64, .. }
            | E::Eq { .. }
            | E::Not { .. }
            | E::And { .. }
            | E::Or { .. }
            | E::Ite { .. }
    )
}

/// This is the existing literal evaluator applied to ONE exact operator shell.
/// The supplied child values are literal leaves; unresolved symbols are never
/// assigned values in an EvalEnv or recursively expanded into an expression.
fn literal_value(
    node: &E,
    sort: &SmtSort,
    mut children: impl Iterator<Item = Option<E>>,
) -> Option<E> {
    if !literal_operator(node) {
        return None;
    }
    let shallow = node
        .try_map_children::<()>(&mut |_| children.next().flatten().map(Arc::new).ok_or(()))
        .ok()?;
    match (shallow.try_eval(&EvalEnv::default()).ok(), sort) {
        (Some(crate::smt::EvalResult::Bv(value)), SmtSort::BitVec(width @ (1..=64))) => {
            Some(E::bv_const(value, *width))
        }
        (Some(crate::smt::EvalResult::Bool(value)), SmtSort::Bool) => Some(E::BoolConst(value)),
        _ => None,
    }
}

struct Text {
    text: String,
    next: Id,
    steps: usize,
}

impl Write for Text {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        if self
            .text
            .len()
            .checked_add(text.len())
            .is_none_or(|n| n > MAX_OUTPUT_BYTES)
        {
            return Err(fmt::Error);
        }
        self.text.push_str(text);
        Ok(())
    }
}

impl Text {
    fn allocate(&mut self) -> Result<Id, ClosedDefinitionRefusal> {
        let id = self.next;
        self.next = id
            .checked_add(1)
            .ok_or(ClosedDefinitionRefusal::Budget("proof commands"))?;
        Ok(id)
    }

    fn write(&mut self, args: fmt::Arguments<'_>) -> Result<(), ClosedDefinitionRefusal> {
        self.write_fmt(args)
            .map_err(|_| ClosedDefinitionRefusal::Budget("output bytes"))
    }

    fn assume(&mut self, formula: &E) -> Result<Id, ClosedDefinitionRefusal> {
        let id = self.allocate()?;
        self.write(format_args!("(assume cd{id} {formula})\n"))?;
        Ok(id)
    }

    fn begin(&mut self, clause: fmt::Arguments<'_>) -> Result<Id, ClosedDefinitionRefusal> {
        let id = self.allocate()?;
        self.steps += 1;
        self.write(format_args!("(step cd{id} (cl"))?;
        self.write(clause)?;
        self.write(format_args!(")"))?;
        Ok(id)
    }

    fn end(
        &mut self,
        rule: &str,
        premises: &[Id],
        arg: Option<usize>,
    ) -> Result<(), ClosedDefinitionRefusal> {
        self.write(format_args!(" :rule {rule}"))?;
        if !premises.is_empty() {
            self.write(format_args!(" :premises ("))?;
            for (index, premise) in premises.iter().enumerate() {
                if index > 0 {
                    self.write(format_args!(" "))?;
                }
                self.write(format_args!("cd{premise}"))?;
            }
            self.write(format_args!(")"))?;
        }
        if let Some(arg) = arg {
            self.write(format_args!(" :args ({arg})"))?;
        }
        self.write(format_args!(")\n"))
    }

    fn unit(
        &mut self,
        term: &E,
        rule: &str,
        premises: &[Id],
        arg: Option<usize>,
    ) -> Result<Id, ClosedDefinitionRefusal> {
        let id = self.begin(format_args!(" {term}"))?;
        self.end(rule, premises, arg)?;
        Ok(id)
    }

    fn equality(
        &mut self,
        left: &E,
        right: &E,
        rule: &str,
        premises: &[Id],
    ) -> Result<Id, ClosedDefinitionRefusal> {
        let id = self.begin(format_args!(" (= {left} {right})"))?;
        self.end(rule, premises, None)?;
        Ok(id)
    }
}

enum Work {
    Visit(Pair),
    Alias {
        pair: Pair,
        inner: Pair,
        left: Option<Definition>,
        right: Option<Definition>,
    },
    Selected {
        pair: Pair,
        inner: Pair,
        left: Option<Id>,
        right: Option<Id>,
    },
    Congruence {
        pair: Pair,
        children: Vec<Pair>,
    },
}

enum LiteralWork {
    Visit(Id),
    Alias { node: Id, definition: Definition },
    Compound(Id),
}

enum TruthWork {
    Visit(Id),
    Conjunction(Id),
    Lift {
        root: Id,
        leaf: Id,
        parents: HashMap<Id, (Id, usize)>,
    },
}

struct Composer<'a> {
    graph: Graph<'a>,
    text: Text,
    equalities: HashMap<Pair, Id>,
    /// Only unconditional equalities grounded in the complete original premise
    /// inventory. No branch- or guard-local fact may enter this memo.
    literal_equalities: HashMap<Id, Id>,
    keys: Vec<Id>,
    known_true: HashMap<Id, (Id, Id)>,
    truths: HashMap<Id, Id>,
    /// Signed units derived from this candidate's sole original refutation.
    /// Never consulted by unconditional literal metadata or its proof memo.
    root_facts: Option<guard::RootFacts>,
    /// One branch theorem per original ITE under the same immutable root.
    selected_ites: HashMap<Id, (Id, Id)>,
    #[cfg(test)]
    modular_candidate: bool,
    visits: usize,
    edges: usize,
}

impl Composer<'_> {
    fn selected_ite(&mut self, id: Id) -> Result<Option<(Id, Id)>, ClosedDefinitionRefusal> {
        if let Some(proof) = self.selected_ites.get(&id) {
            return Ok(Some(*proof));
        }
        let node = &self.graph.nodes[id];
        if !matches!(node.original, E::Ite { .. }) {
            return Ok(None);
        }
        let condition = node.children[0];
        let fact = self.root_facts.as_ref().and_then(|facts| {
            facts
                .get(condition, true)
                .or_else(|| facts.get(condition, false))
        });
        if let Some(fact) = fact {
            // Bound the additional memo entry before deriving its theorem.
            reserve_visits(&mut self.visits, 1)?;
            let selected = self.ite_branch_equality(id, fact)?;
            self.selected_ites.insert(id, selected);
            Ok(Some(selected))
        } else {
            Ok(None)
        }
    }

    /// Boolean equality transport using only the checker’s core Alethe rules.
    /// The equality and the original left-term unit must BOTH be established.
    fn transport(
        &mut self,
        from: Id,
        to: Id,
        premise: Id,
        equality: Id,
    ) -> Result<Id, ClosedDefinitionRefusal> {
        reserve_work::<Work>(&[], &mut self.edges, 2)?;
        let bridge = self.text.begin(format_args!(
            " (not {}) {}",
            self.graph.nodes[from].spelled(),
            self.graph.nodes[to].spelled()
        ))?;
        self.text.end("equiv1", &[equality], None)?;
        self.text.unit(
            self.graph.nodes[to].spelled(),
            "resolution",
            &[premise, bridge],
            None,
        )
    }

    fn literal(&mut self, pair: Pair) -> Result<Option<Id>, ClosedDefinitionRefusal> {
        let left = &self.graph.nodes[pair.0];
        let right = &self.graph.nodes[pair.1];
        let (Some(a), Some(b)) = (&left.literal, &right.literal) else {
            return Ok(None);
        };
        if a != b {
            return Ok(None);
        }
        reserve_work::<LiteralWork>(&[], &mut self.edges, 2)?;
        let a = self.literal_equality(pair.0)?;
        let b = self.literal_equality(pair.1)?;
        Ok(Some(self.text.equality(
            self.graph.nodes[pair.0].spelled(),
            self.graph.nodes[pair.1].spelled(),
            "trans",
            &[a, b],
        )?))
    }

    /// Prove an actual term equal to its selected literal. An original UF is
    /// related through its projected equation, NEVER through `evaluate`.
    /// Compound evaluation first proves every child-to-literal equality and
    /// lifts them by congruence to a shallow, genuinely closed operator shell.
    fn literal_equality(&mut self, goal: Id) -> Result<Id, ClosedDefinitionRefusal> {
        let mut pending = vec![LiteralWork::Visit(goal)];
        while let Some(work) = pending.pop() {
            match work {
                LiteralWork::Visit(id) => {
                    if self.literal_equalities.contains_key(&id) {
                        continue;
                    }
                    reserve_visits(&mut self.visits, 1)?;
                    let node = &self.graph.nodes[id];
                    let value =
                        node.literal
                            .as_ref()
                            .ok_or(ClosedDefinitionRefusal::Unsupported(
                                "no literal derivation",
                            ))?;
                    if let Some(definition) = self.graph.definitions.get(&id).copied() {
                        // Two scheduled work items and two trans premises.
                        reserve_work(&pending, &mut self.edges, 4)?;
                        pending.push(LiteralWork::Alias {
                            node: id,
                            definition,
                        });
                        pending.push(LiteralWork::Visit(definition.rhs));
                    } else if !literal_operator(node.original) {
                        return Err(ClosedDefinitionRefusal::Unsupported(
                            "no literal derivation",
                        ));
                    } else if node.children.is_empty() {
                        let proof = self.text.equality(node.spelled(), value, "evaluate", &[])?;
                        self.literal_equalities.insert(id, proof);
                    } else {
                        // Child work plus congruence/evaluation/transitivity
                        // references all share the ordinary aggregate cap.
                        reserve_work(&pending, &mut self.edges, node.children.len() * 2 + 3)?;
                        pending.push(LiteralWork::Compound(id));
                        pending
                            .extend(node.children.iter().rev().map(|id| LiteralWork::Visit(*id)));
                    }
                }
                LiteralWork::Alias {
                    node: id,
                    definition,
                } => {
                    let node = &self.graph.nodes[id];
                    let value =
                        node.literal
                            .as_ref()
                            .ok_or(ClosedDefinitionRefusal::Unsupported(
                                "no literal derivation",
                            ))?;
                    let proof = self.text.equality(
                        node.spelled(),
                        value,
                        "trans",
                        &[definition.premise, self.literal_equalities[&definition.rhs]],
                    )?;
                    self.literal_equalities.insert(id, proof);
                }
                LiteralWork::Compound(id) => {
                    let node = &self.graph.nodes[id];
                    let mut position = 0usize;
                    let shallow = node
                        .original
                        .try_map_children::<Infallible>(&mut |_| {
                            let child = node.children[position];
                            position += 1;
                            // Visit proved every one of these literal leaves.
                            Ok(Arc::new(
                                self.graph.nodes[child].literal.as_ref().unwrap().clone(),
                            ))
                        })
                        .unwrap_or_else(|never| match never {});
                    let premises: Vec<_> = node
                        .children
                        .iter()
                        .map(|child| self.literal_equalities[child])
                        .collect();
                    let congruence =
                        self.text
                            .equality(node.spelled(), &shallow, "cong", &premises)?;
                    let value =
                        node.literal
                            .as_ref()
                            .ok_or(ClosedDefinitionRefusal::Unsupported(
                                "no literal derivation",
                            ))?;
                    let evaluation = self.text.equality(&shallow, value, "evaluate", &[])?;
                    let proof = self.text.equality(
                        node.spelled(),
                        value,
                        "trans",
                        &[congruence, evaluation],
                    )?;
                    self.literal_equalities.insert(id, proof);
                }
            }
        }
        Ok(self.literal_equalities[&goal])
    }

    fn equality(&mut self, goal: Pair) -> Result<Id, ClosedDefinitionRefusal> {
        let mut pending = vec![Work::Visit(goal)];
        let mut active = HashSet::new();
        while let Some(work) = pending.pop() {
            match work {
                Work::Visit(pair) => {
                    if self.equalities.contains_key(&pair) {
                        continue;
                    }
                    reserve_visits(&mut self.visits, 1)?;
                    let left = &self.graph.nodes[pair.0];
                    let right = &self.graph.nodes[pair.1];
                    if left.sort != right.sort {
                        return Err(ClosedDefinitionRefusal::Unsupported("goal sort differs"));
                    }
                    if pair.0 == pair.1 {
                        let id =
                            self.text
                                .equality(left.spelled(), right.spelled(), "refl", &[])?;
                        self.equalities.insert(pair, id);
                        continue;
                    }
                    if let Some(reverse) = self.equalities.get(&(pair.1, pair.0)) {
                        let id = self.text.equality(
                            left.spelled(),
                            right.spelled(),
                            "symm",
                            &[*reverse],
                        )?;
                        self.equalities.insert(pair, id);
                        continue;
                    }
                    if !active.insert(pair) {
                        return Err(ClosedDefinitionRefusal::Malformed("cyclic equality work"));
                    }
                    let left_definition = self.graph.definitions.get(&pair.0).copied();
                    let right_definition = self.graph.definitions.get(&pair.1).copied();
                    if left_definition.is_some() || right_definition.is_some() {
                        reserve_work(&pending, &mut self.edges, 2)?;
                        let inner = (
                            left_definition.map_or(pair.0, |d| d.rhs),
                            right_definition.map_or(pair.1, |d| d.rhs),
                        );
                        pending.push(Work::Alias {
                            pair,
                            inner,
                            left: left_definition,
                            right: right_definition,
                        });
                        pending.push(Work::Visit(inner));
                        continue;
                    }
                    let left_selected = self.selected_ite(pair.0)?;
                    let right_selected = self.selected_ite(pair.1)?;
                    if left_selected.is_some() || right_selected.is_some() {
                        reserve_work(&pending, &mut self.edges, 2)?;
                        let inner = (
                            left_selected.map_or(pair.0, |selected| selected.0),
                            right_selected.map_or(pair.1, |selected| selected.0),
                        );
                        pending.push(Work::Selected {
                            pair,
                            inner,
                            left: left_selected.map(|selected| selected.1),
                            right: right_selected.map(|selected| selected.1),
                        });
                        pending.push(Work::Visit(inner));
                        continue;
                    }
                    #[cfg(test)]
                    if self.modular_candidate {
                        let left = &self.graph.nodes[pair.0];
                        let right = &self.graph.nodes[pair.1];
                        let same_head =
                            left.head == right.head && left.children.len() == right.children.len();
                        // Keep working literal/congruence routes first. Shallow
                        // polynomial identities extend mismatched BV root shapes;
                        // they do not replace existing same-head derivations.
                        let polynomial = if !same_head {
                            if let Some(proof) = self.literal(pair)? {
                                self.equalities.insert(pair, proof);
                                active.remove(&pair);
                                continue;
                            }
                            self.polynomial_equality(pair)?
                        } else if matches!(left.original, E::Eq { .. })
                            && left.children.iter().zip(&right.children).any(|(a, b)| {
                                self.graph.nodes[*a].head != self.graph.nodes[*b].head
                                    && (polynomial::affine_operator(self.graph.nodes[*a].original)
                                        || polynomial::affine_operator(
                                            self.graph.nodes[*b].original,
                                        ))
                            })
                        {
                            self.polynomial_predicate_equality(pair)?
                        } else {
                            None
                        };
                        if let Some(proof) = polynomial {
                            self.equalities.insert(pair, proof);
                            active.remove(&pair);
                            continue;
                        }
                    }
                    let left = &self.graph.nodes[pair.0];
                    let right = &self.graph.nodes[pair.1];
                    if left.head == right.head && left.children.len() == right.children.len() {
                        let children: Vec<_> = left
                            .children
                            .iter()
                            .copied()
                            .zip(right.children.iter().copied())
                            .filter(|(a, b)| a != b)
                            .collect();
                        if children.is_empty() {
                            return Err(ClosedDefinitionRefusal::Malformed(
                                "inconsistent interned node",
                            ));
                        }
                        reserve_work(&pending, &mut self.edges, children.len() + 1)?;
                        pending.push(Work::Congruence {
                            pair,
                            children: children.clone(),
                        });
                        pending.extend(children.into_iter().rev().map(Work::Visit));
                        continue;
                    }
                    if let Some(id) = self.literal(pair)? {
                        self.equalities.insert(pair, id);
                        active.remove(&pair);
                        continue;
                    }
                    return Err(ClosedDefinitionRefusal::Unsupported(
                        "no congruence derivation",
                    ));
                }
                Work::Alias {
                    pair,
                    inner,
                    left,
                    right,
                } => {
                    let mut premises = Vec::with_capacity(3);
                    if let Some(left) = left {
                        premises.push(left.premise);
                    }
                    premises.push(self.equalities[&inner]);
                    if let Some(right) = right {
                        premises.push(right.premise);
                    }
                    let id = self.text.equality(
                        self.graph.nodes[pair.0].spelled(),
                        self.graph.nodes[pair.1].spelled(),
                        "trans",
                        &premises,
                    )?;
                    self.equalities.insert(pair, id);
                    active.remove(&pair);
                }
                Work::Congruence { pair, children } => {
                    let premises: Vec<_> =
                        children.iter().map(|pair| self.equalities[pair]).collect();
                    let id = self.text.equality(
                        self.graph.nodes[pair.0].spelled(),
                        self.graph.nodes[pair.1].spelled(),
                        "cong",
                        &premises,
                    )?;
                    self.equalities.insert(pair, id);
                    active.remove(&pair);
                }
                Work::Selected {
                    pair,
                    inner,
                    left,
                    right,
                } => {
                    reserve_work::<Work>(
                        &[],
                        &mut self.edges,
                        1 + usize::from(left.is_some()) + usize::from(right.is_some()),
                    )?;
                    let mut premises = Vec::with_capacity(3);
                    if let Some(proof) = left {
                        premises.push(proof);
                    }
                    premises.push(self.equalities[&inner]);
                    if let Some(proof) = right {
                        premises.push(proof);
                    }
                    let proof = self.text.equality(
                        self.graph.nodes[pair.0].spelled(),
                        self.graph.nodes[pair.1].spelled(),
                        "trans",
                        &premises,
                    )?;
                    self.equalities.insert(pair, proof);
                    active.remove(&pair);
                }
            }
        }
        Ok(self.equalities[&goal])
    }

    fn truth(&mut self, goal: Id, true_node: Id) -> Result<Id, ClosedDefinitionRefusal> {
        let mut pending = vec![TruthWork::Visit(goal)];
        while let Some(work) = pending.pop() {
            match work {
                TruthWork::Visit(id) => {
                    if self.truths.contains_key(&id) {
                        continue;
                    }
                    reserve_visits(&mut self.visits, 1)?;
                    if self.graph.nodes[id].sort != SmtSort::Bool {
                        return Err(ClosedDefinitionRefusal::Unsupported(
                            "non-Boolean truth goal",
                        ));
                    }
                    if let Some(fact) = self
                        .root_facts
                        .as_ref()
                        .and_then(|facts| facts.get(id, true))
                    {
                        self.truths.insert(id, fact.proof());
                        continue;
                    }
                    if let Some((premise_node, premise)) =
                        self.known_true.get(&self.keys[id]).copied()
                    {
                        let equal = self.equality((premise_node, id))?;
                        let proof = self.transport(premise_node, id, premise, equal)?;
                        self.truths.insert(id, proof);
                        continue;
                    }
                    if self.graph.nodes[id].literal.as_ref() == Some(&E::BoolConst(true)) {
                        let true_proof = if let Some(proof) = self.truths.get(&true_node) {
                            *proof
                        } else {
                            let proof = self.text.unit(
                                self.graph.nodes[true_node].spelled(),
                                "true",
                                &[],
                                None,
                            )?;
                            self.truths.insert(true_node, proof);
                            proof
                        };
                        let equal = self.equality((true_node, id))?;
                        let proof = self.transport(true_node, id, true_proof, equal)?;
                        self.truths.insert(id, proof);
                        continue;
                    }
                    match self.graph.nodes[id].original {
                        E::And { .. } => {
                            reserve_work(&pending, &mut self.edges, 3)?;
                            pending.push(TruthWork::Conjunction(id));
                            pending.extend(
                                self.graph.nodes[id]
                                    .children
                                    .iter()
                                    .rev()
                                    .map(|child| TruthWork::Visit(*child)),
                            );
                        }
                        E::Or { .. } => {
                            let OrForest { parents, leaves } = self.or_leaves(id)?;
                            let mut atoms = HashMap::<(Id, bool), (Id, Id)>::new();
                            let mut complement = None;
                            let mut known = None;
                            let mut guarded_equality = None;
                            for leaf in leaves {
                                if self.root_facts.is_some()
                                    && guarded_equality.is_none()
                                    && matches!(self.graph.nodes[leaf].original, E::Eq { .. })
                                {
                                    guarded_equality = Some(leaf);
                                }
                                if known.is_none()
                                    && (self.known_true.contains_key(&self.keys[leaf])
                                        || self
                                            .root_facts
                                            .as_ref()
                                            .is_some_and(|facts| facts.get(leaf, true).is_some())
                                        || self.graph.nodes[leaf].literal.as_ref()
                                            == Some(&E::BoolConst(true)))
                                {
                                    known = Some(leaf);
                                }
                                let (base, polarity) = self.signed_atom(leaf)?;
                                let key = self.keys[base];
                                if let Some(&(other_leaf, other_base)) =
                                    atoms.get(&(key, !polarity))
                                {
                                    complement = Some(if polarity {
                                        (other_leaf, other_base, leaf, base)
                                    } else {
                                        (leaf, base, other_leaf, other_base)
                                    });
                                    break;
                                }
                                atoms.entry((key, polarity)).or_insert((leaf, base));
                            }
                            if let Some((negative_leaf, negative, positive_leaf, positive)) =
                                complement
                            {
                                let equal = self.equality((negative, positive))?;
                                let bridge = self.text.begin(format_args!(
                                    " (not {}) {}",
                                    self.graph.nodes[negative].spelled(),
                                    self.graph.nodes[positive].spelled()
                                ))?;
                                self.text.end("equiv1", &[equal], None)?;
                                let negative_lift = self.lift_or(id, negative_leaf, &parents)?;
                                let positive_lift = self.lift_or(id, positive_leaf, &parents)?;
                                // Resolution strips only logical negations; every intermediate
                                // clause is still independently checked over ORIGINAL terms.
                                let partial = self.text.begin(format_args!(
                                    " {} {}",
                                    self.graph.nodes[id].spelled(),
                                    self.graph.nodes[positive].spelled()
                                ))?;
                                self.text
                                    .end("resolution", &[bridge, negative_lift], None)?;
                                let duplicates = self.text.begin(format_args!(
                                    " {} {}",
                                    self.graph.nodes[id].spelled(),
                                    self.graph.nodes[id].spelled()
                                ))?;
                                self.text
                                    .end("resolution", &[partial, positive_lift], None)?;
                                let proof = self.text.unit(
                                    self.graph.nodes[id].spelled(),
                                    "contraction",
                                    &[duplicates],
                                    None,
                                )?;
                                self.truths.insert(id, proof);
                            } else if let Some(leaf) = known.or(guarded_equality) {
                                reserve_work(&pending, &mut self.edges, 2)?;
                                pending.push(TruthWork::Lift {
                                    root: id,
                                    leaf,
                                    parents,
                                });
                                pending.push(TruthWork::Visit(leaf));
                            } else {
                                return Err(ClosedDefinitionRefusal::Unsupported(
                                    "no Boolean entailment",
                                ));
                            }
                        }
                        E::Eq { .. } if self.root_facts.is_some() => {
                            let pair = (
                                self.graph.nodes[id].children[0],
                                self.graph.nodes[id].children[1],
                            );
                            // The emitted equality is this exact original leaf
                            // after its proof-local term macro is expanded.
                            let proof = self.equality(pair)?;
                            self.truths.insert(id, proof);
                        }
                        _ => {
                            return Err(ClosedDefinitionRefusal::Unsupported(
                                "no Boolean entailment",
                            ));
                        }
                    }
                }
                TruthWork::Conjunction(id) => {
                    reserve_work::<Work>(&[], &mut self.edges, 3)?;
                    let [left, right] = [
                        self.graph.nodes[id].children[0],
                        self.graph.nodes[id].children[1],
                    ];
                    let introduction = self.text.begin(format_args!(
                        " {} (not {}) (not {})",
                        self.graph.nodes[id].spelled(),
                        self.graph.nodes[left].spelled(),
                        self.graph.nodes[right].spelled()
                    ))?;
                    self.text.end("and_neg", &[], None)?;
                    let partial = self.text.begin(format_args!(
                        " {} (not {})",
                        self.graph.nodes[id].spelled(),
                        self.graph.nodes[right].spelled()
                    ))?;
                    self.text
                        .end("resolution", &[introduction, self.truths[&left]], None)?;
                    let proof = self.text.unit(
                        self.graph.nodes[id].spelled(),
                        "resolution",
                        &[partial, self.truths[&right]],
                        None,
                    )?;
                    self.truths.insert(id, proof);
                }
                TruthWork::Lift {
                    root,
                    leaf,
                    parents,
                } => {
                    let lifted = self.lift_or(root, leaf, &parents)?;
                    let proof = self.text.unit(
                        self.graph.nodes[root].spelled(),
                        "resolution",
                        &[self.truths[&leaf], lifted],
                        None,
                    )?;
                    self.truths.insert(root, proof);
                }
            }
        }
        Ok(self.truths[&goal])
    }

    fn signed_atom(&mut self, mut id: Id) -> Result<(Id, bool), ClosedDefinitionRefusal> {
        let mut positive = true;
        while matches!(self.graph.nodes[id].original, E::Not { .. }) {
            reserve_work::<Work>(&[], &mut self.edges, 1)?;
            positive = !positive;
            id = self.graph.nodes[id].children[0];
        }
        Ok((id, positive))
    }

    fn or_leaves(&mut self, root: Id) -> Result<OrForest, ClosedDefinitionRefusal> {
        let mut pending = vec![root];
        let mut parents = HashMap::new();
        let mut seen = HashSet::new();
        let mut leaves = Vec::new();
        while let Some(id) = pending.pop() {
            if !seen.insert(id) {
                continue;
            }
            if seen.len() > MAX_NODES {
                return Err(ClosedDefinitionRefusal::Budget("Boolean nodes"));
            }
            if matches!(self.graph.nodes[id].original, E::Or { .. }) {
                reserve_work(
                    &pending,
                    &mut self.edges,
                    self.graph.nodes[id].children.len(),
                )?;
                for (index, child) in self.graph.nodes[id].children.iter().enumerate().rev() {
                    parents.entry(*child).or_insert((id, index));
                    pending.push(*child);
                }
            } else {
                leaves.push(id);
            }
        }
        Ok(OrForest { parents, leaves })
    }

    fn lift_or(
        &mut self,
        root: Id,
        leaf: Id,
        parents: &HashMap<Id, (Id, usize)>,
    ) -> Result<Id, ClosedDefinitionRefusal> {
        let mut current = leaf;
        let mut lifted = None;
        while current != root {
            reserve_work::<Work>(&[], &mut self.edges, 1)?;
            let &(parent, index) = parents
                .get(&current)
                .ok_or(ClosedDefinitionRefusal::Malformed("OR ancestor path"))?;
            let immediate = self.text.begin(format_args!(
                " {} (not {})",
                self.graph.nodes[parent].spelled(),
                self.graph.nodes[current].spelled()
            ))?;
            self.text.end("or_neg", &[], Some(index))?;
            let proof = if let Some(earlier) = lifted {
                let proof = self.text.begin(format_args!(
                    " {} (not {})",
                    self.graph.nodes[parent].spelled(),
                    self.graph.nodes[leaf].spelled()
                ))?;
                self.text.end("resolution", &[earlier, immediate], None)?;
                proof
            } else {
                immediate
            };
            lifted = Some(proof);
            current = parent;
        }
        lifted.ok_or(ClosedDefinitionRefusal::Malformed("empty OR ancestor path"))
    }
}

fn reserve_visits(visits: &mut usize, additional: usize) -> Result<(), ClosedDefinitionRefusal> {
    *visits = visits
        .checked_add(additional)
        .filter(|n| *n <= MAX_NODES)
        .ok_or(ClosedDefinitionRefusal::Budget("equality visits"))?;
    Ok(())
}

fn reserve_work<T>(
    pending: &[T],
    edges: &mut usize,
    additional: usize,
) -> Result<(), ClosedDefinitionRefusal> {
    *edges = edges
        .checked_add(additional)
        .filter(|n| *n <= MAX_EDGES)
        .ok_or(ClosedDefinitionRefusal::Budget("equality work edges"))?;
    pending
        .len()
        .checked_add(additional)
        .filter(|n| *n <= MAX_EDGES)
        .map(|_| ())
        .ok_or(ClosedDefinitionRefusal::Budget("pending equality work"))
}

/// Return bounded UNTRUSTED proof text, or leave this exact query to its
/// existing producer. No original assertion, premise or declaration is changed.
pub(crate) fn compose(
    obligation: &ProofObligation,
) -> Result<ClosedDefinitionCandidate, ClosedDefinitionRefusal> {
    compose_candidate(obligation, false)
}

/// Test-only original-query candidate, never production proof authority.
#[cfg(test)]
pub(crate) fn compose_modular_candidate(
    obligation: &ProofObligation,
) -> Result<ClosedDefinitionCandidate, ClosedDefinitionRefusal> {
    compose_candidate(obligation, true)
}

fn compose_candidate(
    obligation: &ProofObligation,
    modular_candidate: bool,
) -> Result<ClosedDefinitionCandidate, ClosedDefinitionRefusal> {
    #[cfg(not(test))]
    let _ = modular_candidate;
    // Unused declarations still participate in freshness. Bound that work
    // before traversing or allocating the candidate graph, using existing caps.
    if obligation.preconditions.len() > MAX_NODES
        || obligation
            .inputs
            .len()
            .checked_add(obligation.fp_inputs.len())
            .is_none_or(|n| n > MAX_NODES)
    {
        return Err(ClosedDefinitionRefusal::Budget("original inventory"));
    }
    obligation
        .inputs
        .iter()
        .map(|(name, _)| name)
        .chain(obligation.fp_inputs.iter().map(|(name, _, _)| name))
        .try_fold(0usize, |bytes, name| {
            bytes
                .checked_add(name.len())
                .filter(|n| *n <= MAX_SCRIPT_BYTES)
        })
        .ok_or(ClosedDefinitionRefusal::Budget("declaration payload"))?;
    // The canonical connector envelope is balanced; shallow premise count is
    // not expression depth. Its minimum depth includes final Not/Eq/operand.
    // Borrowed component and complete owned-formula preflight below still
    // enforce the SAME actual longest-path/node/edge/output caps.
    let leaf_count = obligation.preconditions.len() + 1;
    let connector_height = leaf_count.next_power_of_two().ilog2() as usize;
    if connector_height + 3 > MAX_DEPTH {
        return Err(ClosedDefinitionRefusal::Budget("expression depth"));
    }
    // Preflight borrowed roots before cloning: UF arguments are owned trees,
    // unlike ordinary Arc children. Even an unsupported root must not trigger
    // deep recursive cloning before the ordinary shape refusal. The component
    // work shares the existing aggregate shape budgets; the full owned formula
    // still receives the normal independent preflight below.
    let mut component_nodes = 0usize;
    let mut component_edges = 0usize;
    let mut component_payload = 0usize;
    for root in std::iter::once(&obligation.trust_ir_expr)
        .chain(std::iter::once(&obligation.aarch64_expr))
        .chain(&obligation.preconditions)
    {
        let bounded = preflight(root)?;
        component_nodes = component_nodes
            .checked_add(bounded.order.len())
            .filter(|n| *n <= MAX_NODES)
            .ok_or(ClosedDefinitionRefusal::Budget("original component nodes"))?;
        component_edges = component_edges
            .checked_add(bounded.edges)
            .filter(|n| *n <= MAX_EDGES)
            .ok_or(ClosedDefinitionRefusal::Budget("original component edges"))?;
        // Like node/edge work, the complete borrowed-component payload is
        // admitted BEFORE any owned UF name/argument clone. Per-root checks
        // alone let wide shallow inventories allocate beyond the same cap.
        component_payload = component_payload
            .checked_add(bounded.payload)
            .filter(|n| *n <= MAX_PAYLOAD_BYTES)
            .ok_or(ClosedDefinitionRefusal::Budget(
                "original component payload",
            ))?;
    }
    let formula = obligation.negated_equivalence();
    let mut graph = Graph::new(&formula)?;
    let mut text = Text {
        text: String::new(),
        next: 0,
        steps: 0,
    };
    let root = graph.pointers[&(&formula as *const E)];
    let original_assumption = text.assume(&formula)?;
    graph.sharing(obligation, &mut text)?;
    let mut true_premises = Vec::new();
    // Traverse ENVELOPE occurrences, not unique graph IDs or every And node.
    // Range length one is an opaque original premise even when it is And.
    // The partition is the canonical constructor's deterministic midpoint.
    let mut pending = vec![(root, original_assumption, 0usize, leaf_count)];
    let mut terminal = None;
    let mut next_leaf = 0usize;
    while let Some((id, unit, start, count)) = pending.pop() {
        if count == 1 {
            if start != next_leaf {
                return Err(ClosedDefinitionRefusal::Malformed("original leaf order"));
            }
            next_leaf += 1;
            if start == obligation.preconditions.len() {
                terminal = Some((id, unit));
            } else {
                // The fresh private constructor supplies this exact occurrence.
                // Never recursively compare a representative to a separate
                // equal DAG: that re-expands shared subtrees. Independent
                // checking validates every actual child projection against the
                // sole complete canonical original assumption.
                graph.definition(id, unit)?;
                true_premises.push((id, unit));
            }
            continue;
        }
        let node = &graph.nodes[id];
        if !matches!(node.original, E::And { .. }) || node.children.len() != 2 {
            return Err(ClosedDefinitionRefusal::Malformed(
                "original premise conjunction",
            ));
        }
        let [left, right] = [node.children[0], node.children[1]];
        let left_unit = text.unit(graph.nodes[left].spelled(), "and", &[unit], Some(0))?;
        let right_unit = text.unit(graph.nodes[right].spelled(), "and", &[unit], Some(1))?;
        let left_count = count / 2;
        pending.push((right, right_unit, start + left_count, count - left_count));
        pending.push((left, left_unit, start, left_count));
    }
    if next_leaf != leaf_count {
        return Err(ClosedDefinitionRefusal::Malformed(
            "original leaf inventory",
        ));
    }
    let (remaining, premise) = terminal.ok_or(ClosedDefinitionRefusal::Malformed(
        "missing original disequality",
    ))?;
    let E::Not { .. } = graph.nodes[remaining].original else {
        return Err(ClosedDefinitionRefusal::Malformed("original disequality"));
    };
    let equality = graph.nodes[remaining].children[0];
    if !matches!(graph.nodes[equality].original, E::Eq { .. }) {
        return Err(ClosedDefinitionRefusal::Malformed("original equivalence"));
    }
    let goal = (
        graph.nodes[equality].children[0],
        graph.nodes[equality].children[1],
    );
    let definitions = graph.definitions.len();
    let boolean_goal = matches!(graph.nodes[goal.0].original, E::BoolConst(true))
        && graph.nodes[goal.1].sort == SmtSort::Bool
        && goal.0 != goal.1;
    let mut order = Vec::new();
    graph.acyclic(Some(&mut order))?;
    let mut visits = 0usize;
    let mut edges = 0usize;
    graph.prepare_literals(&order, &mut visits, &mut edges)?;
    let (keys, key_edges) = if boolean_goal {
        reserve_visits(&mut visits, order.len())?;
        graph.canonical_keys(&order)?
    } else {
        (vec![], 0)
    };
    reserve_work::<Id>(&[], &mut edges, key_edges)?;
    let mut known_true = HashMap::new();
    if boolean_goal {
        for &(node, proof) in &true_premises {
            known_true.entry(keys[node]).or_insert((node, proof));
        }
    }
    let mut composer = Composer {
        graph,
        text,
        equalities: HashMap::new(),
        literal_equalities: HashMap::new(),
        keys,
        known_true,
        truths: HashMap::new(),
        root_facts: None,
        selected_ites: HashMap::new(),
        #[cfg(test)]
        modular_candidate,
        // Literal/key selection and actual proof derivation share work caps.
        visits,
        edges,
    };
    let target = &composer.graph.nodes[goal.1];
    let guarded_root = boolean_goal
        && matches!(target.original, E::Or { .. })
        && matches!(
            composer.graph.nodes[target.children[0]].original,
            E::Not { .. }
        )
        && matches!(
            composer.graph.nodes[target.children[1]].original,
            E::Eq { .. }
        );
    if guarded_root {
        let facts =
            composer.root_boolean_facts(goal.0, goal.1, remaining, premise, &true_premises)?;
        composer.root_facts = Some(facts);
    } else if boolean_goal {
        composer.root_facts = Some(composer.original_boolean_facts(&true_premises)?);
    }
    let equal = if boolean_goal {
        let truth = composer.truth(goal.1, goal.0)?;
        let simplify = composer.text.equality(
            composer.graph.nodes[goal.1].spelled(),
            composer.graph.nodes[equality].spelled(),
            "equiv_simplify",
            &[],
        )?;
        composer.transport(goal.1, equality, truth, simplify)?
    } else {
        composer.equality(goal)?
    };
    composer.text.begin(format_args!(""))?;
    composer.text.end("resolution", &[premise, equal], None)?;
    Ok(ClosedDefinitionCandidate {
        text: composer.text.text,
        premises: obligation.preconditions.len(),
        definitions,
        steps: composer.text.steps,
    })
}
