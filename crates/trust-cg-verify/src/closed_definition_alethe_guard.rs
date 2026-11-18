// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Root-local, untrusted Boolean proof construction. Signed units come from
//! the exact original refutation/premises or ordinary Boolean tautologies.
//! They never enter unconditional literal or equality selection metadata.

use super::*;

/// A proved signed unit in ONE candidate composition, not a Boolean assignment.
#[derive(Clone, Copy)]
pub(super) struct BooleanFact {
    scope: *const (),
    node: Id,
    positive: bool,
    proof: Id,
}

impl BooleanFact {
    pub(super) fn node(self) -> Id {
        self.node
    }
    pub(super) fn positive(self) -> bool {
        self.positive
    }
    pub(super) fn proof(self) -> Id {
        self.proof
    }
}

/// No public constructor or unchecked insertion. Reverse indexes and units
/// are scoped to the current graph and bounded by the ordinary work caps.
pub(super) struct RootFacts {
    scope: *const (),
    units: HashMap<(Id, bool), BooleanFact>,
    // Only actual Boolean reverse uses allocate rows. Mixed memory/BV graphs
    // do not allocate two empty Vec headers for every non-Boolean node.
    definitions: HashMap<Id, Vec<Id>>,
    parents: HashMap<Id, Vec<Id>>,
}

impl RootFacts {
    pub(super) fn get(&self, node: Id, positive: bool) -> Option<BooleanFact> {
        self.units.get(&(node, positive)).copied()
    }

    fn add(
        &mut self,
        composer: &mut Composer<'_>,
        node: Id,
        positive: bool,
        proof: Id,
        pending: &mut Vec<BooleanFact>,
    ) -> Result<(), ClosedDefinitionRefusal> {
        composer.boolean_node(node)?;
        if self.scope != composer.graph_scope() || proof >= composer.text.next {
            return Err(ClosedDefinitionRefusal::Malformed(
                "foreign Boolean proof scope",
            ));
        }
        if self.units.contains_key(&(node, positive)) {
            return Ok(());
        }
        // This single charge bounds both the memo entry and its worklist visit.
        reserve_visits(&mut composer.visits, 1)?;
        reserve_work(pending, &mut composer.edges, 1)?;
        let fact = BooleanFact {
            scope: self.scope,
            node,
            positive,
            proof,
        };
        self.units.insert((node, positive), fact);
        pending.push(fact);
        Ok(())
    }
}

impl Composer<'_> {
    fn graph_scope(&self) -> *const () {
        self.graph.nodes.as_ptr().cast()
    }

    fn boolean_node(&self, id: Id) -> Result<(), ClosedDefinitionRefusal> {
        let node = self
            .graph
            .nodes
            .get(id)
            .ok_or(ClosedDefinitionRefusal::Malformed("Boolean fact node"))?;
        if node.sort != SmtSort::Bool {
            return Err(ClosedDefinitionRefusal::Malformed("non-Boolean fact"));
        }
        if !node.children.is_empty() && node.spelling.is_none() {
            return Err(ClosedDefinitionRefusal::Malformed(
                "unshared Boolean proof graph",
            ));
        }
        Ok(())
    }

    fn signed_term(&self, id: Id, positive: bool) -> E {
        let term = self.graph.nodes[id].spelled().clone();
        if positive { term } else { term.not_expr() }
    }

    /// Eq(left,right) transports a genuine signed unit in either direction.
    /// Exact rule schemas dictate clause order, including negative units.
    pub(super) fn signed_transport(
        &mut self,
        left: &E,
        right: &E,
        unit: Id,
        equality: Id,
        positive: bool,
        forward: bool,
    ) -> Result<Id, ClosedDefinitionRefusal> {
        reserve_work::<BooleanFact>(&[], &mut self.edges, 3)?;
        let (bridge, rule) = match (positive, forward) {
            (true, true) => (
                self.text.begin(format_args!(" (not {left}) {right}"))?,
                "equiv1",
            ),
            (false, true) => (
                self.text.begin(format_args!(" {left} (not {right})"))?,
                "equiv2",
            ),
            (true, false) => (
                self.text.begin(format_args!(" {left} (not {right})"))?,
                "equiv2",
            ),
            (false, false) => (
                self.text.begin(format_args!(" (not {left}) {right}"))?,
                "equiv1",
            ),
        };
        self.text.end(rule, &[equality], None)?;
        let target = if forward { right } else { left };
        let term = if positive {
            target.clone()
        } else {
            target.clone().not_expr()
        };
        self.text.unit(&term, "resolution", &[unit, bridge], None)
    }

    /// Derive root facts from the actual Not(Eq(true,goal)) unit, with goal
    /// exactly Or(Not(guard),Eq(left,right)). No assumption is introduced.
    pub(super) fn root_boolean_facts(
        &mut self,
        true_id: Id,
        goal: Id,
        terminal: Id,
        terminal_unit: Id,
        original_premises: &[(Id, Id)],
    ) -> Result<RootFacts, ClosedDefinitionRefusal> {
        for id in [true_id, goal, terminal] {
            self.boolean_node(id)?;
        }
        if !matches!(self.graph.nodes[true_id].original, E::BoolConst(true))
            || !matches!(self.graph.nodes[terminal].original, E::Not { .. })
            || terminal_unit >= self.text.next
        {
            return Err(ClosedDefinitionRefusal::Malformed(
                "original guarded disequality",
            ));
        }
        let equation = self.graph.nodes[terminal].children[0];
        if !matches!(self.graph.nodes[equation].original, E::Eq { .. })
            || self.graph.nodes[equation].children.as_slice() != [true_id, goal]
        {
            return Err(ClosedDefinitionRefusal::Malformed(
                "original guarded disequality",
            ));
        }
        let node = &self.graph.nodes[goal];
        if !matches!(node.original, E::Or { .. }) || node.children.len() != 2 {
            return Err(ClosedDefinitionRefusal::Unsupported("guarded Boolean root"));
        }
        let left = node.children[0];
        let right = node.children[1];
        if !matches!(self.graph.nodes[left].original, E::Not { .. })
            || !matches!(self.graph.nodes[right].original, E::Eq { .. })
        {
            return Err(ClosedDefinitionRefusal::Unsupported("guarded Boolean root"));
        }
        let (mut facts, mut pending) = self.original_fact_seeds(original_premises)?;
        reserve_work::<BooleanFact>(&[], &mut self.edges, 9)?;
        let simplify = self.text.equality(
            self.graph.nodes[equation].spelled(),
            self.graph.nodes[goal].spelled(),
            "equiv_simplify",
            &[],
        )?;
        let not_goal = self.signed_term(goal, false);
        let lifted = self.text.equality(
            self.graph.nodes[terminal].spelled(),
            &not_goal,
            "cong",
            &[simplify],
        )?;
        let negated_goal = self.signed_transport(
            &self.graph.nodes[terminal].spelled().clone(),
            &not_goal,
            terminal_unit,
            lifted,
            true,
            true,
        )?;
        facts.add(self, goal, false, negated_goal, &mut pending)?;
        // `not_or` proves EACH actual root child false. The Not child then
        // produces the guard's positive unit through checked double negation.
        for (index, child) in [left, right].into_iter().enumerate() {
            let unit = self.text.unit(
                &self.signed_term(child, false),
                "not_or",
                &[negated_goal],
                Some(index),
            )?;
            facts.add(self, child, false, unit, &mut pending)?;
        }
        self.close_root_facts(&mut facts, pending)?;
        Ok(facts)
    }

    /// Forward Boolean units projected only from the original premises and
    /// literal truth/falsity. No terminal or branch hypothesis is introduced.
    pub(super) fn original_boolean_facts(
        &mut self,
        original_premises: &[(Id, Id)],
    ) -> Result<RootFacts, ClosedDefinitionRefusal> {
        let (mut facts, pending) = self.original_fact_seeds(original_premises)?;
        self.close_root_facts(&mut facts, pending)?;
        Ok(facts)
    }

    fn original_fact_seeds(
        &mut self,
        original_premises: &[(Id, Id)],
    ) -> Result<(RootFacts, Vec<BooleanFact>), ClosedDefinitionRefusal> {
        if original_premises.len() > MAX_NODES {
            return Err(ClosedDefinitionRefusal::Budget("original inventory"));
        }
        for &(id, proof) in original_premises {
            self.boolean_node(id)?;
            if proof >= self.text.next {
                return Err(ClosedDefinitionRefusal::Malformed(
                    "original Boolean premise",
                ));
            }
        }
        reserve_visits(&mut self.visits, self.graph.nodes.len())?;
        let mut facts = RootFacts {
            scope: self.graph_scope(),
            units: HashMap::new(),
            definitions: HashMap::new(),
            parents: HashMap::new(),
        };
        for id in 0..self.graph.nodes.len() {
            if let Some(definition) = self.graph.definitions.get(&id)
                && self.graph.nodes[id].sort == SmtSort::Bool
            {
                reserve_work::<Id>(&[], &mut self.edges, 1)?;
                facts
                    .definitions
                    .entry(definition.rhs)
                    .or_default()
                    .push(id);
            }
            if matches!(
                self.graph.nodes[id].original,
                E::Not { .. } | E::And { .. } | E::Or { .. }
            ) {
                for &child in &self.graph.nodes[id].children {
                    reserve_work::<Id>(&[], &mut self.edges, 1)?;
                    facts.parents.entry(child).or_default().push(id);
                }
            }
        }
        let mut pending = Vec::new();
        for &(id, proof) in original_premises {
            facts.add(self, id, true, proof, &mut pending)?;
        }
        for id in 0..self.graph.nodes.len() {
            if let E::BoolConst(positive) = self.graph.nodes[id].original {
                let positive = *positive;
                let proof = self.text.unit(
                    &self.signed_term(id, positive),
                    if positive { "true" } else { "false" },
                    &[],
                    None,
                )?;
                facts.add(self, id, positive, proof, &mut pending)?;
            }
        }
        Ok((facts, pending))
    }

    /// A positive binary OR plus a proved false child entails the other
    /// child. Clause order remains the exact original child order.
    fn close_positive_or(
        &mut self,
        facts: &mut RootFacts,
        pending: &mut Vec<BooleanFact>,
        id: Id,
    ) -> Result<(), ClosedDefinitionRefusal> {
        let Some(parent) = facts.get(id, true) else {
            return Ok(());
        };
        let [left, right] = [
            self.graph.nodes[id].children[0],
            self.graph.nodes[id].children[1],
        ];
        for (child, other) in [(left, right), (right, left)] {
            if facts.get(other, true).is_some() {
                continue;
            }
            let Some(negative) = facts.get(child, false) else {
                continue;
            };
            reserve_work::<BooleanFact>(&[], &mut self.edges, 2)?;
            let clause = self.text.begin(format_args!(
                " {} {}",
                self.graph.nodes[left].spelled(),
                self.graph.nodes[right].spelled()
            ))?;
            self.text.end("or", &[parent.proof], None)?;
            let proof = self.text.unit(
                self.graph.nodes[other].spelled(),
                "resolution",
                &[clause, negative.proof],
                None,
            )?;
            facts.add(self, other, true, proof, pending)?;
        }
        Ok(())
    }

    fn close_root_facts(
        &mut self,
        facts: &mut RootFacts,
        mut pending: Vec<BooleanFact>,
    ) -> Result<(), ClosedDefinitionRefusal> {
        while let Some(fact) = pending.pop() {
            let id = fact.node;
            if let Some(definition) = self.graph.definitions.get(&id).copied()
                && facts.get(definition.rhs, fact.positive).is_none()
            {
                let proof = self.signed_transport(
                    &self.graph.nodes[id].spelled().clone(),
                    &self.graph.nodes[definition.rhs].spelled().clone(),
                    fact.proof,
                    definition.premise,
                    fact.positive,
                    true,
                )?;
                facts.add(self, definition.rhs, fact.positive, proof, &mut pending)?;
            }
            for index in 0..facts.definitions.get(&id).map_or(0, Vec::len) {
                reserve_work::<BooleanFact>(&[], &mut self.edges, 1)?;
                let lhs = facts.definitions[&id][index];
                if facts.get(lhs, fact.positive).is_some() {
                    continue;
                }
                let definition = self.graph.definitions[&lhs];
                let proof = self.signed_transport(
                    &self.graph.nodes[lhs].spelled().clone(),
                    &self.graph.nodes[id].spelled().clone(),
                    fact.proof,
                    definition.premise,
                    fact.positive,
                    false,
                )?;
                facts.add(self, lhs, fact.positive, proof, &mut pending)?;
            }
            let node = &self.graph.nodes[id];
            if matches!(node.original, E::Not { .. }) {
                let child = node.children[0];
                if facts.get(child, !fact.positive).is_none() {
                    let proof = if fact.positive {
                        fact.proof
                    } else {
                        let from = self.signed_term(id, false);
                        let to = self.signed_term(child, true);
                        let equality = self.text.equality(&from, &to, "not_simplify", &[])?;
                        self.signed_transport(&from, &to, fact.proof, equality, true, true)?
                    };
                    facts.add(self, child, !fact.positive, proof, &mut pending)?;
                }
            } else if matches!(node.original, E::And { .. }) && fact.positive {
                for index in 0..node.children.len() {
                    let child = self.graph.nodes[id].children[index];
                    if facts.get(child, true).is_some() {
                        continue;
                    }
                    reserve_work::<BooleanFact>(&[], &mut self.edges, 1)?;
                    let proof = self.text.unit(
                        self.graph.nodes[child].spelled(),
                        "and",
                        &[fact.proof],
                        Some(index),
                    )?;
                    facts.add(self, child, true, proof, &mut pending)?;
                }
            }
            if matches!(self.graph.nodes[id].original, E::Or { .. }) {
                if fact.positive {
                    self.close_positive_or(facts, &mut pending, id)?;
                } else {
                    for index in 0..self.graph.nodes[id].children.len() {
                        let child = self.graph.nodes[id].children[index];
                        if facts.get(child, false).is_some() {
                            continue;
                        }
                        reserve_work::<BooleanFact>(&[], &mut self.edges, 1)?;
                        let proof = self.text.unit(
                            &self.signed_term(child, false),
                            "not_or",
                            &[fact.proof],
                            Some(index),
                        )?;
                        facts.add(self, child, false, proof, &mut pending)?;
                    }
                }
            }
            for index in 0..facts.parents.get(&id).map_or(0, Vec::len) {
                reserve_work::<BooleanFact>(&[], &mut self.edges, 1)?;
                let parent = facts.parents[&id][index];
                let node = &self.graph.nodes[parent];
                if matches!(node.original, E::Not { .. }) {
                    let positive = !fact.positive;
                    if facts.get(parent, positive).is_some() {
                        continue;
                    }
                    let proof = if positive {
                        fact.proof
                    } else {
                        let double_negative = self.signed_term(parent, false);
                        let child = self.signed_term(id, true);
                        let equality =
                            self.text
                                .equality(&double_negative, &child, "not_simplify", &[])?;
                        self.signed_transport(
                            &double_negative,
                            &child,
                            fact.proof,
                            equality,
                            true,
                            false,
                        )?
                    };
                    facts.add(self, parent, positive, proof, &mut pending)?;
                } else if matches!(node.original, E::Or { .. }) {
                    if fact.positive {
                        if facts.get(parent, true).is_some() {
                            continue;
                        }
                        let position = node.children.iter().position(|child| *child == id).unwrap();
                        reserve_work::<BooleanFact>(&[], &mut self.edges, 2)?;
                        let clause = self.text.begin(format_args!(
                            " {} (not {})",
                            node.spelled(),
                            self.graph.nodes[id].spelled()
                        ))?;
                        self.text.end("or_neg", &[], Some(position))?;
                        let proof = self.text.unit(
                            node.spelled(),
                            "resolution",
                            &[fact.proof, clause],
                            None,
                        )?;
                        facts.add(self, parent, true, proof, &mut pending)?;
                    } else {
                        self.close_positive_or(facts, &mut pending, parent)?;
                    }
                } else if !fact.positive {
                    if facts.get(parent, false).is_some() {
                        continue;
                    }
                    let position = node.children.iter().position(|child| *child == id).unwrap();
                    reserve_work::<BooleanFact>(&[], &mut self.edges, 2)?;
                    let clause = self.text.begin(format_args!(
                        " (not {}) {}",
                        node.spelled(),
                        self.graph.nodes[id].spelled(),
                    ))?;
                    self.text.end("and_pos", &[], Some(position))?;
                    let proof = self.text.unit(
                        &self.signed_term(parent, false),
                        "resolution",
                        &[fact.proof, clause],
                        None,
                    )?;
                    facts.add(self, parent, false, proof, &mut pending)?;
                } else if facts.get(parent, true).is_none()
                    && node
                        .children
                        .iter()
                        .all(|child| facts.get(*child, true).is_some())
                {
                    let [left, right] = [node.children[0], node.children[1]];
                    let units = [
                        facts.get(left, true).unwrap().proof,
                        facts.get(right, true).unwrap().proof,
                    ];
                    reserve_work::<BooleanFact>(&[], &mut self.edges, 4)?;
                    let clause = self.text.begin(format_args!(
                        " {} (not {}) (not {})",
                        node.spelled(),
                        self.graph.nodes[left].spelled(),
                        self.graph.nodes[right].spelled()
                    ))?;
                    self.text.end("and_neg", &[], None)?;
                    let partial = self.text.begin(format_args!(
                        " {} (not {})",
                        node.spelled(),
                        self.graph.nodes[right].spelled()
                    ))?;
                    self.text.end("resolution", &[clause, units[0]], None)?;
                    let proof =
                        self.text
                            .unit(node.spelled(), "resolution", &[partial, units[1]], None)?;
                    facts.add(self, parent, true, proof, &mut pending)?;
                }
            }
        }
        Ok(())
    }

    /// A generic ITE-to-selected-branch equality, proved through Boolean ITE
    /// equalities. Neither condition values nor branch facts change literals.
    pub(super) fn ite_branch_equality(
        &mut self,
        ite: Id,
        fact: BooleanFact,
    ) -> Result<(Id, Id), ClosedDefinitionRefusal> {
        let node = self
            .graph
            .nodes
            .get(ite)
            .ok_or(ClosedDefinitionRefusal::Malformed("ITE node"))?;
        if !matches!(node.original, E::Ite { .. }) || node.children.len() != 3 {
            return Err(ClosedDefinitionRefusal::Unsupported("ITE branch equality"));
        }
        let [condition, then_branch, else_branch] =
            [node.children[0], node.children[1], node.children[2]];
        if fact.scope != self.graph_scope()
            || fact.node() != condition
            || fact.proof >= self.text.next
        {
            return Err(ClosedDefinitionRefusal::Malformed("ITE condition fact"));
        }
        self.boolean_node(condition)?;
        if node.spelling.is_none() {
            return Err(ClosedDefinitionRefusal::Malformed(
                "unshared Boolean proof graph",
            ));
        }
        reserve_visits(&mut self.visits, 1)?;
        reserve_work::<BooleanFact>(&[], &mut self.edges, 10)?;
        let term = node.spelled().clone();
        let predicate = self.graph.nodes[condition].spelled().clone();
        let then_equality = term
            .clone()
            .eq_expr(self.graph.nodes[then_branch].spelled().clone());
        let else_equality = term
            .clone()
            .eq_expr(self.graph.nodes[else_branch].spelled().clone());
        let root = term.clone().eq_expr(term);
        let selected = E::ite(
            predicate.clone(),
            then_equality.clone(),
            else_equality.clone(),
        );
        let introduced = root.clone().and_expr(selected.clone());
        let reflexive = self.text.unit(&root, "refl", &[], None)?;
        let intro = self.text.equality(&root, &introduced, "ite_intro", &[])?;
        let conjunction =
            self.signed_transport(&root, &introduced, reflexive, intro, true, true)?;
        let boolean_ite = self.text.unit(&selected, "and", &[conjunction], Some(1))?;
        let (branch, equality, rule) = if fact.positive() {
            (then_branch, then_equality, "ite2")
        } else {
            (else_branch, else_equality, "ite1")
        };
        let clause = if fact.positive() {
            self.text
                .begin(format_args!(" (not {predicate}) {equality}"))?
        } else {
            self.text.begin(format_args!(" {predicate} {equality}"))?
        };
        self.text.end(rule, &[boolean_ite], None)?;
        let proof = self
            .text
            .unit(&equality, "resolution", &[fact.proof, clause], None)?;
        Ok((branch, proof))
    }
}
