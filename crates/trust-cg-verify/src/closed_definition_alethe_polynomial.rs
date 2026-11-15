// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Bounded UNTRUSTED modular-affine candidate steps over original terms.
//! Keys only select a derivation. Original atom correspondences must first be
//! proved, and the complete original problem still needs independent replay.

use super::*;

#[cfg(test)]
#[path = "closed_definition_alethe_polynomial_tests.rs"]
mod tests;

// A deliberately small producer fragment, not a larger verifier/checker cap.
const MAX_SHELL_NODES: usize = 16;
const MAX_SHELL_DEPTH: usize = 4;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct PolynomialKey {
    width: u32,
    constant: u64,
    terms: Vec<(Id, u64)>,
}

impl PolynomialKey {
    fn constant(width: u32, value: u64) -> Self {
        Self {
            width,
            constant: value & mask(width),
            terms: vec![],
        }
    }

    fn add_scaled(&mut self, other: &Self, scale: u64) {
        let m = mask(self.width);
        self.constant = self
            .constant
            .wrapping_add(other.constant.wrapping_mul(scale))
            & m;
        for &(atom, coefficient) in &other.terms {
            match self.terms.binary_search_by_key(&atom, |(id, _)| *id) {
                Ok(index) => {
                    self.terms[index].1 = self.terms[index]
                        .1
                        .wrapping_add(coefficient.wrapping_mul(scale))
                        & m
                }
                Err(index) => self
                    .terms
                    .insert(index, (atom, coefficient.wrapping_mul(scale) & m)),
            }
        }
        self.terms.retain(|(_, coefficient)| *coefficient != 0);
    }
}

// Inspection surface for construction/resource controls, not a compiler API.
#[cfg(test)]
pub(super) struct PolynomialShape {
    pub(super) key: PolynomialKey,
    /// Bounded selection work; callers incorporating keys charge these counts.
    pub(super) visits: usize,
    pub(super) edges: usize,
}

struct Shell {
    root: Id,
    key: PolynomialKey,
    order: Vec<Id>,
    atoms: Vec<(Id, Id)>,
}

fn mask(width: u32) -> u64 {
    if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

fn width(graph: &Graph<'_>, id: Id) -> Option<u32> {
    match &graph.nodes.get(id)?.sort {
        SmtSort::BitVec(width @ 1..=64) => Some(*width),
        _ => None,
    }
}

pub(super) fn affine_operator(node: &E) -> bool {
    matches!(
        node,
        E::BvAdd { .. } | E::BvSub { .. } | E::BvMul { .. } | E::BvNeg { .. }
    )
}

/// Exact original Var/nullary-UF atoms only. Products of symbolic polynomials
/// never enter the checker: multiplication requires one constant polynomial.
fn shell(
    graph: &Graph<'_>,
    root: Id,
    atom_key: &impl Fn(Id) -> Option<Id>,
    visits: &mut usize,
    edges: &mut usize,
) -> Result<Option<Shell>, ClosedDefinitionRefusal> {
    let Some(bits) = width(graph, root) else {
        return Ok(None);
    };
    let mut pending = vec![(root, 1usize, false)];
    let mut values = HashMap::<Id, PolynomialKey>::new();
    // Exact subtree heights bound expanded checker traversal even when an
    // already-normalized shared node is revisited at a deeper occurrence.
    // Each entry shares its node's already charged visit and fragment limit.
    let mut heights = HashMap::<Id, usize>::new();
    let mut order = Vec::new();
    let mut atoms = Vec::new();
    while let Some((id, depth, ready)) = pending.pop() {
        if depth > MAX_SHELL_DEPTH {
            return Ok(None);
        }
        if let Some(height) = heights.get(&id) {
            if depth + height - 1 > MAX_SHELL_DEPTH {
                return Ok(None);
            }
            continue;
        }
        if !ready {
            reserve_visits(visits, 1)?;
            if order.len() + pending.len() + 1 > MAX_SHELL_NODES {
                return Ok(None);
            }
            let node = &graph.nodes[id];
            if width(graph, id) != Some(bits) {
                return Ok(None);
            }
            match node.original {
                E::Var { .. } => {
                    let Some(key) = atom_key(id) else {
                        return Ok(None);
                    };
                    atoms.push((id, key));
                    values.insert(
                        id,
                        PolynomialKey {
                            width: bits,
                            constant: 0,
                            terms: vec![(key, 1)],
                        },
                    );
                    heights.insert(id, 1);
                    order.push(id);
                    continue;
                }
                E::UF { args, .. } if args.is_empty() => {
                    let Some(key) = atom_key(id) else {
                        return Ok(None);
                    };
                    atoms.push((id, key));
                    values.insert(
                        id,
                        PolynomialKey {
                            width: bits,
                            constant: 0,
                            terms: vec![(key, 1)],
                        },
                    );
                    heights.insert(id, 1);
                    order.push(id);
                    continue;
                }
                E::BvConst { value, width } if *width == bits && *value & !mask(bits) == 0 => {
                    values.insert(id, PolynomialKey::constant(bits, *value));
                    heights.insert(id, 1);
                    order.push(id);
                    continue;
                }
                _ if affine_operator(node.original) => {}
                _ => return Ok(None),
            }
            reserve_work(&pending, edges, node.children.len() + 1)?;
            pending.push((id, depth, true));
            pending.extend(
                node.children
                    .iter()
                    .rev()
                    .map(|child| (*child, depth + 1, false)),
            );
        } else {
            let node = &graph.nodes[id];
            let height = 1 + node
                .children
                .iter()
                .map(|child| heights[child])
                .max()
                .unwrap_or(0);
            if depth + height - 1 > MAX_SHELL_DEPTH {
                return Ok(None);
            }
            let mut value = PolynomialKey::constant(bits, 0);
            match (node.original, node.children.as_slice()) {
                (E::BvAdd { .. }, [a, b]) => {
                    value.add_scaled(&values[a], 1);
                    value.add_scaled(&values[b], 1);
                }
                (E::BvSub { .. }, [a, b]) => {
                    value.add_scaled(&values[a], 1);
                    value.add_scaled(&values[b], u64::MAX);
                }
                (E::BvNeg { .. }, [a]) => value.add_scaled(&values[a], u64::MAX),
                (E::BvMul { .. }, [a, b]) if values[a].terms.is_empty() => {
                    value.add_scaled(&values[b], values[a].constant);
                }
                (E::BvMul { .. }, [a, b]) if values[b].terms.is_empty() => {
                    value.add_scaled(&values[a], values[b].constant);
                }
                _ => return Ok(None),
            }
            values.insert(id, value);
            heights.insert(id, height);
            order.push(id);
        }
    }
    Ok(Some(Shell {
        root,
        key: values.remove(&root).unwrap(),
        order,
        atoms,
    }))
}

/// Metadata ONLY. Equal keys never authorize a polynomial or atom equality.
#[cfg(test)]
pub(super) fn polynomial_key(
    graph: &Graph<'_>,
    node: Id,
    atom_key: impl Fn(Id) -> Option<Id>,
) -> Option<PolynomialShape> {
    let (mut visits, mut edges) = (0, 0);
    let shell = shell(graph, node, &atom_key, &mut visits, &mut edges).ok()??;
    Some(PolynomialShape {
        key: shell.key,
        visits,
        edges,
    })
}

/// Fresh calls into the equality engine may invoke this fragment again. Bound
/// the ENTIRE actual atom dependency closure first, not merely its affine
/// shell, so acyclic but long defining-equation histories cannot recurse on the
/// Rust stack. Already proved atom pairs need no further dependency work.
fn bounded_atom_dependencies(
    graph: &Graph<'_>,
    roots: Pair,
    visits: &mut usize,
    edges: &mut usize,
) -> Result<bool, ClosedDefinitionRefusal> {
    let mut pending = vec![(roots.0, 1usize), (roots.1, 1usize)];
    let mut depths = HashMap::<Id, usize>::new();
    while let Some((id, depth)) = pending.pop() {
        if depth > MAX_SHELL_DEPTH {
            return Ok(false);
        }
        if depths.get(&id).is_some_and(|old| *old >= depth) {
            continue;
        }
        reserve_visits(visits, 1)?;
        depths.insert(id, depth);
        if let Some(definition) = graph.definitions.get(&id) {
            reserve_work(&pending, edges, 1)?;
            pending.push((definition.rhs, depth + 1));
        } else {
            let children = &graph.nodes[id].children;
            reserve_work(&pending, edges, children.len())?;
            pending.extend(children.iter().map(|child| (*child, depth + 1)));
        }
    }
    Ok(true)
}

impl Composer<'_> {
    fn polynomial_shell(&mut self, node: Id) -> Result<Option<Shell>, ClosedDefinitionRefusal> {
        let keys = &self.keys;
        shell(
            &self.graph,
            node,
            &|id| Some(keys.get(id).copied().unwrap_or(id)),
            &mut self.visits,
            &mut self.edges,
        )
    }

    /// Rewrite only a small proof term, never the original query. Every changed
    /// original atom uses the existing equality engine; all other steps are
    /// original-operator congruences. Acyclic definitions and strict child
    /// dependencies prevent re-entering the current outer operator equality.
    fn align_polynomial_shell(
        &mut self,
        source: &Shell,
        target_atoms: &[(Id, Id)],
    ) -> Result<(E, Id), ClosedDefinitionRefusal> {
        let mut rewritten = HashMap::<Id, (E, Id)>::new();
        for &id in &source.order {
            reserve_visits(&mut self.visits, 1)?;
            let original = self.graph.nodes[id].spelled().clone();
            if let Some(&(_, key)) = source.atoms.iter().find(|(atom, _)| *atom == id) {
                let target = target_atoms
                    .iter()
                    .find(|(atom, k)| *atom == id && *k == key)
                    .or_else(|| target_atoms.iter().find(|(_, k)| *k == key))
                    .map_or(id, |(atom, _)| *atom);
                if id != target
                    && !self.equalities.contains_key(&(id, target))
                    && !self.equalities.contains_key(&(target, id))
                    && !bounded_atom_dependencies(
                        &self.graph,
                        (id, target),
                        &mut self.visits,
                        &mut self.edges,
                    )?
                {
                    return Err(ClosedDefinitionRefusal::Unsupported(
                        "polynomial atom dependency fragment",
                    ));
                }
                let proof = self.equality((id, target))?;
                rewritten.insert(id, (self.graph.nodes[target].spelled().clone(), proof));
            } else if self.graph.nodes[id].children.is_empty() {
                let proof = self.text.equality(&original, &original, "refl", &[])?;
                rewritten.insert(id, (original, proof));
            } else {
                let node = &self.graph.nodes[id];
                reserve_work::<Id>(&[], &mut self.edges, node.children.len() * 2 + 1)?;
                let mut position = 0;
                let view = node
                    .original
                    .try_map_children::<Infallible>(&mut |_| {
                        let child = node.children[position];
                        position += 1;
                        Ok(Arc::new(rewritten[&child].0.clone()))
                    })
                    .unwrap_or_else(|never| match never {});
                let premises: Vec<_> = node
                    .children
                    .iter()
                    .map(|child| rewritten[child].1)
                    .collect();
                let proof = self.text.equality(&original, &view, "cong", &premises)?;
                rewritten.insert(id, (view, proof));
            }
        }
        Ok(rewritten.remove(&source.root).unwrap())
    }

    /// Modular BV equality candidate, not an integer/no-wrap assertion.
    /// Called AFTER original defining equations have been unfolded.
    pub(super) fn polynomial_equality(
        &mut self,
        pair: Pair,
    ) -> Result<Option<Id>, ClosedDefinitionRefusal> {
        if self.graph.definitions.contains_key(&pair.0)
            || self.graph.definitions.contains_key(&pair.1)
            || width(&self.graph, pair.0).is_none()
            || width(&self.graph, pair.0) != width(&self.graph, pair.1)
            || !(affine_operator(self.graph.nodes[pair.0].original)
                || affine_operator(self.graph.nodes[pair.1].original))
        {
            return Ok(None);
        }
        let Some(left) = self.polynomial_shell(pair.0)? else {
            return Ok(None);
        };
        let Some(right) = self.polynomial_shell(pair.1)? else {
            return Ok(None);
        };
        if left.key != right.key {
            return Ok(None);
        }
        let (aligned, congruence) = self.align_polynomial_shell(&left, &right.atoms)?;
        reserve_visits(&mut self.visits, 1)?;
        reserve_work::<Id>(&[], &mut self.edges, 3)?;
        let lhs = self.graph.nodes[pair.0].spelled();
        let rhs = self.graph.nodes[pair.1].spelled();
        let polynomial = self.text.equality(&aligned, rhs, "poly_simp", &[])?;
        Ok(Some(self.text.equality(
            lhs,
            rhs,
            "trans",
            &[congruence, polynomial],
        )?))
    }

    /// Predicate equality via the checked modular relation schema. The two
    /// multiplier coefficients are literal ONE (odd even at width one).
    /// No even-factor cancellation or inequality transformation is attempted.
    pub(super) fn polynomial_predicate_equality(
        &mut self,
        pair: Pair,
    ) -> Result<Option<Id>, ClosedDefinitionRefusal> {
        if !matches!(self.graph.nodes[pair.0].original, E::Eq { .. })
            || !matches!(self.graph.nodes[pair.1].original, E::Eq { .. })
        {
            return Ok(None);
        }
        let [a, b] = self.graph.nodes[pair.0].children.as_slice() else {
            return Ok(None);
        };
        let [c, d] = self.graph.nodes[pair.1].children.as_slice() else {
            return Ok(None);
        };
        let [a, b, c, d] = [*a, *b, *c, *d];
        let Some(bits) = width(&self.graph, a) else {
            return Ok(None);
        };
        if [b, c, d]
            .iter()
            .any(|id| width(&self.graph, *id) != Some(bits))
        {
            return Ok(None);
        }
        let mut shells = Vec::new();
        for id in [a, b, c, d] {
            let Some(shell) = self.polynomial_shell(id)? else {
                return Ok(None);
            };
            shells.push(shell);
        }
        let mut left = shells[0].key.clone();
        left.add_scaled(&shells[1].key, u64::MAX);
        let mut right = shells[2].key.clone();
        right.add_scaled(&shells[3].key, u64::MAX);
        // Retain directed differences; no orientation or coefficient is
        // discarded by candidate selection.
        if left != right {
            return Ok(None);
        }
        let target_atoms: Vec<_> = shells[2]
            .atoms
            .iter()
            .chain(&shells[3].atoms)
            .copied()
            .collect();
        let (a_view, a_proof) = self.align_polynomial_shell(&shells[0], &target_atoms)?;
        let (b_view, b_proof) = self.align_polynomial_shell(&shells[1], &target_atoms)?;
        reserve_visits(&mut self.visits, 2)?;
        reserve_work::<Id>(&[], &mut self.edges, 12)?;
        let actual_left = self.graph.nodes[pair.0].spelled();
        let actual_right = self.graph.nodes[pair.1].spelled();
        let aligned = a_view.clone().eq_expr(b_view.clone());
        let lifted = self
            .text
            .equality(actual_left, &aligned, "cong", &[a_proof, b_proof])?;
        let one = E::bv_const(1, bits);
        let left_difference = a_view.bvsub(b_view);
        let right_difference = self.graph.nodes[c]
            .spelled()
            .clone()
            .bvsub(self.graph.nodes[d].spelled().clone());
        let polynomial = self.text.equality(
            &one.clone().bvmul(left_difference),
            &one.bvmul(right_difference),
            "poly_simp",
            &[],
        )?;
        let relation =
            self.text
                .equality(&aligned, actual_right, "poly_simp_rel", &[polynomial])?;
        Ok(Some(self.text.equality(
            actual_left,
            actual_right,
            "trans",
            &[lifted, relation],
        )?))
    }
}
