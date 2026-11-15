// Copyright 2026 Andrew Yates | Apache-2.0

//! Shared checked conjunct inventory for source-bound whole statements.
//! This is the existing scalar-cell caller decomposition: at most six
//! memory-free conjuncts per part, and each memory-reading conjunct alone.
//! Every original goal is retained in written order within its category;
//! part premises can only be a subset of original premises (a stronger claim),
//! and declarations are exactly their used original inputs. All parts must
//! independently replay under the original request before a consumer grants
//! its complete statement. This grants no solver result or replay capability.

use crate::lowering_proof::ProofObligation;
use crate::smt::SmtExpr as E;
use std::collections::BTreeSet;

/// The part name prefix: the statement's name. A part is
/// `"<statement> -- part k of n"`.
fn part_name(label: &str, k: usize, n: usize) -> String {
    format!("{label} -- part {k} of {n}")
}

/// Preserve the existing integer caller's memory classification. Pointer
/// visitation memoizes immutable shared nodes without changing that domain.
fn reads_memory(term: &E) -> bool {
    let mut pending = vec![term];
    let mut seen = std::collections::HashSet::new();
    while let Some(term) = pending.pop() {
        if !seen.insert(std::ptr::from_ref(term)) {
            continue;
        }
        if matches!(term, E::Select { .. }) {
            return true;
        }
        pending.extend(children(term));
    }
    false
}

fn children(term: &E) -> Vec<&E> {
    use E::*;
    match term {
        Var { .. } | BvConst { .. } | BoolConst(_) => Vec::new(),
        Not { operand } => vec![operand],
        Extract { operand, .. } | ZeroExtend { operand, .. } => vec![operand],
        BvAdd { lhs, rhs, .. }
        | BvSub { lhs, rhs, .. }
        | BvAnd { lhs, rhs, .. }
        | BvOr { lhs, rhs, .. }
        | BvXor { lhs, rhs, .. }
        | BvShl { lhs, rhs, .. }
        | BvUle { lhs, rhs, .. }
        | BvUge { lhs, rhs, .. }
        | Eq { lhs, rhs }
        | And { lhs, rhs } => vec![lhs, rhs],
        Concat { hi, lo, .. } => vec![hi, lo],
        Select { array, index } => vec![array, index],
        Store {
            array,
            index,
            value,
        } => vec![array, index, value],
        ConstArray { value, .. } => vec![value],
        UF { args, .. } => args.iter().collect(),
        _ => Vec::new(),
    }
}

/// The statement's conjuncts, in order (its `And` tree flattened).
pub(crate) fn conjuncts_of(term: &E) -> Vec<E> {
    let mut pending = vec![term];
    let mut all = Vec::new();
    while let Some(term) = pending.pop() {
        match term {
            E::And { lhs, rhs } => {
                pending.push(rhs);
                pending.push(lhs);
            }
            other => all.push(other.clone()),
        }
    }
    all
}

/// One part: `conjuncts` under the statement's premises that share a name
/// with them, declaring exactly the inputs it uses.
fn part(statement: &ProofObligation, name: String, conjuncts: Vec<E>) -> ProofObligation {
    let complete = conjuncts
        .into_iter()
        .reduce(|a, b| a.and_expr(b))
        .expect("a part has a conjunct");
    let mut used: BTreeSet<String> = complete.free_vars().into_iter().collect();
    let preconditions: Vec<E> = statement
        .preconditions
        .iter()
        .filter(|premise| premise.free_vars().iter().any(|name| used.contains(name)))
        .cloned()
        .collect();
    for premise in &preconditions {
        used.extend(premise.free_vars());
    }
    ProofObligation {
        name,
        trust_ir_expr: E::bool_const(true),
        aarch64_expr: complete,
        inputs: statement
            .inputs
            .iter()
            .filter(|(name, _)| used.contains(name))
            .cloned()
            .collect(),
        preconditions,
        fp_inputs: Vec::new(),
        category: statement.category,
        machine_side_provenance: statement.machine_side_provenance.clone(),
    }
}

/// Most memory-free conjuncts one part holds. One query of every such
/// conjunct took 18-26 s of the 30 s budget on this host and twice ended
/// with a proof AY could not complete; single conjuncts took 0.1-1 s each.
const MEMORY_FREE_PER_PART: usize = 6;

/// The statement in parts: the memory-free conjuncts in groups of at most
/// [`MEMORY_FREE_PER_PART`], then each memory-reading conjunct alone, in
/// statement order within each group.
pub(crate) fn split_parts(
    statement: &ProofObligation,
    label: &str,
) -> Result<Vec<ProofObligation>, String> {
    let (pure, memory): (Vec<E>, Vec<E>) = conjuncts_of(&statement.aarch64_expr)
        .into_iter()
        .partition(|conjunct| !reads_memory(conjunct));
    let mut groups: Vec<Vec<E>> = pure
        .chunks(MEMORY_FREE_PER_PART)
        .map(<[E]>::to_vec)
        .collect();
    groups.extend(memory.into_iter().map(|conjunct| vec![conjunct]));
    let n = groups.len();
    if n == 0 {
        return Err("no part".into());
    }
    Ok(groups
        .into_iter()
        .enumerate()
        .map(|(k, group)| part(statement, part_name(label, k + 1, n), group))
        .collect())
}

/// Check the exact complete conjunct inventory and original assumption scope.
pub(crate) fn check_parts(
    statement: &ProofObligation,
    parts: &[ProofObligation],
    label: &str,
    opaque_inputs: &[&str],
) -> Result<(), String> {
    if statement.trust_ir_expr != E::bool_const(true) || !statement.fp_inputs.is_empty() {
        return Err("conjunctive replay requires a true-sided integer statement".into());
    }
    let n = parts.len();
    if n == 0 {
        return Err("no part".into());
    }
    let mut pure = Vec::new();
    let mut memory = Vec::new();
    for (k, part) in parts.iter().enumerate() {
        if part.name != part_name(label, k + 1, n)
            || part.category != statement.category
            || part.machine_side_provenance != statement.machine_side_provenance
            || part.trust_ir_expr != E::bool_const(true)
            || !part.fp_inputs.is_empty()
        {
            return Err(format!("part {} is not the statement's", k + 1));
        }
        if !part
            .preconditions
            .iter()
            .all(|premise| statement.preconditions.contains(premise))
        {
            return Err(format!(
                "part {} carries a premise the statement has not",
                k + 1
            ));
        }
        let mut used: BTreeSet<String> = part.aarch64_expr.free_vars().into_iter().collect();
        for premise in &part.preconditions {
            used.extend(premise.free_vars());
        }
        for opaque in opaque_inputs {
            used.remove(*opaque);
        }
        let declared: BTreeSet<String> = part.inputs.iter().map(|(name, _)| name.clone()).collect();
        if used != declared
            || !part
                .inputs
                .iter()
                .all(|input| statement.inputs.contains(input))
        {
            return Err(format!("part {} declares other inputs than it uses", k + 1));
        }
        let conjuncts = conjuncts_of(&part.aarch64_expr);
        if memory.is_empty()
            && conjuncts.len() <= MEMORY_FREE_PER_PART
            && conjuncts.iter().all(|c| !reads_memory(c))
        {
            pure.extend(conjuncts);
        } else if conjuncts.len() == 1 && reads_memory(&conjuncts[0]) {
            memory.extend(conjuncts);
        } else {
            return Err(format!(
                "part {} is neither a memory-free group nor one memory conjunct",
                k + 1
            ));
        }
    }
    let (expected_pure, expected_memory): (Vec<E>, Vec<E>) = conjuncts_of(&statement.aarch64_expr)
        .into_iter()
        .partition(|conjunct| !reads_memory(conjunct));
    if pure != expected_pure || memory != expected_memory {
        return Err("the parts' conjuncts are not the statement's".into());
    }
    Ok(())
}
