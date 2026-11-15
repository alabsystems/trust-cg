// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Bounded QF Bool/BV/array SMT-LIB PRINT VIEW, never normalized semantics.
//!
//! The original AST, declaration inventory and query identity stay unchanged.
//! Existing DAG rewriting and Display supply every node's spelling; aliases
//! exist only in nested, dependency-level `let` bindings. No alias is a new
//! global input. Independent replay against the ORIGINAL raw script remains
//! mandatory outside this module; the text/counters below supply no authority.
//! Pointer identity preserves existing sharing without recursive hash/equality.
//! This initial profile declines binders, FP and implicit-symbol operations.

use crate::smt::{SmtExpr, SmtSort};
use std::collections::HashMap;
use std::fmt::{self, Write};

#[cfg(test)]
#[path = "smt_raw_print_tests.rs"]
mod tests;

pub(crate) const MAX_NODES: usize = 32_768;
pub(crate) const MAX_EDGES: usize = 131_072;
pub(crate) const MAX_DEPTH: usize = 256;
const MAX_ARITY: usize = 64;
const MAX_SYMBOL_BYTES: usize = 4096;
pub(crate) const MAX_PAYLOAD_BYTES: usize = 1_048_576;
pub(crate) const MAX_SCRIPT_BYTES: usize = 4_194_304;
pub(crate) const MAX_OUTPUT_BYTES: usize = 4_194_304;
const MAX_SORT_DEPTH: usize = 16;
const MAX_SORT_NODES: usize = 64;
const MAX_BIT_WIDTH: u32 = 256;
pub(crate) const MAX_PREFIX_ATTEMPTS: usize = 64;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum CompactPrintRefusal {
    #[error("compact raw print resource limit: {0}")]
    Budget(&'static str),
    #[error("compact raw print unsupported: {0}")]
    Unsupported(&'static str),
    #[error("compact raw print malformed sort: {0}")]
    Sort(&'static str),
}

#[derive(Debug)]
pub(crate) struct CompactFormula {
    pub(crate) text: String,
    pub(crate) distinct_nodes: usize,
    pub(crate) edges: usize,
    pub(crate) bindings: usize,
    pub(crate) output_bytes: usize,
    pub(crate) levels: usize,
}

/// Resource/shape inventory shared with untrusted proof production. It carries
/// no semantic admission: callers must also validate shallow typed-child views
/// with `checked_sort` and independently replay any resulting proof.
pub(crate) struct Preflight<'a> {
    pub(crate) order: Vec<&'a SmtExpr>,
    pub(crate) edges: usize,
    /// Stored shallow payload charged by the existing bounded traversal.
    pub(crate) payload: usize,
}

fn width(width: u32) -> Result<(), CompactPrintRefusal> {
    if (1..=MAX_BIT_WIDTH).contains(&width) {
        Ok(())
    } else {
        Err(CompactPrintRefusal::Sort("bitvector width"))
    }
}

fn sort_shape(sort: &SmtSort) -> Result<usize, CompactPrintRefusal> {
    let mut pending = vec![(sort, 1)];
    let mut nodes = 0usize;
    while let Some((sort, depth)) = pending.pop() {
        nodes += 1;
        if nodes > MAX_SORT_NODES || depth > MAX_SORT_DEPTH {
            return Err(CompactPrintRefusal::Budget("sort shape"));
        }
        match sort {
            SmtSort::Bool => {}
            SmtSort::BitVec(bits) => width(*bits)?,
            SmtSort::Array(index, element) => {
                pending.push((element, depth + 1));
                pending.push((index, depth + 1));
            }
            SmtSort::FloatingPoint(..) => {
                return Err(CompactPrintRefusal::Unsupported("floating-point sort"));
            }
        }
    }
    Ok(nodes)
}

// Check payload BEFORE the existing walker can clone strings or Sort boxes.
fn shape(node: &SmtExpr, payload: &mut usize) -> Result<(), CompactPrintRefusal> {
    use SmtExpr as E;
    let symbol = match node {
        E::Var { name, width: bits } => {
            width(*bits)?;
            Some(name)
        }
        E::UF {
            name,
            args,
            ret_sort,
        } => {
            if args.len() > MAX_ARITY {
                return Err(CompactPrintRefusal::Budget("node arity"));
            }
            *payload = payload
                .checked_add(sort_shape(ret_sort)? * 16)
                .ok_or(CompactPrintRefusal::Budget("payload bytes"))?;
            Some(name)
        }
        E::BvConst { width: bits, .. }
        | E::BvAdd { width: bits, .. }
        | E::BvSub { width: bits, .. }
        | E::BvMul { width: bits, .. }
        | E::BvSDiv { width: bits, .. }
        | E::BvUDiv { width: bits, .. }
        | E::BvURem { width: bits, .. }
        | E::BvNeg { width: bits, .. }
        | E::BvSlt { width: bits, .. }
        | E::BvSge { width: bits, .. }
        | E::BvSgt { width: bits, .. }
        | E::BvSle { width: bits, .. }
        | E::BvUlt { width: bits, .. }
        | E::BvUge { width: bits, .. }
        | E::BvUgt { width: bits, .. }
        | E::BvUle { width: bits, .. }
        | E::BvAnd { width: bits, .. }
        | E::BvOr { width: bits, .. }
        | E::BvXor { width: bits, .. }
        | E::BvShl { width: bits, .. }
        | E::BvLshr { width: bits, .. }
        | E::BvAshr { width: bits, .. }
        | E::Extract { width: bits, .. }
        | E::Concat { width: bits, .. }
        | E::ZeroExtend { width: bits, .. }
        | E::SignExtend { width: bits, .. } => {
            width(*bits)?;
            None
        }
        E::ConstArray { index_sort, .. } => {
            *payload = payload
                .checked_add(sort_shape(index_sort)? * 16)
                .ok_or(CompactPrintRefusal::Budget("payload bytes"))?;
            None
        }
        E::BoolConst(_)
        | E::Eq { .. }
        | E::Not { .. }
        | E::And { .. }
        | E::Or { .. }
        | E::Ite { .. }
        | E::Select { .. }
        | E::Store { .. } => None,
        E::ForAll { .. } | E::Exists { .. } => {
            return Err(CompactPrintRefusal::Unsupported("remaining quantifier"));
        }
        E::UFDecl { .. } => return Err(CompactPrintRefusal::Unsupported("declaration statement")),
        E::TrapIfZero { .. } | E::MemLoad { .. } => {
            return Err(CompactPrintRefusal::Unsupported(
                "implicit-symbol operation",
            ));
        }
        E::FPConst { .. }
        | E::FPAdd { .. }
        | E::FPMul { .. }
        | E::FPSub { .. }
        | E::FPDiv { .. }
        | E::FPNeg { .. }
        | E::FPEq { .. }
        | E::FPLt { .. }
        | E::FPGt { .. }
        | E::FPGe { .. }
        | E::FPLe { .. }
        | E::FPSqrt { .. }
        | E::FPRoundToIntegral { .. }
        | E::FPAbs { .. }
        | E::FPFma { .. }
        | E::FPIsNaN { .. }
        | E::FPIsInf { .. }
        | E::FPIsZero { .. }
        | E::FPIsNormal { .. }
        | E::FPToSBv { .. }
        | E::FPToUBv { .. }
        | E::BvToFP { .. }
        | E::FPToFP { .. }
        | E::BvBitsToFP { .. } => {
            return Err(CompactPrintRefusal::Unsupported(
                "floating-point expression",
            ));
        }
    };
    if let Some(name) = symbol {
        if name.is_empty() || name.len() > MAX_SYMBOL_BYTES {
            return Err(CompactPrintRefusal::Budget("symbol bytes"));
        }
        *payload = payload
            .checked_add(name.len())
            .ok_or(CompactPrintRefusal::Budget("payload bytes"))?;
    }
    if *payload > MAX_PAYLOAD_BYTES {
        return Err(CompactPrintRefusal::Budget("payload bytes"));
    }
    Ok(())
}

pub(crate) fn preflight(formula: &SmtExpr) -> Result<Preflight<'_>, CompactPrintRefusal> {
    preflight_roots(&[formula])
}

/// One aggregate shape budget for a finite collection of borrowed roots. This
/// is the same inspection as `preflight`, with sharing preserved across roots.
pub(crate) fn preflight_roots<'a>(
    formulas: &[&'a SmtExpr],
) -> Result<Preflight<'a>, CompactPrintRefusal> {
    if formulas.len() > MAX_ARITY {
        return Err(CompactPrintRefusal::Budget("root arity"));
    }
    let mut pending: Vec<_> = formulas
        .iter()
        .rev()
        .map(|root| (*root, false, 1usize))
        .collect();
    let mut depths = HashMap::<*const SmtExpr, Option<usize>>::new();
    let mut order = Vec::new();
    let mut edges = 0usize;
    let mut payload = 0usize;
    while let Some((node, ready, path_depth)) = pending.pop() {
        let key = node as *const SmtExpr;
        if ready {
            let mut depth = 1usize;
            node.for_each_child(&mut |child| {
                depth = depth.max(depths[&(child as *const SmtExpr)].unwrap() + 1);
            });
            if depth > MAX_DEPTH {
                return Err(CompactPrintRefusal::Budget("expression depth"));
            }
            depths.insert(key, Some(depth));
            order.push(node);
            continue;
        }
        if let Some(depth) = depths.get(&key) {
            if depth.is_none() {
                return Err(CompactPrintRefusal::Unsupported("cyclic expression"));
            }
            continue;
        }
        if depths.len() >= MAX_NODES || path_depth > MAX_DEPTH {
            return Err(CompactPrintRefusal::Budget(if path_depth > MAX_DEPTH {
                "expression depth"
            } else {
                "distinct nodes"
            }));
        }
        shape(node, &mut payload)?;
        let mut children = Vec::new();
        let mut excessive = false;
        node.for_each_child(&mut |child| {
            if children.len() >= MAX_ARITY {
                excessive = true;
            } else {
                children.push(child);
            }
        });
        if excessive {
            return Err(CompactPrintRefusal::Budget("node arity"));
        }
        edges = edges
            .checked_add(children.len())
            .filter(|n| *n <= MAX_EDGES)
            .ok_or(CompactPrintRefusal::Budget("child edges"))?;
        depths.insert(key, None);
        pending.push((node, true, path_depth));
        pending.extend(
            children
                .into_iter()
                .rev()
                .map(|child| (child, false, path_depth + 1)),
        );
    }
    Ok(Preflight {
        order,
        edges,
        payload,
    })
}

// Non-word children remain exact leaves or typed zero-argument aliases.
// Word children may contain admitted single-use inline expressions; their
// heights remain bounded by the same input preflight.
pub(crate) fn checked_sort(node: &SmtExpr) -> Result<SmtSort, CompactPrintRefusal> {
    use SmtExpr as E;
    let mut children = Vec::new();
    node.for_each_child(&mut |child| children.push(child.sort()));
    let malformed = || CompactPrintRefusal::Sort("operand/result sort mismatch");
    let same = |a: usize, b: usize| children[a] == children[b];
    let valid = match node {
        E::Var { .. } | E::BvConst { .. } | E::BoolConst(_) | E::UF { .. } => true,
        E::Eq { .. } => same(0, 1),
        E::Not { .. } => children[0] == SmtSort::Bool,
        E::And { .. } | E::Or { .. } => children.iter().all(|s| *s == SmtSort::Bool),
        E::Ite { .. } => children[0] == SmtSort::Bool && same(1, 2),
        E::Select { .. } => {
            matches!(&children[0], SmtSort::Array(index, _) if **index == children[1])
        }
        E::Store { .. } => {
            matches!(&children[0], SmtSort::Array(index, value) if **index == children[1] && **value == children[2])
        }
        E::ConstArray { .. } => true,
        E::Extract {
            high, low, width, ..
        } => {
            matches!(children[0], SmtSort::BitVec(bits) if low <= high && *high < bits && high - low + 1 == *width)
        }
        E::Concat { width, .. } => match (&children[0], &children[1]) {
            (SmtSort::BitVec(a), SmtSort::BitVec(b)) => a.checked_add(*b) == Some(*width),
            _ => false,
        },
        E::ZeroExtend {
            extra_bits, width, ..
        }
        | E::SignExtend {
            extra_bits, width, ..
        } => {
            matches!(children[0], SmtSort::BitVec(bits) if bits.checked_add(*extra_bits) == Some(*width))
        }
        _ => {
            let bits = node
                .try_bv_width()
                .ok()
                .or(match node {
                    E::BvSlt { width, .. }
                    | E::BvSge { width, .. }
                    | E::BvSgt { width, .. }
                    | E::BvSle { width, .. }
                    | E::BvUlt { width, .. }
                    | E::BvUge { width, .. }
                    | E::BvUgt { width, .. }
                    | E::BvUle { width, .. } => Some(*width),
                    _ => None,
                })
                .ok_or_else(malformed)?;
            children.iter().all(|s| *s == SmtSort::BitVec(bits))
        }
    };
    if !valid {
        return Err(malformed());
    }
    // The existing sort() fallback asks for a BV width on Ite, which panics
    // for Bool/array arms. Preserve the already checked arm's exact sort.
    let sort = if matches!(node, E::Ite { .. }) {
        children[1].clone()
    } else {
        node.sort()
    };
    sort_shape(&sort)?;
    Ok(sort)
}

struct BoundedText {
    text: String,
    limit: usize,
}
impl Write for BoundedText {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        if self
            .text
            .len()
            .checked_add(text.len())
            .is_none_or(|n| n > self.limit)
        {
            return Err(fmt::Error);
        }
        self.text.push_str(text);
        Ok(())
    }
}
fn spelling(node: &SmtExpr, limit: usize) -> Result<String, CompactPrintRefusal> {
    let mut out = BoundedText {
        text: String::new(),
        limit,
    };
    write!(&mut out, "{node}").map_err(|_| CompactPrintRefusal::Budget("output bytes"))?;
    Ok(out.text)
}

struct Binding<'a> {
    #[cfg(test)]
    original: &'a SmtExpr,
    #[cfg(test)]
    view: SmtExpr,
    name: String,
    definition: String,
    #[cfg(test)]
    sort: SmtSort,
    level: usize,
    _source: std::marker::PhantomData<&'a SmtExpr>,
}
struct PrintPlan<'a> {
    bindings: Vec<Binding<'a>>,
    root: SmtExpr,
    distinct_nodes: usize,
    edges: usize,
    levels: usize,
}

fn plan<'a>(
    formula: &'a SmtExpr,
    original_script: &str,
) -> Result<PrintPlan<'a>, CompactPrintRefusal> {
    if original_script.len() > MAX_SCRIPT_BYTES {
        return Err(CompactPrintRefusal::Budget("original script bytes"));
    }
    let scanned = preflight(formula)?;
    if scanned.edges == 0 {
        checked_sort(formula)?;
        return Ok(PrintPlan {
            bindings: Vec::new(),
            root: formula.clone(),
            distinct_nodes: scanned.order.len(),
            edges: 0,
            levels: 0,
        });
    }
    let prefix = (0..MAX_PREFIX_ATTEMPTS).map(|i| format!("tcg!raw{i}_"))
        .find(|prefix| !original_script.contains(prefix) && !scanned.order.iter().any(|node| matches!(node, SmtExpr::Var { name, .. } | SmtExpr::UF { name, .. } if name.contains(prefix))))
        .ok_or(CompactPrintRefusal::Budget("fresh-name attempts"))?;
    let mut bindings: Vec<Binding<'_>> = Vec::new();
    let mut uses = HashMap::<usize, usize>::new();
    for node in &scanned.order {
        node.for_each_child(&mut |child| {
            // The admitted edge census bounds this sum by MAX_EDGES.
            *uses.entry(std::ptr::from_ref(child) as usize).or_default() += 1;
        });
    }
    let mut dependency_levels = HashMap::<usize, usize>::new();
    let mut cursor = 0usize;
    let mut definition_bytes = 0usize;
    let root = formula
        .try_rewrite_dag(&mut |view| {
            let _original = scanned
                .order
                .get(cursor)
                .copied()
                .ok_or(CompactPrintRefusal::Unsupported("DAG visit order"))?;
            cursor += 1;
            let sort = checked_sort(view)?;
            let mut child_count = 0usize;
            let mut dependency = 0usize;
            _original.for_each_child(&mut |child| {
                child_count += 1;
                dependency =
                    dependency.max(dependency_levels[&(std::ptr::from_ref(child) as usize)]);
            });
            let key = std::ptr::from_ref(_original) as usize;
            // Single-use BV nodes can stay inline. Keep Bool/array views
            // named so the existing shallow sort contract never asks sort()
            // to infer a nested Bool/array ITE's bit-vector width.
            if child_count == 0
                || (matches!(sort, SmtSort::BitVec(_))
                    && !std::ptr::eq(_original, formula)
                    && uses.get(&key).copied().unwrap_or(0) <= 1)
            {
                dependency_levels.insert(key, dependency);
                return Ok(None);
            }
            let level = dependency + 1;
            dependency_levels.insert(key, level);
            if bindings.len() >= MAX_NODES || level > MAX_DEPTH {
                return Err(CompactPrintRefusal::Budget("bindings/levels"));
            }
            let definition = spelling(view, MAX_OUTPUT_BYTES - definition_bytes)?;
            definition_bytes += definition.len();
            let name = format!("{prefix}{}", bindings.len());
            let alias = SmtExpr::uf(name.clone(), vec![], sort.clone());
            bindings.push(Binding {
                #[cfg(test)]
                original: _original,
                #[cfg(test)]
                view: view.clone(),
                name,
                definition,
                #[cfg(test)]
                sort,
                level,
                _source: std::marker::PhantomData,
            });
            Ok(Some(alias))
        })?
        .unwrap_or_else(|| formula.clone());
    if cursor != scanned.order.len() {
        return Err(CompactPrintRefusal::Unsupported("DAG visit count"));
    }
    let levels = bindings
        .iter()
        .map(|binding| binding.level)
        .max()
        .unwrap_or(0);
    Ok(PrintPlan {
        bindings,
        root,
        distinct_nodes: scanned.order.len(),
        edges: scanned.edges,
        levels,
    })
}

/// Compare the existing Display spelling without staging another expanded
/// String. Admission bounds depth/payload; the sink stops at the first byte
/// mismatch or beyond the expected output length. This grants no semantics.
pub(crate) fn prints_exactly(formula: &SmtExpr, expected: &str) -> bool {
    if expected.len() > MAX_OUTPUT_BYTES || preflight(formula).is_err() {
        return false;
    }
    struct Exact<'a> {
        remaining: &'a str,
    }
    impl fmt::Write for Exact<'_> {
        fn write_str(&mut self, text: &str) -> fmt::Result {
            self.remaining = self.remaining.strip_prefix(text).ok_or(fmt::Error)?;
            Ok(())
        }
    }
    let mut output = Exact {
        remaining: expected,
    };
    write!(&mut output, "{formula}").is_ok() && output.remaining.is_empty()
}

pub(crate) fn compact_formula(
    formula: &SmtExpr,
    original_script: &str,
) -> Result<Option<CompactFormula>, CompactPrintRefusal> {
    let plan = plan(formula, original_script)?;
    if plan.bindings.is_empty() {
        return Ok(None);
    }
    let root = spelling(&plan.root, MAX_OUTPUT_BYTES)?;
    let mut size = root.len();
    for binding in &plan.bindings {
        size = size
            .checked_add(binding.name.len())
            .and_then(|n| n.checked_add(binding.definition.len()))
            .and_then(|n| n.checked_add(4))
            .filter(|n| *n <= MAX_OUTPUT_BYTES)
            .ok_or(CompactPrintRefusal::Budget("output bytes"))?;
    }
    size = size
        .checked_add(plan.levels * 9)
        .filter(|n| *n <= MAX_OUTPUT_BYTES)
        .ok_or(CompactPrintRefusal::Budget("output bytes"))?;
    let mut groups = vec![Vec::new(); plan.levels];
    for (i, binding) in plan.bindings.iter().enumerate() {
        groups[binding.level - 1].push(i);
    }
    let mut text = String::with_capacity(size);
    for group in groups {
        text.push_str("(let (");
        for (position, index) in group.into_iter().enumerate() {
            if position != 0 {
                text.push(' ');
            }
            let binding = &plan.bindings[index];
            text.push('(');
            text.push_str(&binding.name);
            text.push(' ');
            text.push_str(&binding.definition);
            text.push(')');
        }
        text.push_str(") ");
    }
    text.push_str(&root);
    for _ in 0..plan.levels {
        text.push(')');
    }
    let output_bytes = text.len();
    Ok(Some(CompactFormula {
        text,
        distinct_nodes: plan.distinct_nodes,
        edges: plan.edges,
        bindings: plan.bindings.len(),
        output_bytes,
        levels: plan.levels,
    }))
}
