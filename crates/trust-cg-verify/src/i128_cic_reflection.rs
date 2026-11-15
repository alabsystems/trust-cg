// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Bounded, unsimplified rendering of an original four-limb Bool/BV query.
//!
//! This constructs an EXPECTED CIC goal, never a proof or a verdict. The Raw
//! vocabulary must itself be independently admitted. A later kernel check must
//! compare an actual retained proof to this exact goal. No theorem name, shape,
//! fingerprint or successful construction supplies proof authority.

use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr as E;
use clean_kernel::{BinderInfo, Expr, Level, Name};
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};

const MAX_NODES: usize = 32_768;
const MAX_EDGES: usize = 131_072;
const MAX_DEPTH: usize = 256;
const MAX_EXPANDED: usize = 131_072;
const MAX_BINDING_BYTES: usize = 4_194_304;
const MAX_STRING_BYTES: usize = 4096;
const MAX_HEAD_BYTES: usize = 1_048_576;
const BINDING_DOMAIN: &[u8] = b"trust-cg/original-i128-cic/v1\0";

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReflectionRefusal {
    Profile(&'static str),
    Sort(&'static str),
    Unsupported,
    FreeVariable(String),
    Budget(&'static str),
    Cycle,
}

impl std::fmt::Display for ReflectionRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "original i128 CIC rendering declined: {self:?}")
    }
}
impl std::error::Error for ReflectionRefusal {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReflectionStats {
    pub distinct_nodes: usize,
    pub edges: usize,
    pub expanded_nodes: usize,
    pub depth: usize,
}

/// No proof constructor, checked-state deserializer, or conversion to a grade.
#[derive(Debug)]
pub struct OriginalI128Goal {
    goal: Expr,
    input_order: Vec<(String, u32)>,
    binding: Vec<u8>,
    binding_sha256: [u8; 32],
    stats: ReflectionStats,
}

impl OriginalI128Goal {
    pub fn expected_goal(&self) -> &Expr {
        &self.goal
    }
    pub fn input_order(&self) -> &[(String, u32)] {
        &self.input_order
    }
    /// Lossless length-framed metadata and both complete original AST trees.
    /// Sharing is expanded, so equal ASTs hash identically regardless of Arc
    /// allocation/sharing; neither occurrences nor operand order are discarded.
    pub fn original_binding_bytes(&self) -> &[u8] {
        &self.binding
    }
    pub fn original_binding_sha256(&self) -> &[u8; 32] {
        &self.binding_sha256
    }
    /// Resource diagnostics only, never an admission denominator or authority.
    pub fn stats(&self) -> ReflectionStats {
        self.stats
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Sort {
    Bool,
    Bv(u32),
}

#[derive(Clone, Copy)]
enum Kind<'a> {
    Var(&'a str, u32),
    Constant(u64, u32),
    Boolean(bool),
    Binary(&'static str, u32),
    Compare(&'static str, u32),
    Neg(u32),
    Eq,
    Not,
    BoolBinary(&'static str),
    Ite,
    Extract(u32, u32, u32),
    Concat(u32),
    Extend(&'static str, u32, u32),
}

// Tags are part of binding schema v1. Stored width/range metadata is encoded
// even where the children's independently validated sorts determine it.
fn shape(node: &E) -> Result<(u8, Kind<'_>, Vec<&E>), ReflectionRefusal> {
    use Kind as K;
    Ok(match node {
        E::Var { name, width } => (0, K::Var(name, *width), vec![]),
        E::BvConst { value, width } => (1, K::Constant(*value, *width), vec![]),
        E::BoolConst(value) => (2, K::Boolean(*value), vec![]),
        E::BvAdd { lhs, rhs, width } => (3, K::Binary("bvAdd", *width), vec![lhs, rhs]),
        E::BvSub { lhs, rhs, width } => (4, K::Binary("bvSub", *width), vec![lhs, rhs]),
        E::BvMul { lhs, rhs, width } => (5, K::Binary("bvMul", *width), vec![lhs, rhs]),
        E::BvAnd { lhs, rhs, width } => (6, K::Binary("bvAnd", *width), vec![lhs, rhs]),
        E::BvOr { lhs, rhs, width } => (7, K::Binary("bvOr", *width), vec![lhs, rhs]),
        E::BvXor { lhs, rhs, width } => (8, K::Binary("bvXor", *width), vec![lhs, rhs]),
        E::BvUDiv { lhs, rhs, width } => (9, K::Binary("bvUDiv", *width), vec![lhs, rhs]),
        E::BvShl { lhs, rhs, width } => (10, K::Binary("bvShl", *width), vec![lhs, rhs]),
        E::BvLshr { lhs, rhs, width } => (11, K::Binary("bvLshr", *width), vec![lhs, rhs]),
        E::BvAshr { lhs, rhs, width } => (12, K::Binary("bvAshr", *width), vec![lhs, rhs]),
        E::BvNeg { operand, width } => (13, K::Neg(*width), vec![operand]),
        E::Eq { lhs, rhs } => (14, K::Eq, vec![lhs, rhs]),
        E::BvUlt { lhs, rhs, width } => (15, K::Compare("bvUlt", *width), vec![lhs, rhs]),
        E::BvUgt { lhs, rhs, width } => (16, K::Compare("bvUgt", *width), vec![lhs, rhs]),
        E::BvUle { lhs, rhs, width } => (17, K::Compare("bvUle", *width), vec![lhs, rhs]),
        E::BvUge { lhs, rhs, width } => (18, K::Compare("bvUge", *width), vec![lhs, rhs]),
        E::BvSlt { lhs, rhs, width } => (19, K::Compare("bvSlt", *width), vec![lhs, rhs]),
        E::BvSgt { lhs, rhs, width } => (20, K::Compare("bvSgt", *width), vec![lhs, rhs]),
        E::BvSle { lhs, rhs, width } => (21, K::Compare("bvSle", *width), vec![lhs, rhs]),
        E::BvSge { lhs, rhs, width } => (22, K::Compare("bvSge", *width), vec![lhs, rhs]),
        E::Not { operand } => (23, K::Not, vec![operand]),
        E::And { lhs, rhs } => (24, K::BoolBinary("boolAnd"), vec![lhs, rhs]),
        E::Or { lhs, rhs } => (25, K::BoolBinary("boolOr"), vec![lhs, rhs]),
        E::Ite {
            cond,
            then_expr,
            else_expr,
        } => (26, K::Ite, vec![cond, then_expr, else_expr]),
        E::Extract {
            high,
            low,
            operand,
            width,
        } => (27, K::Extract(*high, *low, *width), vec![operand]),
        E::Concat { hi, lo, width } => (28, K::Concat(*width), vec![hi, lo]),
        E::ZeroExtend {
            operand,
            extra_bits,
            width,
        } => (
            29,
            K::Extend("bvZeroExtend", *extra_bits, *width),
            vec![operand],
        ),
        E::SignExtend {
            operand,
            extra_bits,
            width,
        } => (
            30,
            K::Extend("bvSignExtend", *extra_bits, *width),
            vec![operand],
        ),
        _ => return Err(ReflectionRefusal::Unsupported),
    })
}

fn constant(parts: &[&str]) -> Expr {
    // Components are fixed program literals, never parsed dotted input names.
    let name = parts.iter().fold(Name::anon(), |name, part| name.str(part));
    Expr::const_(name, Vec::<Level>::new())
}
fn raw(name: &'static str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(
        constant(&["Trust", "Cert", "CheckedMulI128Raw", name]),
        args,
    )
}
fn nat(value: u32) -> Expr {
    Expr::nat_lit(u64::from(value))
}
fn bv(width: u32) -> Expr {
    Expr::app(constant(&["BitVec"]), nat(width))
}
fn width(width: u32) -> Result<u32, ReflectionRefusal> {
    if (1..=128).contains(&width) {
        Ok(width)
    } else {
        Err(ReflectionRefusal::Sort("BV width outside 1..128"))
    }
}
fn require(found: Sort, expected: Sort) -> Result<(), ReflectionRefusal> {
    if found == expected {
        Ok(())
    } else {
        Err(ReflectionRefusal::Sort("operand/result sort mismatch"))
    }
}
fn word(sort: Sort) -> Result<u32, ReflectionRefusal> {
    if let Sort::Bv(w) = sort {
        Ok(w)
    } else {
        Err(ReflectionRefusal::Sort("expected bitvector"))
    }
}

struct Node {
    sort: Sort,
    term: Expr,
    head: Vec<u8>,
    children: Vec<usize>,
    depth: usize,
    expanded: usize,
}

fn bytes(out: &mut Vec<u8>, value: &[u8]) -> Result<(), ReflectionRefusal> {
    if out
        .len()
        .checked_add(value.len())
        .is_none_or(|n| n > MAX_BINDING_BYTES)
    {
        return Err(ReflectionRefusal::Budget("original binding bytes"));
    }
    out.extend_from_slice(value);
    Ok(())
}
fn number(out: &mut Vec<u8>, value: u32) -> Result<(), ReflectionRefusal> {
    bytes(out, &value.to_be_bytes())
}
fn string(out: &mut Vec<u8>, value: &str) -> Result<(), ReflectionRefusal> {
    if value.len() > MAX_STRING_BYTES {
        return Err(ReflectionRefusal::Budget("UTF8 string bytes"));
    }
    number(out, value.len() as u32)?;
    bytes(out, value.as_bytes())
}

fn lower(
    tag: u8,
    kind: Kind<'_>,
    ids: Vec<usize>,
    nodes: &[Node],
    inputs: &HashMap<&str, u32>,
) -> Result<Node, ReflectionRefusal> {
    let child: Vec<_> = ids.iter().map(|id| &nodes[*id]).collect();
    let mut head = vec![tag];
    let (sort, term) = match kind {
        Kind::Var(name, w) => {
            width(w)?;
            number(&mut head, w)?;
            string(&mut head, name)?;
            let index = *inputs
                .get(name)
                .ok_or_else(|| ReflectionRefusal::FreeVariable(name.to_owned()))?;
            if w != 64 {
                return Err(ReflectionRefusal::Sort(
                    "variable differs from declared BV64",
                ));
            }
            (Sort::Bv(w), Expr::bvar(3 - index))
        }
        Kind::Constant(value, w) => {
            width(w)?;
            if w < 64 && value >> w != 0 {
                return Err(ReflectionRefusal::Sort("noncanonical literal payload"));
            }
            number(&mut head, w)?;
            bytes(&mut head, &value.to_be_bytes())?;
            (Sort::Bv(w), raw("bvOfNat", [nat(w), Expr::nat_lit(value)]))
        }
        Kind::Boolean(value) => {
            bytes(&mut head, &[u8::from(value)])?;
            (
                Sort::Bool,
                constant(&["Bool", if value { "true" } else { "false" }]),
            )
        }
        Kind::Binary(op, w) | Kind::Compare(op, w) => {
            width(w)?;
            require(child[0].sort, Sort::Bv(w))?;
            require(child[1].sort, Sort::Bv(w))?;
            number(&mut head, w)?;
            let result = if matches!(kind, Kind::Compare(..)) {
                Sort::Bool
            } else {
                Sort::Bv(w)
            };
            (
                result,
                raw(op, [nat(w), child[0].term.clone(), child[1].term.clone()]),
            )
        }
        Kind::Neg(w) => {
            width(w)?;
            require(child[0].sort, Sort::Bv(w))?;
            number(&mut head, w)?;
            (Sort::Bv(w), raw("bvNeg", [nat(w), child[0].term.clone()]))
        }
        Kind::Eq => {
            require(child[0].sort, child[1].sort)?;
            let a = child[0].term.clone();
            let b = child[1].term.clone();
            let result = match child[0].sort {
                Sort::Bool => raw("boolEq", [a, b]),
                Sort::Bv(w) => raw("bvEq", [nat(w), a, b]),
            };
            (Sort::Bool, result)
        }
        Kind::Not => {
            require(child[0].sort, Sort::Bool)?;
            (Sort::Bool, raw("boolNot", [child[0].term.clone()]))
        }
        Kind::BoolBinary(op) => {
            require(child[0].sort, Sort::Bool)?;
            require(child[1].sort, Sort::Bool)?;
            (
                Sort::Bool,
                raw(op, [child[0].term.clone(), child[1].term.clone()]),
            )
        }
        Kind::Ite => {
            require(child[0].sort, Sort::Bool)?;
            require(child[1].sort, child[2].sort)?;
            let args = [
                child[0].term.clone(),
                child[1].term.clone(),
                child[2].term.clone(),
            ];
            (
                child[1].sort,
                match child[1].sort {
                    Sort::Bool => raw("boolIte", args),
                    Sort::Bv(w) => raw("bvIte", std::iter::once(nat(w)).chain(args)),
                },
            )
        }
        Kind::Extract(high, low, w) => {
            width(w)?;
            let input = word(child[0].sort)?;
            if low > high || high >= input || high - low + 1 != w {
                return Err(ReflectionRefusal::Sort("invalid extract range/width"));
            }
            for value in [high, low, w] {
                number(&mut head, value)?;
            }
            (
                Sort::Bv(w),
                raw(
                    "bvExtract",
                    [nat(input), nat(high), nat(low), child[0].term.clone()],
                ),
            )
        }
        Kind::Concat(w) => {
            width(w)?;
            let hi = word(child[0].sort)?;
            let lo = word(child[1].sort)?;
            if hi.checked_add(lo) != Some(w) {
                return Err(ReflectionRefusal::Sort("concat width mismatch"));
            }
            number(&mut head, w)?;
            (
                Sort::Bv(w),
                raw(
                    "bvConcat",
                    [
                        nat(hi),
                        nat(lo),
                        child[0].term.clone(),
                        child[1].term.clone(),
                    ],
                ),
            )
        }
        Kind::Extend(op, extra, w) => {
            width(w)?;
            let input = word(child[0].sort)?;
            if input.checked_add(extra) != Some(w) {
                return Err(ReflectionRefusal::Sort("extension width mismatch"));
            }
            number(&mut head, extra)?;
            number(&mut head, w)?;
            (
                Sort::Bv(w),
                raw(op, [nat(input), nat(extra), child[0].term.clone()]),
            )
        }
    };
    let depth = 1 + child.iter().map(|n| n.depth).max().unwrap_or(0);
    let expanded = child
        .iter()
        .try_fold(1usize, |sum, n| sum.checked_add(n.expanded))
        .filter(|n| *n <= MAX_EXPANDED)
        .ok_or(ReflectionRefusal::Budget("expanded AST occurrences"))?;
    Ok(Node {
        sort,
        term,
        head,
        children: ids,
        depth,
        expanded,
    })
}

fn category(kind: Option<TransvalCheckKind>) -> u8 {
    match kind {
        None => 0,
        Some(TransvalCheckKind::DataFlow) => 1,
        Some(TransvalCheckKind::ControlFlow) => 2,
        Some(TransvalCheckKind::ReturnValue) => 3,
        Some(TransvalCheckKind::Termination) => 4,
        Some(TransvalCheckKind::InstructionLowering) => 5,
        Some(TransvalCheckKind::PeepholeOptimization) => 6,
        Some(TransvalCheckKind::MemoryModel) => 7,
        Some(TransvalCheckKind::RegisterAllocation) => 8,
        Some(TransvalCheckKind::Vectorization) => 9,
    }
}

/// Render BOTH unchanged original expressions. The fixed profile is four
/// distinct ordered BV64 declarations, no FP inputs or assumptions, and BV1
/// roots. It neither recognizes a theorem nor inspects its purported verdict.
pub fn render_original_i128_goal(
    obligation: &ProofObligation,
) -> Result<OriginalI128Goal, ReflectionRefusal> {
    if obligation.inputs.len() != 4
        || !obligation.fp_inputs.is_empty()
        || !obligation.preconditions.is_empty()
    {
        return Err(ReflectionRefusal::Profile(
            "exactly four BV64 inputs, no FP/preconditions",
        ));
    }
    let mut seen = HashSet::new();
    let mut inputs = HashMap::new();
    let mut binding = Vec::new();
    bytes(&mut binding, BINDING_DOMAIN)?;
    string(&mut binding, &obligation.name)?;
    bytes(&mut binding, &[category(obligation.category)])?;
    match &obligation.machine_side_provenance {
        MachineSideProvenance::StaticDb => bytes(&mut binding, &[0])?,
        MachineSideProvenance::Reconstructed { from_opcode, arity } => {
            bytes(&mut binding, &[1])?;
            string(&mut binding, from_opcode)?;
            bytes(&mut binding, &[*arity])?;
        }
    }
    number(&mut binding, 4)?;
    number(&mut binding, 0)?;
    number(&mut binding, 0)?;
    for (index, (name, w)) in obligation.inputs.iter().enumerate() {
        if *w != 64 || !seen.insert(name.as_str()) {
            return Err(ReflectionRefusal::Profile(
                "duplicate input name or non-BV64 declaration",
            ));
        }
        string(&mut binding, name)?;
        number(&mut binding, *w)?;
        inputs.insert(name.as_str(), index as u32);
    }

    let roots = [&obligation.trust_ir_expr, &obligation.aarch64_expr];
    let mut positions = HashMap::<*const E, Option<usize>>::new();
    let mut nodes = Vec::<Node>::new();
    let mut edges = 0usize;
    let mut payload = 0usize;
    for root in roots {
        let mut pending = vec![(root, false, 1usize)];
        while let Some((node, ready, path)) = pending.pop() {
            let key = node as *const E;
            if !ready {
                if let Some(position) = positions.get(&key) {
                    let id = position.ok_or(ReflectionRefusal::Cycle)?;
                    if path
                        .checked_add(nodes[id].depth - 1)
                        .is_none_or(|d| d > MAX_DEPTH)
                    {
                        return Err(ReflectionRefusal::Budget("AST depth"));
                    }
                    continue;
                }
                if positions.len() >= MAX_NODES || path > MAX_DEPTH {
                    return Err(ReflectionRefusal::Budget("AST nodes/depth"));
                }
                let (_, _, children) = shape(node)?;
                edges = edges
                    .checked_add(children.len())
                    .filter(|n| *n <= MAX_EDGES)
                    .ok_or(ReflectionRefusal::Budget("AST edges"))?;
                positions.insert(key, None);
                pending.push((node, true, path));
                pending.extend(
                    children
                        .into_iter()
                        .rev()
                        .map(|child| (child, false, path + 1)),
                );
            } else {
                let (tag, kind, children) = shape(node)?;
                let ids: Vec<usize> = children
                    .iter()
                    .map(|child| positions[&(*child as *const E)].ok_or(ReflectionRefusal::Cycle))
                    .collect::<Result<_, _>>()?;
                let rendered = lower(tag, kind, ids, &nodes, &inputs)?;
                if path + rendered.depth - 1 > MAX_DEPTH {
                    return Err(ReflectionRefusal::Budget("AST depth"));
                }
                payload = payload
                    .checked_add(rendered.head.len())
                    .filter(|n| *n <= MAX_HEAD_BYTES)
                    .ok_or(ReflectionRefusal::Budget("AST payload"))?;
                positions.insert(key, Some(nodes.len()));
                nodes.push(rendered);
            }
        }
    }
    let source = positions[&(roots[0] as *const E)].ok_or(ReflectionRefusal::Cycle)?;
    let machine = positions[&(roots[1] as *const E)].ok_or(ReflectionRefusal::Cycle)?;
    require(nodes[source].sort, Sort::Bv(1))?;
    require(nodes[machine].sort, Sort::Bv(1))?;
    let expanded = nodes[source]
        .expanded
        .checked_add(nodes[machine].expanded)
        .filter(|n| *n <= MAX_EXPANDED)
        .ok_or(ReflectionRefusal::Budget("combined AST occurrences"))?;
    for (role, root) in [source, machine].into_iter().enumerate() {
        bytes(&mut binding, &[role as u8])?;
        let mut pending = vec![root];
        while let Some(id) = pending.pop() {
            let node = &nodes[id];
            number(&mut binding, node.head.len() as u32)?;
            bytes(&mut binding, &node.head)?;
            bytes(&mut binding, &[node.children.len() as u8])?;
            pending.extend(node.children.iter().rev().copied());
        }
    }
    let equality = Expr::const_(Name::anon().str("Eq"), vec![Level::succ(Level::zero())]);
    let mut goal = Expr::apps(
        equality,
        [
            bv(1),
            nodes[source].term.clone(),
            nodes[machine].term.clone(),
        ],
    );
    for _ in obligation.inputs.iter().rev() {
        goal = Expr::pi(BinderInfo::Default, bv(64), goal);
    }
    let binding_sha256 = Sha256::digest(&binding).into();
    let stats = ReflectionStats {
        distinct_nodes: nodes.len(),
        edges,
        expanded_nodes: expanded,
        depth: nodes[source].depth.max(nodes[machine].depth),
    };
    Ok(OriginalI128Goal {
        goal,
        input_order: obligation.inputs.clone(),
        binding,
        binding_sha256,
        stats,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::ExprKind;
    use std::sync::Arc;

    fn flag(condition: E) -> E {
        E::ite(condition, E::bv_const(1, 1), E::bv_const(0, 1))
    }
    fn fixture(source: E, machine: E) -> ProofObligation {
        ProofObligation {
            name: "original-renderer-control".into(),
            trust_ir_expr: source,
            aarch64_expr: machine,
            inputs: ["a", "b", "c", "d"].map(|n| (n.into(), 64)).to_vec(),
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
            machine_side_provenance: MachineSideProvenance::StaticDb,
        }
    }
    fn basic() -> ProofObligation {
        fixture(E::var("a", 64).extract(0, 0), E::var("b", 64).extract(0, 0))
    }
    fn spine(mut term: &Expr) -> (&Expr, Vec<&Expr>) {
        let mut args = Vec::new();
        while let ExprKind::App(fun, arg) = term.kind() {
            args.push(arg.as_ref());
            term = fun.as_ref();
        }
        args.reverse();
        (term, args)
    }
    fn changed(original: &OriginalI128Goal, candidate: ProofObligation) {
        if let Ok(other) = render_original_i128_goal(&candidate) {
            assert_ne!(
                original.original_binding_sha256(),
                other.original_binding_sha256()
            );
            assert_ne!(original.expected_goal(), other.expected_goal());
        }
    }

    #[test]
    fn actual_three_original_rows_are_complete_goals_without_credit() {
        use crate::checked_mul_i128_proofs as p;
        for original in [
            p::proof_checked_umul_i128_limb_check_flag(),
            p::proof_checked_smul_i128_limb_check_flag(),
            p::proof_checked_umul_i128_const_limit_flag(),
        ] {
            let rendered = render_original_i128_goal(&original).expect("actual original row");
            assert_eq!(rendered.input_order(), original.inputs);
            assert_eq!(
                rendered.original_binding_sha256().as_slice(),
                Sha256::digest(rendered.original_binding_bytes()).as_slice()
            );
            assert!(rendered.stats().expanded_nodes > rendered.stats().distinct_nodes);
            let mut body = rendered.expected_goal();
            for _ in 0..4 {
                let ExprKind::Pi(_, domain, next) = body.kind() else {
                    panic!("missing full input binder")
                };
                assert_eq!(domain.as_ref(), &bv(64));
                body = next;
            }
            let (head, args) = spine(body);
            assert!(
                matches!(head.kind(), ExprKind::Const(name, levels) if *name == Name::anon().str("Eq") && levels.len() == 1)
            );
            assert_eq!(args.len(), 3);
            assert_eq!(args[0], &bv(1));
        }
    }

    #[test]
    fn actual_declaration_order_and_utf8_names_bind_exactly_four_levels() {
        let mut original = basic();
        original.inputs = ["a.b", "a::b", "变量", "01"]
            .map(|name| (name.into(), 64))
            .to_vec();
        original.trust_ir_expr = E::var("a.b", 64).extract(0, 0);
        original.aarch64_expr = E::var("01", 64).extract(0, 0);
        let rendered = render_original_i128_goal(&original).unwrap();
        let mut body = rendered.expected_goal();
        for _ in 0..4 {
            let ExprKind::Pi(_, _, next) = body.kind() else {
                panic!()
            };
            body = next;
        }
        let (_, eq) = spine(body);
        for (term, index) in [(eq[1], 3), (eq[2], 0)] {
            let (head, args) = spine(term);
            assert_eq!(
                head,
                &constant(&["Trust", "Cert", "CheckedMulI128Raw", "bvExtract"])
            );
            assert_eq!(args, vec![&nat(64), &nat(0), &nat(0), &Expr::bvar(index)]);
        }
        assert_eq!(rendered.input_order(), original.inputs);
    }

    #[test]
    fn duplicate_free_wrong_width_and_extra_domains_decline_whole_goal() {
        let mut row = basic();
        row.inputs[1].0 = "a".into();
        assert!(matches!(
            render_original_i128_goal(&row),
            Err(ReflectionRefusal::Profile(_))
        ));
        let mut row = basic();
        row.inputs[0].1 = 63;
        assert!(render_original_i128_goal(&row).is_err());
        let mut row = basic();
        row.trust_ir_expr = E::var("fresh@q", 64).extract(0, 0);
        assert!(matches!(
            render_original_i128_goal(&row),
            Err(ReflectionRefusal::FreeVariable(_))
        ));
        let mut row = basic();
        row.trust_ir_expr = E::var("a", 32).extract(0, 0);
        assert!(render_original_i128_goal(&row).is_err());
        let mut row = basic();
        row.preconditions.push(E::BoolConst(true));
        assert!(render_original_i128_goal(&row).is_err());
        let mut row = basic();
        row.fp_inputs.push(("unused-fp".into(), 8, 24));
        assert!(render_original_i128_goal(&row).is_err());
        let mut row = basic();
        row.inputs.pop();
        assert!(render_original_i128_goal(&row).is_err());
    }

    #[test]
    fn malformed_binary_boolean_and_unreachable_branch_sorts_decline() {
        let a = Arc::new(E::var("a", 64));
        let b = Arc::new(E::var("b", 64));
        for malformed in [
            E::BvAdd {
                lhs: a.clone(),
                rhs: b.clone(),
                width: 63,
            },
            E::Eq {
                lhs: a.clone(),
                rhs: Arc::new(E::BoolConst(false)),
            },
            E::And {
                lhs: a.clone(),
                rhs: Arc::new(E::BoolConst(true)),
            },
            E::Ite {
                cond: Arc::new(E::bv_const(1, 1)),
                then_expr: a.clone(),
                else_expr: b,
            },
            E::Ite {
                cond: Arc::new(E::BoolConst(false)),
                then_expr: Arc::new(E::bv_const(0, 32)),
                else_expr: a,
            },
        ] {
            assert!(
                render_original_i128_goal(&fixture(
                    flag(malformed.eq_expr(E::bv_const(0, 64))),
                    E::bv_const(0, 1)
                ))
                .is_err()
            );
        }
    }

    #[test]
    fn extraction_concat_extension_and_shift_metadata_are_validated() {
        let a = Arc::new(E::var("a", 64));
        let b = Arc::new(E::var("b", 64));
        for malformed in [
            E::Extract {
                high: 64,
                low: 0,
                operand: a.clone(),
                width: 65,
            },
            E::Extract {
                high: 0,
                low: 1,
                operand: a.clone(),
                width: 1,
            },
            E::Extract {
                high: 63,
                low: 0,
                operand: a.clone(),
                width: 63,
            },
            E::Concat {
                hi: a.clone(),
                lo: b.clone(),
                width: 127,
            },
            E::ZeroExtend {
                operand: a.clone(),
                extra_bits: 64,
                width: 127,
            },
            E::SignExtend {
                operand: a.clone(),
                extra_bits: u32::MAX,
                width: 64,
            },
            E::BvLshr {
                lhs: a,
                rhs: Arc::new(E::bv_const(63, 32)),
                width: 64,
            },
        ] {
            assert!(
                render_original_i128_goal(&fixture(malformed.extract(0, 0), E::bv_const(0, 1)))
                    .is_err()
            );
        }
        for (value, width) in [(0, 0), (0, 129), (2, 1), (65_536, 16)] {
            assert!(
                render_original_i128_goal(&fixture(E::BvConst { value, width }, E::bv_const(0, 1)))
                    .is_err()
            );
        }
    }

    #[test]
    fn original_operands_concat_order_cast_kind_and_high_shift_bits_survive() {
        let a = E::var("a", 64);
        let b = E::var("b", 64);
        let original = fixture(
            flag(a.clone().concat(b.clone()).eq_expr(E::bv_const(0, 128))),
            E::bv_const(0, 1),
        );
        let rendered = render_original_i128_goal(&original).unwrap();
        changed(
            &rendered,
            fixture(
                flag(b.concat(a).eq_expr(E::bv_const(0, 128))),
                E::bv_const(0, 1),
            ),
        );
        let original = fixture(
            flag(E::var("a", 64).zero_ext(64).eq_expr(E::bv_const(0, 128))),
            E::bv_const(0, 1),
        );
        let rendered = render_original_i128_goal(&original).unwrap();
        changed(
            &rendered,
            fixture(
                flag(E::var("a", 64).sign_ext(64).eq_expr(E::bv_const(0, 128))),
                E::bv_const(0, 1),
            ),
        );
        let original = fixture(
            flag(
                E::var("a", 64)
                    .bvlshr(E::bv_const(0, 64))
                    .eq_expr(E::var("b", 64)),
            ),
            E::bv_const(0, 1),
        );
        let rendered = render_original_i128_goal(&original).unwrap();
        changed(
            &rendered,
            fixture(
                flag(
                    E::var("a", 64)
                        .bvlshr(E::bv_const(1 << 63, 64))
                        .eq_expr(E::var("b", 64)),
                ),
                E::bv_const(0, 1),
            ),
        );
    }

    #[test]
    fn bool_equality_ite_and_bitvector_comparison_operators_stay_distinct() {
        let a = E::var("a", 64);
        let b = E::var("b", 64);
        let comparisons = [
            a.clone().bvult(b.clone()),
            a.clone().bvugt(b.clone()),
            a.clone().bvule(b.clone()),
            a.clone().bvuge(b.clone()),
            a.clone().bvslt(b.clone()),
            a.clone().bvsgt(b.clone()),
            a.clone().bvsle(b.clone()),
            a.bvsge(b),
        ];
        let mut hashes = HashSet::new();
        for cmp in comparisons {
            let condition =
                E::ite(E::BoolConst(true), cmp, E::BoolConst(false)).eq_expr(E::BoolConst(true));
            let row = fixture(flag(condition), E::bv_const(0, 1));
            assert!(
                hashes.insert(
                    *render_original_i128_goal(&row)
                        .unwrap()
                        .original_binding_sha256()
                )
            );
        }
        assert_eq!(hashes.len(), 8);
    }

    #[test]
    fn no_unsupported_or_unreached_term_is_erased() {
        let unsupported = E::BvSDiv {
            lhs: Arc::new(E::var("a", 64)),
            rhs: Arc::new(E::var("b", 64)),
            width: 64,
        };
        let row = fixture(
            E::ite(
                E::BoolConst(false),
                unsupported.extract(0, 0),
                E::bv_const(0, 1),
            ),
            E::bv_const(0, 1),
        );
        assert_eq!(
            render_original_i128_goal(&row).unwrap_err(),
            ReflectionRefusal::Unsupported
        );
        let row = fixture(
            flag(E::uf("uninterpreted", vec![], crate::smt::SmtSort::Bool)),
            E::bv_const(0, 1),
        );
        assert_eq!(
            render_original_i128_goal(&row).unwrap_err(),
            ReflectionRefusal::Unsupported
        );
        let row = fixture(E::bv_const(0, 64), E::bv_const(0, 64));
        assert!(render_original_i128_goal(&row).is_err());
    }

    #[test]
    fn binding_retains_every_nonformula_obligation_field() {
        let row = basic();
        let original = render_original_i128_goal(&row).unwrap();
        let mut changes = Vec::new();
        let mut next = row.clone();
        next.name.push('\0');
        changes.push(next);
        let mut next = row.clone();
        next.category = Some(TransvalCheckKind::InstructionLowering);
        changes.push(next);
        let mut next = row.clone();
        next.machine_side_provenance = MachineSideProvenance::Reconstructed {
            from_opcode: "ADD.x".into(),
            arity: 2,
        };
        changes.push(next);
        for change in changes {
            let other = render_original_i128_goal(&change).unwrap();
            assert_eq!(original.expected_goal(), other.expected_goal());
            assert_ne!(
                original.original_binding_sha256(),
                other.original_binding_sha256()
            );
        }
        let mut next = row.clone();
        next.inputs.swap(0, 1);
        changed(&original, next);
    }

    #[test]
    fn binding_is_independent_of_pointer_sharing_without_losing_occurrences() {
        let sum = || E::var("a", 64).bvadd(E::var("b", 64));
        let shared = Arc::new(sum());
        let product = E::BvMul {
            lhs: shared.clone(),
            rhs: shared,
            width: 64,
        };
        let left = fixture(flag(product.eq_expr(E::bv_const(0, 64))), E::bv_const(0, 1));
        let right = fixture(
            flag(sum().bvmul(sum()).eq_expr(E::bv_const(0, 64))),
            E::bv_const(0, 1),
        );
        let a = render_original_i128_goal(&left).unwrap();
        let b = render_original_i128_goal(&right).unwrap();
        assert_eq!(a.original_binding_bytes(), b.original_binding_bytes());
        assert_eq!(a.expected_goal(), b.expected_goal());
        assert!(a.stats().distinct_nodes < b.stats().distinct_nodes);
        assert_eq!(a.stats().expanded_nodes, b.stats().expanded_nodes);
    }

    #[test]
    fn depth_dag_expansion_and_payload_limits_decline_before_unbounded_work() {
        let mut deep = E::BoolConst(false);
        for _ in 0..MAX_DEPTH {
            deep = E::Not {
                operand: Arc::new(deep),
            };
        }
        assert!(matches!(
            render_original_i128_goal(&fixture(flag(deep), E::bv_const(0, 1))),
            Err(ReflectionRefusal::Budget(_))
        ));
        let mut dag = E::var("a", 64);
        for _ in 0..19 {
            let node = Arc::new(dag);
            dag = E::BvAdd {
                lhs: node.clone(),
                rhs: node,
                width: 64,
            };
        }
        assert!(matches!(
            render_original_i128_goal(&fixture(
                flag(dag.eq_expr(E::bv_const(0, 64))),
                E::bv_const(0, 1)
            )),
            Err(ReflectionRefusal::Budget(_))
        ));
        let mut row = basic();
        row.name = "x".repeat(MAX_STRING_BYTES + 1);
        assert!(matches!(
            render_original_i128_goal(&row),
            Err(ReflectionRefusal::Budget(_))
        ));
    }
}
