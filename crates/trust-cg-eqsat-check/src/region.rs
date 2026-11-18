// trust-cg-eqsat-check/src/region.rs - checker of Tier S region derivations (PKG-U4)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The region check of docs/eqsat-tier-s.md (section 7).
//!
//! [`check_region`] accepts an (input region, output region, derivation)
//! triple only if every item of section 7 holds, read with this crate's own
//! region decoder and the same term table, rule registry and proof replay
//! as the function check. It shares no code with the engine.
//!
//! What an acceptance establishes, and what it does not:
//! * every root of the output, and the operand of every order-free node the
//!   output keeps, carries the input's term or a term a replayed proof
//!   concludes from it (equal values, or a refinement read forward);
//! * no proof reads an order-free node backwards, so no pinned reduction is
//!   rewritten through one, and every order-free node is either kept as the
//!   one node it was or implemented at **one order** of its family, never
//!   both and never at two orders;
//! * no term of the output or of the derivation names a pinned reduction
//!   at an order and type the input region does not name (on a term it
//!   reaches, or in the family of an order-free node of that type);
//! * the premises are the registry's rule statements (stated, **not
//!   proved**, until PKG-U2 attaches discharge records), this crate's
//!   reading of the operators (docs/eqsat-tier-e.md section 3), that every
//!   declared leaf is a defined value (the region says so; binding a region
//!   to a function body, and with it that premise, is PKG-U3), that an
//!   order-free node's family holds only orders that implement it, and that
//!   a pinned reduction at an order and type the input names is a total
//!   function of its operand's value (the region says both; PKG-U15 states
//!   the contract in trust-ir);
//! * the checker is Rust, so an accepted region is at most `Trusted`.
//!
//! What "one order" does not say: the check is about values. A derivation
//! may rewrite the operand under a pinned reduction after the `Impl` step,
//! so an accepted output can compute the implementation of one order-free
//! node as two nodes with equal values (same order, operands a proof
//! relates). By the last premise the two are one value, which is what the
//! source computed once. That the output computes it once is a property of
//! the engine's extractor (one option per class), not of an acceptance;
//! [`RegionVerdict::pinned_added`] counts the pinned reductions the output
//! adds, for a caller that wants to refuse more than one per implemented
//! node.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::decode::{self, RawProof, RawTerm, Reader, Tier};
use crate::reader::term_rejection;
use crate::registry::Registry;
use crate::rejection::{Body, Rejection, TermSite};
use crate::replay::{self, OrderFreeNode, OrderFreeTable};
use crate::terms::{Interner, Leaf, LeafInfo, Node, TermId};
use crate::types::{Ctx, OpDesc, Sty};

const REGION_MAGIC: &[u8; 8] = b"TCGEQREG";
const REGION_VERSION: u32 = 1;

/// What an accepted region check established.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegionVerdict {
    /// The derivation's claims.
    pub claims: usize,
    /// The derivation's proof steps, all replayed.
    pub proof_steps: usize,
    /// The rules the derivation names, sorted by name.
    pub rules_used: Vec<String>,
    /// Roots compared.
    pub roots: usize,
    /// Roots whose output term differs from the input term.
    pub changed_roots: usize,
    /// Order-free nodes the output keeps.
    pub order_free_kept: usize,
    /// Order-free nodes the derivation implements by a pinned reduction.
    pub order_free_implemented: usize,
    /// Pinned-reduction terms the output reaches and the input does not
    /// (module docs: more than `order_free_implemented` means one node's
    /// implementation is computed as several nodes of equal value).
    pub pinned_added: usize,
}

/// Why the region check refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RegionRejection {
    /// A region's bytes are not a canonical, well-typed version-1 region
    /// (section 3).
    MalformedRegion { body: Body, detail: String },
    /// The two regions differ in name, pointer width, declared leaves or
    /// number of roots.
    RegionMismatch { detail: String },
    /// The derivation is refused by the decoder or the replay (a version
    /// other than 2, a non-canonical encoding, an ill-typed term, an
    /// unknown rule, a step that does not fit).
    Derivation(Rejection),
    /// A root's terms differ and no claim concludes the pair.
    RootUnjustified {
        root: usize,
        input_term: String,
        output_term: String,
    },
    /// The operand of an order-free node the output keeps differs from the
    /// input's and no claim concludes the pair.
    OperandUnjustified {
        leaf: String,
        input_term: String,
        output_term: String,
    },
    /// A claim justifies no root or kept operand whose terms differ, or
    /// repeats another claim's conclusion.
    ClaimMismatch { claim: usize, detail: String },
    /// The output's order-free table names a node the input does not have,
    /// or gives one another family.
    OrderFreeChanged { leaf: String, detail: String },
    /// The output reads the result of an order-free node of the input but
    /// has no such node.
    OrderFreeDropped { leaf: String },
    /// A proof takes a pinned reduction (or anything else) to an order-free
    /// node: it reverses an `Impl` step, which only reads from the
    /// order-free node to the reduction that implements it. This is the
    /// derivation that rewrites a pinned reduction through an order-free
    /// node over the same operand.
    PinnedThroughOrderFree { proof: usize, leaf: String },
    /// An order-free node is elaborated at two sites: the derivation
    /// implements it at two orders, or implements it while the output still
    /// reads it. The source evaluates the node once, at one order. (Two
    /// reductions at the same order over operands a proof relates are one
    /// value and are not this; module docs.)
    OrderFreeAtTwoSites { leaf: String, detail: String },
    /// A term of the output or of the derivation is a pinned reduction at
    /// an order and type the input region does not name: no term the input
    /// reaches is pinned at it and no order-free node of that type has it
    /// in its family. Nothing says such a reduction is defined.
    PinnedOrderIntroduced {
        order: u32,
        ty: &'static str,
        term: String,
    },
}

impl RegionRejection {
    /// A stable snake_case name per variant (a derivation refusal keeps the
    /// name the function check gives it).
    pub fn class(&self) -> &'static str {
        match self {
            RegionRejection::MalformedRegion { .. } => "malformed_region",
            RegionRejection::RegionMismatch { .. } => "region_mismatch",
            RegionRejection::Derivation(rejection) => rejection.class(),
            RegionRejection::RootUnjustified { .. } => "root_unjustified",
            RegionRejection::OperandUnjustified { .. } => "operand_unjustified",
            RegionRejection::ClaimMismatch { .. } => "claim_mismatch",
            RegionRejection::OrderFreeChanged { .. } => "order_free_changed",
            RegionRejection::OrderFreeDropped { .. } => "order_free_dropped",
            RegionRejection::PinnedThroughOrderFree { .. } => "pinned_through_order_free",
            RegionRejection::OrderFreeAtTwoSites { .. } => "order_free_at_two_sites",
            RegionRejection::PinnedOrderIntroduced { .. } => "pinned_order_introduced",
        }
    }
}

impl fmt::Display for RegionRejection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let RegionRejection::Derivation(rejection) = self {
            return write!(f, "{rejection}");
        }
        write!(f, "{}: ", self.class())?;
        match self {
            RegionRejection::MalformedRegion { body, detail } => {
                write!(f, "{body} region: {detail}")
            }
            RegionRejection::RegionMismatch { detail } => f.write_str(detail),
            RegionRejection::Derivation(_) => Ok(()),
            RegionRejection::RootUnjustified {
                root,
                input_term,
                output_term,
            } => write!(
                f,
                "root {root}: input term {input_term} and output term {output_term} differ and no claim concludes them"
            ),
            RegionRejection::OperandUnjustified {
                leaf,
                input_term,
                output_term,
            } => write!(
                f,
                "operand of the order-free node {leaf}: input term {input_term} and output term {output_term} differ and no claim concludes them"
            ),
            RegionRejection::ClaimMismatch { claim, detail } => {
                write!(f, "claim {claim}: {detail}")
            }
            RegionRejection::OrderFreeChanged { leaf, detail } => {
                write!(f, "order-free node {leaf}: {detail}")
            }
            RegionRejection::OrderFreeDropped { leaf } => write!(
                f,
                "the output reads {leaf}, the result of an order-free node it does not have"
            ),
            RegionRejection::PinnedThroughOrderFree { proof, leaf } => write!(
                f,
                "proof {proof} reverses the implementation of the order-free node {leaf}"
            ),
            RegionRejection::OrderFreeAtTwoSites { leaf, detail } => {
                write!(f, "order-free node {leaf}: {detail}")
            }
            RegionRejection::PinnedOrderIntroduced { order, ty, term } => write!(
                f,
                "{term} is pinned at order {order} of {ty}, which the input region does not name"
            ),
        }
    }
}

impl std::error::Error for RegionRejection {}

/// One order-free entry as decoded: term indices into the region's table.
struct RawFree {
    leaf: u32,
    operand: u32,
    orders: Vec<u32>,
}

/// A decoded region (section 3), syntax only.
struct RawRegion {
    name: String,
    pointer_bits: u32,
    leaves: Vec<(Leaf, Sty)>,
    terms: Vec<RawTerm>,
    order_free: Vec<RawFree>,
    roots: Vec<u32>,
}

fn malformed(body: Body, detail: impl Into<String>) -> RegionRejection {
    RegionRejection::MalformedRegion {
        body,
        detail: detail.into(),
    }
}

fn decode_region(bytes: &[u8], body: Body) -> Result<RawRegion, RegionRejection> {
    let bad = |rejection: Rejection| malformed(body, rejection.to_string());
    let mut r = Reader::new(bytes, Tier::S);
    if r.take(8).map_err(bad)? != REGION_MAGIC {
        return Err(malformed(body, "bad magic (expected TCGEQREG)"));
    }
    let version = r.u32().map_err(bad)?;
    if version != REGION_VERSION {
        return Err(malformed(body, format!("bad region version {version}")));
    }
    let name = r.str().map_err(bad)?;
    let pointer_bits = r.u32().map_err(bad)?;

    let leaf_count = r.u32().map_err(bad)?;
    let mut leaves: Vec<(Leaf, Sty)> = Vec::new();
    for i in 0..leaf_count as usize {
        let leaf = match r.u8().map_err(bad)? {
            0x01 => Leaf::Param {
                block: r.u32().map_err(bad)?,
                index: r.u32().map_err(bad)?,
            },
            0x02 => Leaf::Result {
                block: r.u32().map_err(bad)?,
                ordinal: r.u32().map_err(bad)?,
                index: r.u32().map_err(bad)?,
            },
            tag => return Err(malformed(body, format!("bad leaf tag {tag:#04x}"))),
        };
        let ty = r.ty("leaf type").map_err(bad)?;
        if let Some((previous, _)) = leaves.last()
            && *previous >= leaf
        {
            return Err(malformed(
                body,
                format!("leaf {i} is not after the leaf before it"),
            ));
        }
        leaves.push((leaf, ty));
    }

    let term_count = r.u32().map_err(bad)?;
    let mut terms: Vec<RawTerm> = Vec::new();
    for i in 0..term_count as usize {
        terms.push(r.term(i).map_err(bad)?);
    }
    let term_index = |r: &mut Reader<'_>, what: &str| -> Result<u32, RegionRejection> {
        let index = r.u32().map_err(bad)?;
        if index as usize >= terms.len() {
            return Err(malformed(body, format!("{what} names no term ({index})")));
        }
        Ok(index)
    };

    let free_count = r.u32().map_err(bad)?;
    let mut order_free: Vec<RawFree> = Vec::new();
    for i in 0..free_count as usize {
        let leaf = term_index(&mut r, "an order-free result")?;
        let operand = term_index(&mut r, "an order-free operand")?;
        let order_count = r.u32().map_err(bad)?;
        let mut orders: Vec<u32> = Vec::new();
        for _ in 0..order_count {
            let order = r.u32().map_err(bad)?;
            if orders.last().is_some_and(|previous| *previous >= order) {
                return Err(malformed(
                    body,
                    format!("the family of order-free node {i} is not strictly increasing"),
                ));
            }
            orders.push(order);
        }
        if orders.is_empty() {
            return Err(malformed(
                body,
                format!("the family of order-free node {i} is empty"),
            ));
        }
        order_free.push(RawFree {
            leaf,
            operand,
            orders,
        });
    }

    let root_count = r.u32().map_err(bad)?;
    let mut roots: Vec<u32> = Vec::new();
    for _ in 0..root_count {
        roots.push(term_index(&mut r, "a root")?);
    }
    r.finish().map_err(bad)?;

    // Canonical: no two equal term entries, every term reachable.
    let mut seen = BTreeSet::new();
    for (i, term) in terms.iter().enumerate() {
        if !seen.insert(term) {
            return Err(malformed(
                body,
                format!("term {i} repeats an earlier entry"),
            ));
        }
    }
    let mut live = vec![false; terms.len()];
    for root in &roots {
        live[*root as usize] = true;
    }
    for entry in &order_free {
        live[entry.leaf as usize] = true;
        live[entry.operand as usize] = true;
    }
    // References point backwards, so one descending sweep closes them.
    for i in (0..terms.len()).rev() {
        if live[i]
            && let RawTerm::Op { args, .. } = &terms[i]
        {
            for arg in args {
                live[*arg as usize] = true;
            }
        }
    }
    if let Some(i) = live.iter().position(|l| !l) {
        return Err(malformed(
            body,
            format!("term {i} is reachable from no root and no order-free node"),
        ));
    }

    Ok(RawRegion {
        name,
        pointer_bits,
        leaves,
        terms,
        order_free,
        roots,
    })
}

/// A region's terms in the shared interner.
struct Typed {
    roots: Vec<TermId>,
    /// The order-free nodes by result leaf, with the table position.
    order_free: BTreeMap<TermId, (usize, OrderFreeNode)>,
}

/// Every term `starts` reach, themselves included.
fn reach(interner: &Interner, starts: impl IntoIterator<Item = TermId>) -> BTreeSet<TermId> {
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = starts.into_iter().collect();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let Some(Node::Op(_, args)) = interner.node(term) {
            stack.extend(args.iter().copied());
        }
    }
    seen
}

fn intern_region(
    raw: &RawRegion,
    interner: &mut Interner,
    body: Body,
) -> Result<Typed, RegionRejection> {
    let mut ids: Vec<TermId> = Vec::with_capacity(raw.terms.len());
    for (i, term) in raw.terms.iter().enumerate() {
        let id = match term {
            RawTerm::Param { block, index } => interner.leaf(Leaf::Param {
                block: *block,
                index: *index,
            }),
            RawTerm::Result {
                block,
                ordinal,
                index,
            } => interner.leaf(Leaf::Result {
                block: *block,
                ordinal: *ordinal,
                index: *index,
            }),
            RawTerm::Const { ty, residue } => interner.constant(*ty, *residue),
            RawTerm::Op { desc, args } => {
                let mapped: Vec<TermId> = args.iter().map(|a| ids[*a as usize]).collect();
                interner.op(*desc, &mapped)
            }
        }
        .map_err(|e| malformed(body, term_rejection(e, TermSite::TermTable(i)).to_string()))?;
        ids.push(id);
    }

    let mut order_free: BTreeMap<TermId, (usize, OrderFreeNode)> = BTreeMap::new();
    let mut results: Vec<TermId> = Vec::new();
    for (k, entry) in raw.order_free.iter().enumerate() {
        let (leaf, operand) = (ids[entry.leaf as usize], ids[entry.operand as usize]);
        if !matches!(interner.node(leaf), Some(Node::Leaf(_))) {
            return Err(malformed(
                body,
                format!("the result of order-free node {k} is not a leaf"),
            ));
        }
        let ty = interner.ty(leaf);
        if ty.is_none_or(Sty::is_bool) || interner.ty(operand) != ty {
            return Err(malformed(
                body,
                format!(
                    "order-free node {k} needs one integer type for its operand and its result"
                ),
            ));
        }
        if order_free.contains_key(&leaf) {
            return Err(malformed(
                body,
                format!("order-free node {k} repeats the result of an earlier node"),
            ));
        }
        results.push(leaf);
        order_free.insert(
            leaf,
            (
                k,
                OrderFreeNode {
                    operand,
                    orders: entry.orders.clone(),
                },
            ),
        );
    }
    // Dependency order: an operand reads only the results of earlier nodes,
    // so no order-free node feeds itself.
    for (k, leaf) in results.iter().enumerate() {
        let Some((_, node)) = order_free.get(leaf) else {
            continue;
        };
        let under = reach(interner, [node.operand]);
        if results[k..].iter().any(|later| under.contains(later)) {
            return Err(malformed(
                body,
                format!(
                    "the operand of order-free node {k} reads its own result or a later node's"
                ),
            ));
        }
    }

    Ok(Typed {
        roots: raw.roots.iter().map(|r| ids[*r as usize]).collect(),
        order_free,
    })
}

/// The leaf under proof `start` whose `Impl` step it is built on, if any.
fn impl_under(proofs: &[RawProof], start: u32) -> Option<u32> {
    let mut seen = BTreeSet::new();
    let mut stack = vec![start];
    while let Some(p) = stack.pop() {
        if !seen.insert(p) {
            continue;
        }
        match proofs.get(p as usize)? {
            RawProof::Impl { leaf, .. } => return Some(*leaf),
            RawProof::Refl(_) | RawProof::Rule { .. } => {}
            RawProof::Sym(q) => stack.push(*q),
            RawProof::Trans(q, r) => {
                stack.push(*q);
                stack.push(*r);
            }
            RawProof::Congr(_, qs) => stack.extend(qs.iter().copied()),
        }
    }
    None
}

/// What a claim may justify: a root, or the operand of a kept order-free
/// node.
enum Site {
    Root(usize),
    Operand(TermId),
}

/// Checks that the region `output` is a sound rewrite of the region `input`
/// justified by `derivation` over `registry` (docs/eqsat-tier-s.md section
/// 7). The three byte strings are the engine's `Region::encode` of each
/// region and its version-2 derivation.
pub fn check_region(
    input: &[u8],
    output: &[u8],
    derivation: &[u8],
    registry: &Registry,
) -> Result<RegionVerdict, RegionRejection> {
    // Item 1: both regions decode canonically and agree on what they are.
    let raw_in = decode_region(input, Body::Input)?;
    let raw_out = decode_region(output, Body::Output)?;
    let mismatch = |detail: &str| {
        Err(RegionRejection::RegionMismatch {
            detail: detail.to_owned(),
        })
    };
    if raw_in.name != raw_out.name {
        return mismatch("the regions have different names");
    }
    if raw_in.pointer_bits != raw_out.pointer_bits {
        return mismatch("the regions have different pointer widths");
    }
    if raw_in.leaves != raw_out.leaves {
        return mismatch("the regions declare different leaves");
    }
    if raw_in.roots.len() != raw_out.roots.len() {
        return mismatch("the regions have different numbers of roots");
    }

    // Item 2: both regions are well typed over the declared leaves.
    let ctx = Ctx {
        pointer_bits: raw_in.pointer_bits,
    };
    let mut leaves: BTreeMap<Leaf, LeafInfo> = BTreeMap::new();
    for (leaf, sty) in &raw_in.leaves {
        if ctx.width(*sty).is_none() {
            return Err(malformed(
                Body::Input,
                format!(
                    "leaf {leaf} has type {}, which has no width here",
                    sty.name()
                ),
            ));
        }
        leaves.insert(
            *leaf,
            LeafInfo {
                ty: sty.to_ir(),
                sty: Some(*sty),
                // The region's premise (module docs): every declared leaf is
                // a defined value.
                defined: true,
            },
        );
    }
    let mut interner = Interner::new(ctx, leaves);
    let typed_in = intern_region(&raw_in, &mut interner, Body::Input)?;
    let typed_out = intern_region(&raw_out, &mut interner, Body::Output)?;

    // Item 3: the output keeps a subset of the input's order-free nodes,
    // each with its family.
    for (leaf, (_, node)) in &typed_out.order_free {
        let changed = |detail: &str| RegionRejection::OrderFreeChanged {
            leaf: interner.render(*leaf),
            detail: detail.to_owned(),
        };
        match typed_in.order_free.get(leaf) {
            None => return Err(changed("the input has no such order-free node")),
            Some((_, before)) if before.orders != node.orders => {
                return Err(changed("the output gives it another family"));
            }
            Some(_) => {}
        }
    }

    // Item 4: the derivation decodes canonically and every proof replays.
    let d = decode::decode(derivation, Tier::S).map_err(RegionRejection::Derivation)?;
    if d.function != raw_in.name {
        return Err(RegionRejection::Derivation(
            Rejection::FunctionNameMismatch {
                derivation: d.function.clone(),
                function: raw_in.name.clone(),
            },
        ));
    }
    let table: OrderFreeTable = typed_in
        .order_free
        .iter()
        .map(|(leaf, (_, node))| (*leaf, node.clone()))
        .collect();
    let conclusions = match replay::replay(&d, registry, &mut interner, &table) {
        Ok(conclusions) => conclusions,
        // Item 5: an `Impl` step is never read backwards.
        Err(Rejection::SymOfRefines { proof }) => {
            let reversed = match d.proofs.get(proof) {
                Some(RawProof::Sym(inner)) => impl_under(&d.proofs, *inner),
                _ => None,
            };
            return Err(match reversed.and_then(|leaf| d.terms.get(leaf as usize)) {
                Some(RawTerm::Param { block, index }) => RegionRejection::PinnedThroughOrderFree {
                    proof,
                    leaf: Leaf::Param {
                        block: *block,
                        index: *index,
                    }
                    .to_string(),
                },
                Some(RawTerm::Result {
                    block,
                    ordinal,
                    index,
                }) => RegionRejection::PinnedThroughOrderFree {
                    proof,
                    leaf: Leaf::Result {
                        block: *block,
                        ordinal: *ordinal,
                        index: *index,
                    }
                    .to_string(),
                },
                _ => RegionRejection::Derivation(Rejection::SymOfRefines { proof }),
            });
        }
        Err(other) => return Err(RegionRejection::Derivation(other)),
    };

    // Item 6: every root and every kept operand is the input's term or is
    // concluded from it by a claim; every claim is used once.
    let mut by_pair: BTreeMap<(TermId, TermId), usize> = BTreeMap::new();
    for (ci, &p) in d.claims.iter().enumerate() {
        let c = conclusions[p as usize];
        if let Some(previous) = by_pair.insert((c.lhs, c.rhs), ci) {
            return Err(RegionRejection::ClaimMismatch {
                claim: ci,
                detail: format!("repeats the conclusion of claim {previous}"),
            });
        }
    }
    let mut sites: Vec<(Site, TermId, TermId)> = Vec::new();
    for (i, (a, b)) in typed_in.roots.iter().zip(&typed_out.roots).enumerate() {
        sites.push((Site::Root(i), *a, *b));
    }
    for (leaf, (_, node)) in &typed_out.order_free {
        if let Some((_, before)) = typed_in.order_free.get(leaf) {
            sites.push((Site::Operand(*leaf), before.operand, node.operand));
        }
    }
    let mut used = vec![false; d.claims.len()];
    let mut changed_roots = 0usize;
    for (site, a, b) in &sites {
        if a == b {
            continue;
        }
        if matches!(site, Site::Root(_)) {
            changed_roots += 1;
        }
        match by_pair.get(&(*a, *b)) {
            Some(&ci) => used[ci] = true,
            None => {
                let (input_term, output_term) = (interner.render(*a), interner.render(*b));
                return Err(match site {
                    Site::Root(root) => RegionRejection::RootUnjustified {
                        root: *root,
                        input_term,
                        output_term,
                    },
                    Site::Operand(leaf) => RegionRejection::OperandUnjustified {
                        leaf: interner.render(*leaf),
                        input_term,
                        output_term,
                    },
                });
            }
        }
    }
    if let Some(ci) = used.iter().position(|u| !u) {
        return Err(RegionRejection::ClaimMismatch {
            claim: ci,
            detail: "justifies no root and no kept operand whose terms differ".to_owned(),
        });
    }

    // Item 7: every order-free node is one node in the output, or is
    // implemented at one order, never both and never at two orders.
    let mut implemented: BTreeMap<TermId, BTreeSet<u32>> = BTreeMap::new();
    for (proof, conclusion) in d.proofs.iter().zip(&conclusions) {
        // An `Impl` step concludes `(its leaf, the pinned reduction)`.
        if let RawProof::Impl { order, .. } = proof {
            implemented
                .entry(conclusion.lhs)
                .or_default()
                .insert(*order);
        }
    }
    let read_by_output = reach(
        &interner,
        typed_out
            .roots
            .iter()
            .copied()
            .chain(typed_out.order_free.values().map(|(_, node)| node.operand))
            .chain(typed_out.order_free.keys().copied()),
    );
    for (leaf, orders) in &implemented {
        let two_sites = |detail: String| RegionRejection::OrderFreeAtTwoSites {
            leaf: interner.render(*leaf),
            detail,
        };
        if orders.len() > 1 {
            return Err(two_sites(format!(
                "the derivation implements it at the orders {orders:?}"
            )));
        }
        if read_by_output.contains(leaf) {
            return Err(two_sites(format!(
                "the derivation implements it at the order {orders:?} and the output still has it"
            )));
        }
    }
    for leaf in typed_in.order_free.keys() {
        if read_by_output.contains(leaf) && !typed_out.order_free.contains_key(leaf) {
            return Err(RegionRejection::OrderFreeDropped {
                leaf: interner.render(*leaf),
            });
        }
    }

    // Item 8: no term (of the regions, the derivation's table or a replayed
    // conclusion; the interner holds them all) is pinned at an order and
    // type the input does not name.
    let read_by_input = reach(
        &interner,
        typed_in
            .roots
            .iter()
            .copied()
            .chain(typed_in.order_free.values().map(|(_, node)| node.operand))
            .chain(typed_in.order_free.keys().copied()),
    );
    let pinned_at = |term: TermId| match interner.node(term) {
        Some(Node::Op(OpDesc::Pinned(order, ty), _)) => Some((*order, *ty)),
        _ => None,
    };
    let mut named: BTreeSet<(u32, Sty)> = read_by_input
        .iter()
        .filter_map(|term| pinned_at(*term))
        .collect();
    for (leaf, (_, node)) in &typed_in.order_free {
        if let Some(ty) = interner.ty(*leaf) {
            named.extend(node.orders.iter().map(|order| (*order, ty)));
        }
    }
    for term in 0..interner.len() {
        if let Some((order, ty)) = pinned_at(term)
            && !named.contains(&(order, ty))
        {
            return Err(RegionRejection::PinnedOrderIntroduced {
                order,
                ty: ty.name(),
                term: interner.render(term),
            });
        }
    }
    let pinned_added = read_by_output
        .iter()
        .filter(|term| pinned_at(**term).is_some() && !read_by_input.contains(*term))
        .count();

    Ok(RegionVerdict {
        claims: d.claims.len(),
        proof_steps: d.proofs.len(),
        rules_used: d.rules.iter().map(|(n, _)| n.clone()).collect(),
        roots: typed_in.roots.len(),
        changed_roots,
        order_free_kept: typed_out.order_free.len(),
        order_free_implemented: implemented.len(),
        pinned_added,
    })
}
