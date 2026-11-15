// trust-cg-eqsat-check/src/lib.rs - independent checker of trust-cg-eqsat derivations (PKG-U1)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The derivation checker of docs/eqsat-tier-e.md (section 8).
//!
//! [`check`] accepts an (input body, output body, derivation) triple only if
//! all five items of section 8 hold, read with this crate's own code: its own
//! eligibility test, dominator tree, graph/skeleton reader, rule-file parser,
//! byte decoder and proof replay. It shares no code with the engine
//! (`trust-cg-eqsat`) and depends on `trust-ir` only.
//!
//! What an acceptance establishes, and what it does not:
//! * the two bodies execute the same skeleton instructions, in the same
//!   blocks and order, with the same non-operand fields, and every skeleton
//!   operand of the output carries a term that is either the input's term or
//!   is concluded from it by a replayed proof (equal values, or a refinement
//!   in the forward direction);
//! * the proofs are only as good as the registry's rule statements, which
//!   are stated and **not proved** in PKG-U1 (PKG-U2 attaches discharge
//!   records), and as this crate's reading of trust-ir's semantics
//!   (sections 2 and 3);
//! * the checker is Rust, so a function it accepts is at most `Trusted`,
//!   never `Certified`.

#![forbid(unsafe_code)]

mod decode;
mod dom;
mod operands;
mod reader;
mod registry;
mod rejection;
mod replay;
mod semantics;
mod sensitive;
mod terms;
mod types;
mod validity;

use std::collections::BTreeMap;

use trust_ir::{Function, Module};

pub use registry::{Registry, RegistryError};
pub use rejection::{Body, DecodeError, NonCanonicalKind, Rejection, TermSite};
pub use terms::Leaf;

use reader::{Analysis, ValTerm};
use replay::Conclusion;
use terms::{Interner, TermId};
use types::Ctx;

/// What an accepted check established.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Verdict {
    /// The derivation's claims (one per distinct changed operand pair).
    pub claims: usize,
    /// The derivation's proof steps, all replayed.
    pub proof_steps: usize,
    /// The rules the derivation names (its rule table), sorted by name.
    pub rules_used: Vec<String>,
    /// Skeleton operands compared (input body, all blocks).
    pub skeleton_operands: usize,
    /// Skeleton operands whose output term differs from the input term.
    pub changed_operands: usize,
}

/// Checks that `output` is a sound rewrite of `input` justified by
/// `derivation` over `registry` (docs/eqsat-tier-e.md section 8).
pub fn check(
    module: &Module,
    input: &Function,
    output: &Function,
    derivation: &[u8],
    registry: &Registry,
) -> Result<Verdict, Rejection> {
    let ctx = Ctx {
        pointer_bits: module.pointer_bits(),
    };

    // Section 8 item 2: refinement verdicts are decided by fact propagation
    // over the defining instructions, which the checker does not model.
    sensitive::check(module)?;

    // Item 1 (and the eligibility half of item 2's precondition).
    let ia = reader::analyze(module, input, Body::Input, ctx)?;
    let oa = reader::analyze(module, output, Body::Output, ctx)?;
    compare_fields(input, output)?;
    compare_blocks(input, output)?;

    // Item 3: skeletons.
    let pairs = compare_skeletons(module, &ia, &oa)?;

    // Item 2, last clause: operands the validator reads through their
    // defining instruction (section 2.5 "Literal-sensitive operands", and the
    // exhaustive-switch selector trace).
    check_definition_sensitive(module, &ia, &oa, &pairs)?;

    if ia.leaves != oa.leaves {
        let detail = first_leaf_difference(&ia, &oa);
        return Err(Rejection::SkeletonInstructionMismatch {
            block: detail.0,
            ordinal: detail.1,
            input_inst: 0,
            output_inst: 0,
            detail: detail.2,
        });
    }

    // Terms of both bodies, in one interner over the input's leaves.
    let mut interner = Interner::new(ctx, ia.leaves.clone());
    let in_terms = reader::terms(&ia, &mut interner, Body::Input)?;
    let out_terms = reader::terms(&oa, &mut interner, Body::Output)?;

    // Item 5: decode and replay.
    let d = decode::decode(derivation)?;
    if d.function != input.name {
        return Err(Rejection::FunctionNameMismatch {
            derivation: d.function.clone(),
            function: input.name.clone(),
        });
    }
    let conclusions = replay::replay(&d, registry, &mut interner)?;

    // Item 4: every skeleton operand.
    let (skeleton_operands, changed_operands) = justify_operands(
        &pairs,
        &in_terms,
        &out_terms,
        &d.claims,
        &conclusions,
        &interner,
    )?;

    Ok(Verdict {
        claims: d.claims.len(),
        proof_steps: d.proofs.len(),
        rules_used: d.rules.iter().map(|(n, _)| n.clone()).collect(),
        skeleton_operands,
        changed_operands,
    })
}

/// Every `Function` field except `blocks` and `value_names` must agree.
fn compare_fields(a: &Function, b: &Function) -> Result<(), Rejection> {
    macro_rules! same {
        ($($field:ident),*) => {
            $(
                if a.$field != b.$field {
                    return Err(Rejection::FunctionFieldMismatch { field: stringify!($field) });
                }
            )*
        };
    }
    same!(
        id,
        name,
        ty,
        entry,
        proofs,
        calling_conv,
        linkage,
        attrs,
        summary,
        producer,
        scopes,
        source_provenance,
        body_gate,
        display_path,
        section,
        visibility,
        retained
    );
    // Catch-all: any field not named above (for example one a later trust-ir
    // adds) still has to agree.
    let strip = |f: &Function| {
        let mut f = f.clone();
        f.blocks = Vec::new();
        f.value_names = None;
        f
    };
    if strip(a) != strip(b) {
        return Err(Rejection::FunctionFieldMismatch { field: "other" });
    }
    Ok(())
}

/// Same blocks: count, ids, order, parameter count and types. Parameter
/// `ValueId`s may differ (leaves are positional).
fn compare_blocks(a: &Function, b: &Function) -> Result<(), Rejection> {
    if a.blocks.len() != b.blocks.len() {
        return Err(Rejection::BlockShapeMismatch {
            block_index: a.blocks.len().min(b.blocks.len()),
            detail: format!(
                "input has {} blocks, output has {}",
                a.blocks.len(),
                b.blocks.len()
            ),
        });
    }
    for (i, (x, y)) in a.blocks.iter().zip(&b.blocks).enumerate() {
        if x.id != y.id {
            return Err(Rejection::BlockShapeMismatch {
                block_index: i,
                detail: format!("input bb{} vs output bb{}", x.id.0, y.id.0),
            });
        }
        let xt: Vec<_> = x.params.iter().map(|(_, t)| t).collect();
        let yt: Vec<_> = y.params.iter().map(|(_, t)| t).collect();
        if xt != yt {
            return Err(Rejection::BlockShapeMismatch {
                block_index: i,
                detail: format!("bb{}: parameter types differ", x.id.0),
            });
        }
    }
    Ok(())
}

/// One matched skeleton instruction: block id and index (the same in both
/// bodies), ordinal, its instruction index in each body, input and output
/// operands.
struct SkeletonPair {
    block: u32,
    block_index: usize,
    ordinal: usize,
    input_inst: usize,
    output_inst: usize,
    input_ops: Vec<trust_ir::ValueId>,
    output_ops: Vec<trust_ir::ValueId>,
}

fn compare_skeletons(
    module: &Module,
    ia: &Analysis<'_>,
    oa: &Analysis<'_>,
) -> Result<Vec<SkeletonPair>, Rejection> {
    let mut pairs = Vec::new();
    for (bi, (bin, bout)) in ia.func.blocks.iter().zip(&oa.func.blocks).enumerate() {
        let (si, so) = (&ia.skeleton[bi], &oa.skeleton[bi]);
        if si.len() != so.len() {
            return Err(Rejection::SkeletonCountMismatch {
                block: bin.id.0,
                input: si.len(),
                output: so.len(),
            });
        }
        for (k, (&pi, &po)) in si.iter().zip(so).enumerate() {
            let (ni, no) = (&bin.body[pi], &bout.body[po]);
            let mismatch = |detail: &str| Rejection::SkeletonInstructionMismatch {
                block: bin.id.0,
                ordinal: k,
                input_inst: pi,
                output_inst: po,
                detail: detail.to_owned(),
            };
            let input_ops = operands::operands(&ni.inst);
            let output_ops = operands::operands(&no.inst);
            if input_ops.len() != output_ops.len() {
                return Err(mismatch("different number of value operands"));
            }
            let mut replaced = no.inst.clone();
            if operands::set_operands(&mut replaced, &input_ops).is_none() {
                return Err(mismatch(
                    "the output's value operands cannot be overwritten positionally",
                ));
            }
            if replaced != ni.inst {
                return Err(mismatch(
                    "the instruction differs beyond its value operands (kind, types, attributes, targets or sites)",
                ));
            }
            if ni.results.len() != no.results.len() {
                return Err(mismatch("different result count"));
            }
            if ni.result_tys(module) != no.result_tys(module) {
                return Err(mismatch("different result types"));
            }
            if ni.span != no.span {
                return Err(mismatch("different span"));
            }
            if ni.scope != no.scope {
                return Err(mismatch("different scope"));
            }
            if ni.proofs != no.proofs || ni.proof_context != no.proof_context {
                return Err(mismatch("different proofs or proof_context"));
            }
            // Catch-all over every node field: the output node with the
            // input's operands and result ids must equal the input node.
            let mut node = no.clone();
            node.inst = replaced;
            node.results = ni.results.clone();
            if &node != ni {
                return Err(mismatch("the instruction node differs"));
            }
            pairs.push(SkeletonPair {
                block: bin.id.0,
                block_index: bi,
                ordinal: k,
                input_inst: pi,
                output_inst: po,
                input_ops,
                output_ops,
            });
        }
    }
    Ok(pairs)
}

/// Holds every skeleton pair to the rules of [`sensitive`]. The pair's
/// input instruction names the kind and flags of both (item 3).
fn check_definition_sensitive(
    module: &Module,
    ia: &Analysis<'_>,
    oa: &Analysis<'_>,
    pairs: &[SkeletonPair],
) -> Result<(), Rejection> {
    let (ind, outd) = (
        sensitive::Defs::of(module, ia),
        sensitive::Defs::of(module, oa),
    );
    for pair in pairs {
        let Some(ni) = ia
            .func
            .blocks
            .get(pair.block_index)
            .and_then(|b| b.body.get(pair.input_inst))
        else {
            return Err(Rejection::SkeletonInstructionMismatch {
                block: pair.block,
                ordinal: pair.ordinal,
                input_inst: pair.input_inst,
                output_inst: pair.output_inst,
                detail: "the skeleton pair names no input instruction".to_owned(),
            });
        };
        let site = sensitive::Site {
            block: pair.block,
            ordinal: pair.ordinal,
            input: &ni.inst,
            input_ops: &pair.input_ops,
            output_ops: &pair.output_ops,
        };
        sensitive::check_literals(&site, &ind, &outd)?;
        sensitive::check_tag_traces(&site, &ind, &outd)?;
        sensitive::check_tag_guards(&site, &ind, &outd)?;
    }
    Ok(())
}

fn first_leaf_difference(ia: &Analysis<'_>, oa: &Analysis<'_>) -> (u32, usize, String) {
    for (leaf, info) in &ia.leaves {
        if oa.leaves.get(leaf) != Some(info) {
            let (block, ordinal) = match leaf {
                Leaf::Param { block, .. } => (*block, 0),
                Leaf::Result { block, ordinal, .. } => (*block, *ordinal as usize),
            };
            return (
                block,
                ordinal,
                format!("leaf {leaf} differs between the bodies"),
            );
        }
    }
    (0, 0, "the output has a leaf the input does not".to_owned())
}

fn render(t: Option<&ValTerm>, interner: &Interner) -> String {
    match t {
        Some(ValTerm::Term(id)) => interner.render(*id),
        Some(ValTerm::Opaque(leaf)) => leaf.to_string(),
        None => "<no term>".to_owned(),
    }
}

fn justify_operands(
    pairs: &[SkeletonPair],
    in_terms: &BTreeMap<trust_ir::ValueId, ValTerm>,
    out_terms: &BTreeMap<trust_ir::ValueId, ValTerm>,
    claims: &[u32],
    conclusions: &[Conclusion],
    interner: &Interner,
) -> Result<(usize, usize), Rejection> {
    let mut by_pair: BTreeMap<(TermId, TermId), usize> = BTreeMap::new();
    let mut by_lhs: BTreeMap<TermId, usize> = BTreeMap::new();
    for (ci, &p) in claims.iter().enumerate() {
        let c = conclusions[p as usize];
        if let Some(&prev) = by_pair.get(&(c.lhs, c.rhs)) {
            return Err(Rejection::ClaimMismatch {
                claim: ci,
                proof: p,
                detail: format!("repeats the conclusion of claim {prev}"),
            });
        }
        by_pair.insert((c.lhs, c.rhs), ci);
        by_lhs.entry(c.lhs).or_insert(ci);
    }
    let mut used = vec![false; claims.len()];
    let (mut total, mut changed) = (0usize, 0usize);
    for pair in pairs {
        for (operand, (vi, vo)) in pair.input_ops.iter().zip(&pair.output_ops).enumerate() {
            total += 1;
            let (ti, to) = (in_terms.get(vi), out_terms.get(vo));
            if ti.is_some() && ti == to {
                continue;
            }
            changed += 1;
            if let (Some(ValTerm::Term(a)), Some(ValTerm::Term(b))) = (ti, to) {
                if let Some(&ci) = by_pair.get(&(*a, *b)) {
                    used[ci] = true;
                    continue;
                }
                if let Some(&ci) = by_lhs.get(a) {
                    let c = conclusions[claims[ci] as usize];
                    return Err(Rejection::ConclusionMismatch {
                        block: pair.block,
                        ordinal: pair.ordinal,
                        operand,
                        claim: ci,
                        expected: interner.render(*b),
                        concluded: interner.render(c.rhs),
                    });
                }
            }
            return Err(Rejection::OperandUnjustified {
                block: pair.block,
                ordinal: pair.ordinal,
                operand,
                input_term: render(ti, interner),
                output_term: render(to, interner),
            });
        }
    }
    if let Some(ci) = used.iter().position(|u| !u) {
        return Err(Rejection::ClaimMismatch {
            claim: ci,
            proof: claims[ci],
            detail: "justifies no skeleton operand whose terms differ".to_owned(),
        });
    }
    Ok((total, changed))
}
