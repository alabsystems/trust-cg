// crates/trust-cg-eqsat/src/selector.rs - the selector trace of an exhaustive switch, kept as in the input
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The selector trace of a `Switch` flagged `exhaustive_enum_unreachable`
//! (docs/eqsat-tier-e.md section 2.5, "Switch selectors").
//!
//! trust-ir-build (`validate/exhaustive_switch.rs`, `selector_enum`) follows
//! such a selector through `Copy`, `zext`, `sext` and equal-width `bitcast`
//! to `ExtractField { field: 0 }` of an enum, and only when that trace
//! resolves holds the case set to the enum's discriminants. A graph rewrite on
//! the trace can make it resolve where the input's did not (`add (zext tag),
//! 0` to `zext tag` exposes a tag whose case set may be incomplete) or change
//! the casts it resolves through, so an output the validator refuses could be
//! built from a valid input.
//!
//! **Invariant.** For every flagged `Switch` of a body the engine returns, the
//! selector trace (this module's [`traces`]: the definitions reached from the
//! selector by following `Copy` and every `zext`, `sext` and `bitcast`
//! whatever its widths, a superset of the validator's steps, up to the first
//! other definition, the trace's *end*) is the input's: the same casts and the
//! same end, as the same instructions (kind and every field but the value
//! operands, results included), in the same order, each cast's operand being
//! the next trace member up to copies. Only copies on the trace may be removed;
//! both the validator and the checker see through them. The end's own operands
//! may change (a rewrite there cannot make the trace resolve: it stops at the
//! end in both bodies), each justified by a claim.
//!
//! How it is held: every graph instruction on a trace is *pinned*
//! ([`members`]; `to_graph` classifies it `InstClass::Pinned`). A pinned
//! instruction stays in the graph like any graph instruction (other uses of its
//! value are still rewritten), and it is also emitted in place, with its
//! operands remapped like a skeleton instruction's; a skeleton or pinned use of
//! a value whose root is pinned reads the pinned instruction itself. Skeleton
//! instructions on a trace (a cast of a maybe-poison operand, the
//! `ExtractField`) are kept anyway. `lib.rs` re-reads the output and refuses
//! (fail-closed decline) a body whose traces differ from the input's.

use std::collections::BTreeMap;

use trust_ir::{CastOp, Function, Inst, ValueId};

use crate::remap;

/// One member of a selector trace.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Member {
    /// An instruction on the trace (a cast, or the end): its first result
    /// and the instruction with every value operand replaced by `ValueId(0)`.
    Inst { value: ValueId, inst: Inst },
    /// The trace ends at a value no instruction defines (a block parameter).
    Open(ValueId),
}

/// Every instruction of `function` by the values it defines (the first
/// definition; the reader refuses a value defined twice).
fn definitions(function: &Function) -> BTreeMap<ValueId, &Inst> {
    let mut defs = BTreeMap::new();
    for node in function.blocks.iter().flat_map(|block| &block.body) {
        for value in &node.results {
            defs.entry(*value).or_insert(&node.inst);
        }
    }
    defs
}

/// The trace of `selector`: the values of its non-copy members, outermost
/// first, each with its instruction (or `None` for the open end).
fn walk<'f>(
    defs: &BTreeMap<ValueId, &'f Inst>,
    selector: ValueId,
) -> Vec<(ValueId, Option<&'f Inst>)> {
    let mut members = Vec::new();
    let mut current = selector;
    // Each step moves to an operand's definition, so a well-formed body's
    // trace is at most as long as it has definitions; the bound stops a
    // (malformed) cycle.
    for _ in 0..=defs.len() {
        match defs.get(&current).copied() {
            None => {
                members.push((current, None));
                return members;
            }
            Some(Inst::Copy { operand, .. }) => current = *operand,
            Some(
                inst @ Inst::Cast {
                    op: CastOp::ZExt | CastOp::SExt | CastOp::Bitcast,
                    operand,
                    ..
                },
            ) => {
                members.push((current, Some(inst)));
                current = *operand;
            }
            Some(inst) => {
                members.push((current, Some(inst)));
                return members;
            }
        }
    }
    members
}

/// The selectors of the flagged switches of `function`, in body order.
fn flagged_selectors(function: &Function) -> impl Iterator<Item = ValueId> + '_ {
    function
        .blocks
        .iter()
        .flat_map(|block| &block.body)
        .filter_map(|node| match &node.inst {
            Inst::Switch {
                value,
                exhaustive_enum_unreachable: true,
                ..
            } => Some(*value),
            _ => None,
        })
}

/// The values defined by an instruction on the selector trace of a flagged
/// switch (the casts and the end; copies excluded).
pub(crate) fn members(function: &Function) -> Vec<ValueId> {
    let defs = definitions(function);
    let mut out = Vec::new();
    for selector in flagged_selectors(function) {
        for (value, inst) in walk(&defs, selector) {
            if inst.is_some() {
                out.push(value);
            }
        }
    }
    out.sort_unstable();
    out.dedup();
    out
}

/// The selector trace of every flagged switch of `function`, in body order,
/// as the invariant compares them.
pub(crate) fn traces(function: &Function) -> Vec<Vec<Member>> {
    let defs = definitions(function);
    flagged_selectors(function)
        .map(|selector| {
            walk(&defs, selector)
                .into_iter()
                .map(|(value, inst)| match inst {
                    None => Member::Open(value),
                    Some(inst) => {
                        let mut erased = inst.clone();
                        let zeros = vec![ValueId(0); remap::operands(inst).len()];
                        // The walks agree on every variant (remap's unit
                        // test); were they not to, the unerased instruction
                        // is compared, which is stricter.
                        if !remap::replace_operands(&mut erased, &zeros) {
                            erased = inst.clone();
                        }
                        Member::Inst {
                            value,
                            inst: erased,
                        }
                    }
                })
                .collect()
        })
        .collect()
}
