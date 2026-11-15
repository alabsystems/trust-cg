// trust-cg-eqsat-check/src/sensitive.rs - skeleton operands the validator reads through their defining instruction
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The operands whose validity trust-ir-build decides from the instruction
//! that defines them rather than from their value (docs/eqsat-tier-e.md
//! section 2.5 "Literal-sensitive operands", section 8 item 2). Equal terms
//! do not make such an operand safe: a fold that turns a computed operand
//! into a `Const`, or removing a `Copy` in front of one, keeps every term and
//! can still turn an input the validator accepts into an output it refuses.
//!
//! The validator rules that read an operand's definition, at the pinned
//! trust-ir (`crates/trust-ir-build/src/validate.rs` and `validate/`), and how
//! each is held here:
//!
//! * `validate_types` builds `const_int_values` (integer `Const` results,
//!   flow-insensitive) and range-checks the lane index of `ExtractElement`
//!   and `InsertElement` (`check_element_index_operand`) only when it is a
//!   key there. `check_ptr_from_parts_operands` is handed the same map (its
//!   arms read only types at this pin; the contract keeps both of its
//!   operands literal-sensitive). Held by [`check_literals`]: at these
//!   positions an output operand defined by a `Const` needs an input operand
//!   defined by a `Const` of equal type and value. Copies are not seen
//!   through (the validator does not see through them).
//! * `validate_unwind_structure` rule (c) refuses a `Resume` operand defined
//!   by a literal (`Const`, `NullPtr`, `Undef`, `GlobalAddr`) or by a landing
//!   pad's selector. The reader refuses that on each body
//!   (`reader::check_resume_operands`); [`check_literals`] also holds the
//!   `Resume` operand to the `Const` rule above.
//! * `exhaustive_switch::selector_enum` traces the selector of a `Switch`
//!   flagged `exhaustive_enum_unreachable` through `Copy`, `zext`, `sext` and
//!   equal-width `bitcast` to `ExtractField { field: 0 }` of an enum, and only
//!   then (`validate_exhaustive_switch_cases`) holds the case set to the
//!   enum's discriminants. A rewrite anywhere on that chain (a graph `add`
//!   with zero removed, a skeleton cast's operand changed) can make the trace
//!   resolve. Held by [`check_tag_traces`]: when the output selector traces
//!   to an enum tag, the input selector must trace to one of the same type
//!   through the same casts. This trace follows every `zext`, `sext` and
//!   `bitcast` whatever their widths (a superset of the validator's), so the
//!   rule refuses whenever the validator's trace could differ.
//! * `HandleEnumGuards::new` (validate.rs:11210-11250; built for a
//!   handle-bearing module whose function reads a non-tag lane,
//!   validate.rs:19272-19275; its observed twin is
//!   `validate/observed_handle_enum_guards.rs`) records a block-final `Switch`
//!   as a tag guard only when its selector is DIRECTLY the result of an
//!   `ExtractField { field: 0 }` (`tag_reads`, no copy followed), whatever
//!   the switch's flags. `handle_aggregate_lane_rule` (validate.rs:11440-11475)
//!   then refuses a handle-lane read that no dominating guard case selects
//!   ("a handle lane of an enum is read only under a tag switch that selects
//!   a variant carrying it"). A see-through `Copy` inserted in front of such a
//!   selector keeps every term and removes the guard. Held by
//!   [`check_tag_guards`]: at every paired `Switch`, an input selector defined
//!   directly by an `ExtractField` (any field: a superset of the validator's
//!   field 0) needs the output selector defined directly by the
//!   skeleton-paired `ExtractField` (the same skeleton leaf: block, skeleton
//!   ordinal and result index). The converse (a `Copy` removed in front of a
//!   selector) only adds guards, which only admit reads.
//! * `validate_refinements` (only when `Module::predicates` is non-empty)
//!   decides refined consumption sites and declared refinements with
//!   `propagate_function_facts`, which derives a fact from each defining
//!   instruction (`Const` its value, `Add`/`Sub`/casts intervals, `Copy` and
//!   `Select` their operands', anything else `top`). Any graph rewrite can
//!   change those facts, and the checker does not model them: [`check`]
//!   refuses a module with predicates.
//!
//! Rules that read definitions and need nothing here, because the values
//! they trace are never graph-typed (a non-graph-typed operand carries an
//! opaque leaf, so the output keeps the same skeleton definition) or because
//! they see through copies and stop at skeleton instructions: the
//! `PanicLocation::Value` direct-definition test (pointers), the weak
//! `CallIndirect` callee trace (`Copy` to a `Const SymbolAddr`, which is
//! skeleton and never defined, so no rule rewrites above it), closure-target
//! provenance (closure values), the claims/effects address traces and the
//! sealed handle slots (pointers).

use std::collections::BTreeMap;

use trust_ir::{CastOp, Inst, Module, Ty, ValueId};

use crate::reader::{Analysis, Class};
use crate::rejection::Rejection;
use crate::terms::Leaf;

/// One matched skeleton instruction pair. The skeleton comparison has
/// established that the output instruction is `input` with its value
/// operands replaced, so the input instruction names the kind and flags of
/// both.
pub(crate) struct Site<'a> {
    pub(crate) block: u32,
    pub(crate) ordinal: usize,
    pub(crate) input: &'a Inst,
    pub(crate) input_ops: &'a [ValueId],
    pub(crate) output_ops: &'a [ValueId],
}

/// Every instruction of a body by the values it defines (flow-insensitive,
/// as the validator's lookups are; the reader has refused a value defined
/// twice), every value's type, and the positional leaf of every result of a
/// skeleton instruction (section 4), which names the same instruction in
/// both bodies.
pub(crate) struct Defs<'f> {
    inst: BTreeMap<ValueId, &'f Inst>,
    ty: BTreeMap<ValueId, Ty>,
    leaf: BTreeMap<ValueId, Leaf>,
}

impl<'f> Defs<'f> {
    pub(crate) fn of(module: &Module, analysis: &Analysis<'f>) -> Defs<'f> {
        let mut inst = BTreeMap::new();
        let mut ty = BTreeMap::new();
        let mut leaf = BTreeMap::new();
        for (bi, block) in analysis.func.blocks.iter().enumerate() {
            for (v, t) in &block.params {
                ty.insert(*v, t.clone());
            }
            for (ii, node) in block.body.iter().enumerate() {
                for (v, t) in node.results.iter().zip(node.result_tys(module)) {
                    inst.insert(*v, &node.inst);
                    ty.insert(*v, t);
                }
                // A result with no skeleton class (a graph instruction or a
                // see-through copy) gets no leaf, so it never matches one.
                let class = analysis.classes.get(bi).and_then(|c| c.get(ii));
                if let Some(Class::Skeleton(ordinal)) = class {
                    for (j, v) in node.results.iter().enumerate() {
                        let Ok(index) = u32::try_from(j) else { break };
                        leaf.insert(
                            *v,
                            Leaf::Result {
                                block: block.id.0,
                                ordinal: *ordinal,
                                index,
                            },
                        );
                    }
                }
            }
        }
        Defs { inst, ty, leaf }
    }
}

/// Refuses a module whose refinement verdicts depend on fact propagation.
pub(crate) fn check(module: &Module) -> Result<(), Rejection> {
    if module.predicates.is_empty() {
        Ok(())
    } else {
        Err(Rejection::RefinementPredicates {
            predicates: module.predicates.len(),
        })
    }
}

/// The literal-sensitive operand positions of `inst`, as indices into its
/// `Inst::visit_value_operands` order (`operands::set_operands` writes them
/// in that order and the skeleton comparison re-checks it).
fn literal_positions(inst: &Inst) -> &'static [usize] {
    match inst {
        // array, index
        Inst::ExtractElement { .. } => &[1],
        // array, index, value
        Inst::InsertElement { .. } => &[1],
        // data, metadata
        Inst::PtrFromParts { .. } => &[0, 1],
        // exn
        Inst::Resume { .. } => &[0],
        _ => &[],
    }
}

/// Section 2.5 "Literal-sensitive operands" at one skeleton pair.
pub(crate) fn check_literals(
    site: &Site<'_>,
    ind: &Defs<'_>,
    outd: &Defs<'_>,
) -> Result<(), Rejection> {
    for &k in literal_positions(site.input) {
        let (Some(vi), Some(vo)) = (site.input_ops.get(k), site.output_ops.get(k)) else {
            return Err(Rejection::LiteralIntroduced {
                block: site.block,
                ordinal: site.ordinal,
                operand: k,
                detail: "the operand position is missing".to_owned(),
            });
        };
        let Some(Inst::Const { ty, value }) = outd.inst.get(vo).copied() else {
            continue;
        };
        match ind.inst.get(vi).copied() {
            Some(Inst::Const {
                ty: in_ty,
                value: in_value,
            }) if in_ty == ty && in_value == value => {}
            other => {
                let was = match other {
                    Some(Inst::Const { ty, value }) => format!("const {ty} {value}"),
                    Some(Inst::Copy { .. }) => "a copy".to_owned(),
                    Some(_) => "another instruction".to_owned(),
                    None => "a block parameter".to_owned(),
                };
                return Err(Rejection::LiteralIntroduced {
                    block: site.block,
                    ordinal: site.ordinal,
                    operand: k,
                    detail: format!(
                        "output %{} is const {ty} {value}; input %{} is defined by {was}",
                        vo.0, vi.0
                    ),
                });
            }
        }
    }
    Ok(())
}

/// The trace of a value to an enum's tag: the casts from the selector inward
/// and the enum type, or `None` when the trace does not reach a tag.
type TagTrace = (Vec<(CastOp, Ty, Ty)>, Ty);

/// Follows `Copy`, `zext`, `sext` and `bitcast` from `value` to an
/// `ExtractField { field: 0 }` of an enum-typed aggregate. Bounded by the
/// definition count, so a (malformed) cycle ends.
fn tag_trace(defs: &Defs<'_>, value: ValueId) -> Option<TagTrace> {
    let mut casts = Vec::new();
    let mut current = value;
    for _ in 0..=defs.inst.len() {
        match defs.inst.get(&current).copied()? {
            Inst::Copy { operand, .. } => current = *operand,
            Inst::Cast {
                op: op @ (CastOp::ZExt | CastOp::SExt | CastOp::Bitcast),
                src_ty,
                dst_ty,
                operand,
            } => {
                casts.push((*op, src_ty.clone(), dst_ty.clone()));
                current = *operand;
            }
            Inst::ExtractField {
                aggregate,
                field: 0,
                ..
            } => {
                let ty = defs.ty.get(aggregate)?;
                return matches!(ty, Ty::Enum(_)).then(|| (casts, ty.clone()));
            }
            _ => return None,
        }
    }
    None
}

/// The exhaustive-switch selector rule at one skeleton pair.
pub(crate) fn check_tag_traces(
    site: &Site<'_>,
    ind: &Defs<'_>,
    outd: &Defs<'_>,
) -> Result<(), Rejection> {
    let Inst::Switch {
        exhaustive_enum_unreachable: true,
        ..
    } = site.input
    else {
        return Ok(());
    };
    // The selector is operand 0 of a `Switch`.
    let (Some(vi), Some(vo)) = (site.input_ops.first(), site.output_ops.first()) else {
        return Err(Rejection::TagProvenanceChanged {
            block: site.block,
            ordinal: site.ordinal,
            detail: "the switch has no selector operand".to_owned(),
        });
    };
    let Some(out_trace) = tag_trace(outd, *vo) else {
        return Ok(());
    };
    match tag_trace(ind, *vi) {
        Some(in_trace) if in_trace == out_trace => Ok(()),
        in_trace => Err(Rejection::TagProvenanceChanged {
            block: site.block,
            ordinal: site.ordinal,
            detail: format!(
                "output %{} traces to the tag of {} through {} cast(s); input %{} {}",
                vo.0,
                out_trace.1,
                out_trace.0.len(),
                vi.0,
                match in_trace {
                    Some((casts, ty)) => format!(
                        "traces to the tag of {ty} through a different chain of {} cast(s)",
                        casts.len()
                    ),
                    None => "does not trace to an enum tag".to_owned(),
                }
            ),
        }),
    }
}

/// Names how a value is defined, for a refusal's detail.
fn defined_by(defs: &Defs<'_>, value: ValueId) -> String {
    let what = match defs.inst.get(&value).copied() {
        Some(Inst::ExtractField { .. }) => "an extract_field",
        Some(Inst::Copy { .. }) => "a copy",
        Some(Inst::Cast { .. }) => "a cast",
        Some(Inst::Const { .. }) => "a const",
        Some(_) => "another instruction",
        None => "a block parameter",
    };
    match defs.leaf.get(&value) {
        Some(leaf) => format!("{what} (leaf {leaf})"),
        None => what.to_owned(),
    }
}

/// The handle-lane tag-guard rule at one skeleton pair: an input `Switch`
/// selector defined directly by an `ExtractField` keeps, in the output, a
/// selector defined directly by the skeleton-paired `ExtractField` (equal
/// skeleton leaves name the same paired instruction, and the skeleton
/// comparison has made that pair the same kind with the same operands).
pub(crate) fn check_tag_guards(
    site: &Site<'_>,
    ind: &Defs<'_>,
    outd: &Defs<'_>,
) -> Result<(), Rejection> {
    let Inst::Switch { .. } = site.input else {
        return Ok(());
    };
    // The selector is operand 0 of a `Switch`.
    let (Some(vi), Some(vo)) = (site.input_ops.first(), site.output_ops.first()) else {
        return Err(Rejection::TagProvenanceChanged {
            block: site.block,
            ordinal: site.ordinal,
            detail: "the switch has no selector operand".to_owned(),
        });
    };
    let Some(Inst::ExtractField { .. }) = ind.inst.get(vi).copied() else {
        return Ok(());
    };
    let in_leaf = ind.leaf.get(vi);
    let kept = matches!(outd.inst.get(vo).copied(), Some(Inst::ExtractField { .. }))
        && in_leaf.is_some()
        && outd.leaf.get(vo) == in_leaf;
    if kept {
        return Ok(());
    }
    Err(Rejection::TagProvenanceChanged {
        block: site.block,
        ordinal: site.ordinal,
        detail: format!(
            "input selector %{} is defined directly by {}, which trust-ir-build's \
             handle-lane tag guard reads; output selector %{} is defined by {}, \
             not directly by the paired extract_field",
            vi.0,
            defined_by(ind, *vi),
            vo.0,
            defined_by(outd, *vo)
        ),
    })
}
