// trust-cg-eqsat-check/src/validity.rs - the trust-ir validity rules a graph rewrite can break, re-read for one body
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The validity refusals of docs/eqsat-tier-e.md section 2.5 (last
//! paragraph) and section 8 item 2, read on each body with this crate's own
//! code (it cannot depend on trust-ir-build). Each mirrors one rule of the
//! pinned `trust_ir_build::validate_module` exactly, so a rewrite that adds,
//! removes or moves a graph instruction or a see-through `Copy` cannot turn
//! an input the validator accepts into an output it refuses through these
//! rules:
//!
//! * **Value names** (`validate_debug_metadata`, `InvalidValueName`): every
//!   `value_names` entry names a `ValueId` some block parameter or
//!   instruction result of the body defines, and no `ValueId` is named
//!   twice. The same name string on two values is allowed (the validator
//!   compares only the `ValueId`s).
//! * **Instruction scopes** (`validate_debug_metadata`,
//!   `InvalidInstructionScope`): an instruction's `scope`, when present, is
//!   below the length of the function's scope table, which is 0 when the
//!   function has no table (so any stamped scope is refused then). `None`
//!   ("unstamped") is always valid.
//! * **Span files** (`validate_module`, `SpanFileIndexOutOfRange`): when the
//!   module's file table is non-empty, every instruction span's `file`, every
//!   scope's opening span's `file` and every inlining link's call-site span's
//!   `file` is below its length. An empty table makes spans file-less and
//!   nothing is checked. `Block` carries no span.
//! * **Cast width direction** (`check_cast_operand_and_width`,
//!   `CastWidthDirectionInvalid`): for every `Cast` whose op is `Trunc`,
//!   `ZExt` or `SExt` and whose source and destination both have a
//!   `Ty::bit_width` (a target-independent width: fixed-width integers,
//!   `bool` at 1 bit, `char` at 32, floats, vectors; `isize`/`usize` and
//!   pointer-like types have none and are exempt),
//!   `Trunc` requires source width > destination width and `ZExt`/`SExt`
//!   require source width < destination width, both strict (an identity
//!   resize is refused).
//! * **Exhaustive-switch default arm** (`validate/exhaustive_switch.rs`
//!   `validate_exhaustive_switch_shape`, rule 1 (ii),
//!   `ExhaustiveSwitchDefaultReachable`): for every block whose terminator is
//!   a `Switch` flagged `exhaustive_enum_unreachable`, the `default` block,
//!   when it exists, has no parameters and its body is exactly
//!   `[Unreachable]`. `Unreachable` is skeleton, so a rewrite keeps it, but a
//!   graph instruction or see-through `Copy` added to, or moved into, that
//!   block breaks the rule while every skeleton comparison holds. A missing
//!   default block is the reader's edge refusal (the validator's
//!   `BranchTargetNotFound`).
//!
//! Rules of the same families checked and NOT re-read here, with the reason:
//!
//! * The scope table's tree shape (`InvalidScopeTree`, `InvalidInlinedScope`)
//!   and module obligation diagnostics' spans: section 8 item 1 requires
//!   `Function::scopes` equal in both bodies and the module is shared, so a
//!   rewrite cannot change them.
//! * Other `Function` fields that name values: none besides `value_names`
//!   (`proofs`, `summary` and `source_provenance` are refused by eligibility).
//! * Graph-operator typing (`check_binop_operand`, `check_unop_operand`,
//!   the `ICmp` category test, `check_select_operands`, the `Copy` operand
//!   test, `check_cast_compatibility`, `CastOperandTypeMismatch`, the
//!   canonical `Const` spelling): the reader classifies an instruction as a
//!   graph instruction or see-through `Copy` only when its operand and result
//!   types are exactly the operator's (`reader::graph_form`, `see_through`),
//!   and `OpDesc::admitted_category` refuses each category the validator
//!   refuses (`add`/rotates/unary operators at `bool`, `band`/`bor`/`bxor`
//!   off `bool`, casts from or to `bool`); every other instruction is
//!   skeleton, whose count, kinds and types the skeleton comparison fixes.
//!   A changed skeleton operand carries the same term, so the same graph
//!   type, as the input's, or the same opaque leaf.
//! * The other clauses of the exhaustive-switch shape rule (rule 1): (i) an
//!   empty `default_args` and (iii) case values distinct at the selector's
//!   width read only the `Switch` itself and its selector's type. The
//!   `Switch` is skeleton, so its flag, cases and the length of each edge's
//!   argument list are fixed by the skeleton comparison; a changed selector
//!   carries the input's term, whose graph type names exactly one trust-ir
//!   type (`Sty::from_ir` is injective), or the input's opaque leaf, so the
//!   selector type and width are the input's. The default block's parameter
//!   count is fixed by the block comparison (section 8 item 1); the reader
//!   still re-reads it with clause (ii). Rule 2 (the case set against the
//!   enum) reads the selector through its definition and is held by
//!   `sensitive::check_tag_traces`.

use std::collections::BTreeSet;

use trust_ir::{CastOp, Function, Inst, Module, ValueId};

use crate::rejection::{Body, Rejection};

fn malformed(body: Body, block: Option<u32>, inst: Option<usize>, detail: String) -> Rejection {
    Rejection::MalformedBody {
        body,
        block,
        inst,
        detail,
    }
}

/// Refuses `func` (read as `body`) when it breaks one of the validity rules
/// listed in the module documentation. `defined` is every `ValueId` a block
/// parameter or instruction result of `func` defines.
pub(crate) fn check(
    module: &Module,
    func: &Function,
    body: Body,
    defined: &BTreeSet<ValueId>,
) -> Result<(), Rejection> {
    value_names(func, body, defined)?;
    scope_spans(module, func, body)?;
    let scope_count = func.scopes.as_ref().map_or(0, Vec::len);
    let file_count = module.files.len();
    for block in &func.blocks {
        for (pos, node) in block.body.iter().enumerate() {
            let here = |detail: String| malformed(body, Some(block.id.0), Some(pos), detail);
            if let Some(scope) = node.scope
                && usize::try_from(scope).map_or(true, |s| s >= scope_count)
            {
                return Err(here(format!(
                    "instruction scope {scope} is outside the function's scope table of \
                     {scope_count} entr{}",
                    if scope_count == 1 { "y" } else { "ies" }
                )));
            }
            if let Some(span) = &node.span
                && file_out_of_range(span.file, file_count)
            {
                return Err(here(format!(
                    "span file {} is outside the module's file table of {file_count}",
                    span.file
                )));
            }
            if let Some(detail) = cast_direction(&node.inst) {
                return Err(here(detail));
            }
        }
    }
    exhaustive_default_arms(func, body)
}

/// `ExhaustiveSwitchDefaultReachable`, clause (ii): the `default` block of a
/// `Switch` flagged `exhaustive_enum_unreachable` has no parameters and its
/// body is exactly `[Unreachable]`. A default target that does not exist is
/// skipped, as the validator skips it (the reader has refused the edge).
fn exhaustive_default_arms(func: &Function, body: Body) -> Result<(), Rejection> {
    for block in &func.blocks {
        let Some(term) = block.terminator() else {
            continue;
        };
        let Inst::Switch {
            default,
            exhaustive_enum_unreachable: true,
            ..
        } = &term.inst
        else {
            continue;
        };
        let Some(target) = func.blocks.iter().find(|b| b.id == *default) else {
            continue;
        };
        let pos = block.body.len().saturating_sub(1);
        let here = |detail: String| malformed(body, Some(block.id.0), Some(pos), detail);
        if !target.params.is_empty() {
            return Err(here(format!(
                "the exhaustive switch's default block bb{} has {} parameter(s); a dead \
                 default has none",
                default.0,
                target.params.len()
            )));
        }
        let unreachable_only = matches!(
            target.body.as_slice(),
            [only] if matches!(only.inst, Inst::Unreachable)
        );
        if !unreachable_only {
            return Err(here(format!(
                "the exhaustive switch's default block bb{} is not exactly [unreachable] \
                 ({} instruction(s))",
                default.0,
                target.body.len()
            )));
        }
    }
    Ok(())
}

/// `InvalidValueName`: each named `ValueId` is defined, and named once.
fn value_names(func: &Function, body: Body, defined: &BTreeSet<ValueId>) -> Result<(), Rejection> {
    let Some(names) = &func.value_names else {
        return Ok(());
    };
    let mut seen: BTreeSet<ValueId> = BTreeSet::new();
    for (v, _) in names {
        if !seen.insert(*v) {
            return Err(malformed(
                body,
                None,
                None,
                format!("value_names names %{} more than once", v.0),
            ));
        }
        if !defined.contains(v) {
            return Err(malformed(
                body,
                None,
                None,
                format!("value_names names %{}, which the body does not define", v.0),
            ));
        }
    }
    Ok(())
}

/// Whether a span's `file` is outside a non-empty file table of
/// `file_count` entries (an empty table makes spans file-less).
fn file_out_of_range(file: u32, file_count: usize) -> bool {
    file_count != 0 && usize::try_from(file).map_or(true, |f| f >= file_count)
}

/// `SpanFileIndexOutOfRange` on the scope table: each scope's opening span
/// and each inlining link's call-site span.
fn scope_spans(module: &Module, func: &Function, body: Body) -> Result<(), Rejection> {
    let file_count = module.files.len();
    for (index, scope) in func.scopes.iter().flatten().enumerate() {
        let spans = scope
            .span
            .iter()
            .chain(scope.inlined_at.iter().map(|link| &link.span));
        for span in spans {
            if file_out_of_range(span.file, file_count) {
                return Err(malformed(
                    body,
                    None,
                    None,
                    format!(
                        "scope {index} carries span file {}, outside the module's file table \
                         of {file_count}",
                        span.file
                    ),
                ));
            }
        }
    }
    Ok(())
}

/// `CastWidthDirectionInvalid`: the reason an integer resize moves against
/// its op's width direction, or `None`.
fn cast_direction(inst: &Inst) -> Option<String> {
    let Inst::Cast {
        op, src_ty, dst_ty, ..
    } = inst
    else {
        return None;
    };
    let (sw, dw) = (src_ty.bit_width()?, dst_ty.bit_width()?);
    let ok = match op {
        CastOp::Trunc => sw > dw,
        CastOp::ZExt | CastOp::SExt => sw < dw,
        _ => return None,
    };
    (!ok).then(|| {
        format!(
            "{op} from {src_ty} ({sw} bits) to {dst_ty} ({dw} bits) moves against its width \
             direction"
        )
    })
}
