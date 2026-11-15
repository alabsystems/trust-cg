// trust-cg-verify/src/array_row_lowering.rs - exact array elimination by read-over-write
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Eliminate SMT-LIB arrays from an obligation's query by the array theory's
//! own axioms, so the query is array-free and its UNSAT proof is one the
//! independent checker replays.
//!
//! # Why
//!
//! The strict gate's memory obligations (memset and buffer initialisation,
//! frame-slot and spill-slot non-interference, scheduler store/load ordering,
//! the x86 compare-exchange and read-modify-write loops) model memory as
//! `(Array (_ BitVec 64) (_ BitVec 8))` built from a constant array and a
//! chain of `store`s, read with `select`. AY decides every one of them, and
//! for 41 of them (2026-09-28, seal `trust-7d5533b2`) its proof is a bare
//! `trust` step: its array reasoning has no Alethe derivation the checker can
//! replay. The same questions without arrays are ordinary bit-vector
//! questions.
//!
//! # The rewrite
//!
//! Every `select` is pushed through the array term it reads:
//!
//! * `(select (store a i v) j)` is `(ite (= i j) v (select a j))` —
//!   read-over-write, the defining axiom of `store`;
//! * `(select ((as const (Array I E)) d) j)` is `d` — the defining axiom of a
//!   constant array;
//! * `(select (ite c a b) j)` is `(ite c (select a j) (select b j))`.
//! * A nullary BV-array symbol `m : () -> Array(I,E)` becomes the SAME
//!   symbol `m : I -> E`, and `(select m j)` becomes `(m j)`. Arrays and
//!   total functions have bijective interpretations; equal indices retain
//!   congruent reads. No bytes, aliases or unobserved contents are guessed.
//!
//! Each is an EQUIVALENCE in the theory of arrays, so the rewritten formula
//! is equivalent to the original: it has exactly the same models on the
//! remaining (bit-vector) symbols. A read-over-write whose two addresses are
//! provably equal or provably distinct ([`same_address`]: the same term, two
//! constants, or `b + c1` against `b + c2`) resolves on the spot instead of
//! building its `ite` — the byte-granular memory models compare `addr + i`
//! with `addr + j` at every level of every chain, and deciding those keeps
//! the rewritten query the size of the question actually asked. An array that is not built from those
//! forms — an array variable, a non-nullary function returning an
//! array, an equality between arrays, a `store` or constant array outside any
//! `select` — makes [`eliminate_arrays`] decline, and the caller keeps the
//! original query. Nothing is abstracted, so nothing is trusted beyond the
//! transcription of these laws. The arbitrary-array profile also refuses
//! conflicting/implicit symbols, non-simple symbol spellings, quantifiers
//! and non-BV element/index sorts.

use std::sync::Arc;

use crate::smt::{SmtExpr, SmtSort};

/// Bound on the rewritten formula's node count: read-over-write duplicates
/// the read index into every level of a store chain, and a select whose
/// stored values are themselves selects multiplies that. Past this the
/// lowering declines rather than build a query no solver should be asked.
/// The arbitrary-symbol profile also charges its signature census and copied
/// name bytes against this SAME bound, before cloning or hashing names.
const MAX_REWRITTEN_NODES: usize = 1 << 20;

/// Why [`eliminate_arrays`] declined.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArrayDecline {
    /// The formula mentions no array: there is nothing to eliminate.
    NoArrays,
    /// An array construct outside the three axioms (named).
    Unsupported(String),
}

/// The array-free equivalent of `formula` (see the module docs), or why none
/// was produced.
pub fn eliminate_arrays(formula: &SmtExpr) -> Result<SmtExpr, ArrayDecline> {
    eliminate_arrays_with_reserved(formula, &[])
}

/// Obligation declarations participate even when their names are unused in
/// the expression. Never turn an inconsistent array/scalar signature into a
/// well-formed lowered query by changing the array symbol's signature.
pub(crate) fn eliminate_arrays_with_reserved(
    formula: &SmtExpr,
    reserved: &[&str],
) -> Result<SmtExpr, ArrayDecline> {
    if !mentions_arrays(formula) {
        return Err(ArrayDecline::NoArrays);
    }
    let nodes =
        check_read_function_symbols(formula, reserved).map_err(ArrayDecline::Unsupported)?;
    let mut eliminator = Eliminator {
        nodes,
        rewritten: std::collections::HashMap::new(),
    };
    eliminator
        .rewrite(formula)
        .map_err(ArrayDecline::Unsupported)
}

/// A nullary array symbol and a total read function have bijective
/// interpretations. Keep its ORIGINAL name, replacing only () -> Array(I,E)
/// with (I) -> E; no fresh-name assumption or finite-memory approximation is
/// involved. Array equality/extensionality and array-valued applications stay
/// outside this profile. Inspect the whole immutable DAG, including cold arms.
fn check_read_function_symbols(formula: &SmtExpr, reserved: &[&str]) -> Result<usize, String> {
    use std::collections::HashMap;
    let mut arrays = HashMap::new();
    let mut work = 0usize;
    let mut error = None;
    formula.any_node(|node| {
        work = work.saturating_add(1);
        if work > MAX_REWRITTEN_NODES {
            error = Some("the array signature census exceeds its node bound".to_owned());
            return true;
        }
        if let SmtExpr::UF {
            name,
            args,
            ret_sort: SmtSort::Array(i, e),
        } = node
        {
            if !args.is_empty()
                || !matches!(i.as_ref(), SmtSort::BitVec(w) if *w != 0)
                || !matches!(e.as_ref(), SmtSort::BitVec(w) if *w != 0)
            {
                error =
                    Some("only nullary bit-vector array symbols have read functions".to_owned());
                return true;
            }
            work = work.saturating_add(name.len());
            if work > MAX_REWRITTEN_NODES {
                error = Some("the array signature census exceeds its node bound".to_owned());
                return true;
            }
            if let Some(previous) = arrays.insert(name.clone(), (i.clone(), e.clone()))
                && previous != (i.clone(), e.clone())
            {
                error = Some("conflicting array symbol signatures".to_owned());
                return true;
            }
        }
        false
    });
    if let Some(error) = error {
        return Err(error);
    }
    if arrays.is_empty() {
        return Ok(0);
    }
    for name in reserved {
        work = work.saturating_add(1).saturating_add(name.len());
        if work > MAX_REWRITTEN_NODES || !simple_read_symbol(name) || arrays.contains_key(*name) {
            return Err(
                "an array symbol has an unsupported or conflicting obligation input".to_owned(),
            );
        }
    }
    formula.any_node(|node| {
        work = work.saturating_add(1);
        if let SmtExpr::Var { name, .. } | SmtExpr::UF { name, .. } | SmtExpr::UFDecl { name, .. } = node {
            work = work.saturating_add(name.len());
            if work > MAX_REWRITTEN_NODES || !simple_read_symbol(name) {
                error = Some("the arbitrary-array symbol inventory exceeds its bound or has a non-simple spelling".to_owned());
                return true;
            }
        }
        let invalid = match node {
            SmtExpr::Var { name, .. } | SmtExpr::UFDecl { name, .. } => arrays.contains_key(name.as_str()),
            SmtExpr::UF { name, args, ret_sort } if arrays.contains_key(name.as_str()) =>
                !args.is_empty() || !matches!(ret_sort, SmtSort::Array(..)),
            // These introduce implicit symbols. Refuse their combination with
            // arbitrary arrays until the shared symbol owner binds them too.
            SmtExpr::MemLoad { .. } | SmtExpr::TrapIfZero { .. } => true,
            SmtExpr::ForAll { .. } | SmtExpr::Exists { .. } => true,
            SmtExpr::Select { array, index } => !matches!(array.sort(), SmtSort::Array(i, _) if *i == index.sort()),
            SmtExpr::Store { array, index, value } => !matches!(array.sort(), SmtSort::Array(i, e) if *i == index.sort() && *e == value.sort()),
            SmtExpr::Ite { then_expr, else_expr, .. } if is_array(then_expr) || is_array(else_expr) => then_expr.sort() != else_expr.sort(),
            _ => false,
        };
        if invalid || work > MAX_REWRITTEN_NODES {
            error = Some("an arbitrary array has conflicting symbols, sorts, implicit symbols or quantified scope".to_owned());
            return true;
        }
        false
    });
    error.map_or(Ok(work), Err)
}

/// Refuse quoted/escaped aliases rather than invent a second SMT name parser.
/// This bounded new profile admits only ordinary ASCII identifier spellings;
/// the original query route remains available for every other spelling.
pub(crate) fn simple_read_symbol(name: &str) -> bool {
    let mut bytes = name.bytes();
    matches!(bytes.next(), Some(b) if b.is_ascii_alphabetic() || b == b'_')
        && bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
}

/// Whether `expr` has an array node or an array-sorted subterm.
pub fn mentions_arrays(expr: &SmtExpr) -> bool {
    // An array-valued ITE is found through its children. Do not recursively
    // re-derive its sort at every ancestor while doing this presence census.
    expr.any_node(|node| {
        matches!(
            node,
            SmtExpr::Select { .. } | SmtExpr::Store { .. } | SmtExpr::ConstArray { .. }
        ) || matches!(
            node,
            SmtExpr::UF {
                ret_sort: SmtSort::Array(..),
                ..
            }
        )
    })
}

fn is_array(expr: &SmtExpr) -> bool {
    match expr {
        SmtExpr::Store { .. } | SmtExpr::ConstArray { .. } => true,
        SmtExpr::UF { ret_sort, .. } => matches!(ret_sort, SmtSort::Array(..)),
        SmtExpr::Ite { then_expr, .. } => is_array(then_expr),
        _ => false,
    }
}

struct Eliminator {
    nodes: usize,
    // Keys name the immutable input graph, which outlives this eliminator.
    // Reuse existing child ownership rather than cloning a DAG into a tree.
    rewritten: std::collections::HashMap<*const SmtExpr, Arc<SmtExpr>>,
}

impl Eliminator {
    fn charge(&mut self) -> Result<(), String> {
        self.nodes = self.nodes.saturating_add(1);
        if self.nodes > MAX_REWRITTEN_NODES {
            return Err("the read-over-write expansion exceeds its node bound".to_string());
        }
        Ok(())
    }

    fn rewrite_shared(&mut self, expr: &Arc<SmtExpr>) -> Result<Arc<SmtExpr>, String> {
        let key = Arc::as_ptr(expr);
        if let Some(rewritten) = self.rewritten.get(&key).cloned() {
            self.charge()?;
            return Ok(rewritten);
        }
        let rewritten = Arc::new(self.rewrite(expr)?);
        self.rewritten.insert(key, rewritten.clone());
        Ok(rewritten)
    }

    /// Rewrite every `select` in `expr`; refuse any other array construct.
    fn rewrite(&mut self, expr: &SmtExpr) -> Result<SmtExpr, String> {
        self.charge()?;
        if !mentions_arrays(expr) {
            return Ok(expr.clone());
        }
        match expr {
            SmtExpr::Select { array, index } => {
                let index = self.rewrite_shared(index)?;
                self.read(array, &index)
            }
            SmtExpr::Store { .. } | SmtExpr::ConstArray { .. } => {
                Err("an array term outside any select".to_string())
            }
            SmtExpr::Eq { lhs, .. } if is_array(lhs) => {
                Err("an equality between arrays".to_string())
            }
            SmtExpr::UF { .. } | SmtExpr::UFDecl { .. } => {
                Err("an uninterpreted function over arrays".to_string())
            }
            SmtExpr::ForAll { .. } | SmtExpr::Exists { .. } => {
                Err("an array under a quantifier".to_string())
            }
            other => self.rebuild(other),
        }
    }

    /// `(select array index)` pushed through `array`.
    fn read(&mut self, array: &SmtExpr, index: &Arc<SmtExpr>) -> Result<SmtExpr, String> {
        self.charge()?;
        match array {
            // Read-over-write.
            SmtExpr::Store {
                array: inner,
                index: written,
                value,
            } => {
                let written = self.rewrite_shared(written)?;
                match same_address(&written, index, &mut || self.charge())? {
                    // The two addresses are provably equal or provably
                    // distinct: the read resolves here, and the chain below
                    // (or the stored value) is never built.
                    Some(true) => Ok((*self.rewrite_shared(value)?).clone()),
                    Some(false) => self.read(inner, index),
                    None => {
                        let value = self.rewrite_shared(value)?;
                        let rest = Arc::new(self.read(inner, index)?);
                        Ok(SmtExpr::Ite {
                            cond: Arc::new(SmtExpr::Eq {
                                lhs: written,
                                rhs: index.clone(),
                            }),
                            then_expr: value,
                            else_expr: rest,
                        })
                    }
                }
            }
            // A constant array reads its value everywhere.
            SmtExpr::ConstArray { value, .. } => Ok((*self.rewrite_shared(value)?).clone()),
            // Reads distribute over an array-sorted `ite`.
            SmtExpr::Ite {
                cond,
                then_expr,
                else_expr,
            } => {
                let cond = self.rewrite_shared(cond)?;
                let then_read = Arc::new(self.read(then_expr, index)?);
                let else_read = Arc::new(self.read(else_expr, index)?);
                Ok(SmtExpr::Ite {
                    cond,
                    then_expr: then_read,
                    else_expr: else_read,
                })
            }
            SmtExpr::Var { name, .. } => Err(format!("the array variable `{name}`")),
            SmtExpr::UF {
                name,
                args,
                ret_sort: SmtSort::Array(i, e),
            } if args.is_empty() && **i == index.sort() => {
                self.nodes = self.nodes.saturating_add(name.len());
                self.charge()?;
                Ok(SmtExpr::uf(
                    name.clone(),
                    vec![(**index).clone()],
                    *e.clone(),
                ))
            }
            other => Err(format!("a read of the array term {}", head(other))),
        }
    }

    /// The same node over rewritten children.
    fn rebuild(&mut self, expr: &SmtExpr) -> Result<SmtExpr, String> {
        let mut low =
            |child: &Arc<SmtExpr>| -> Result<Arc<SmtExpr>, String> { self.rewrite_shared(child) };
        Ok(match expr {
            SmtExpr::BvAdd { lhs, rhs, width } => SmtExpr::BvAdd {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvSub { lhs, rhs, width } => SmtExpr::BvSub {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvMul { lhs, rhs, width } => SmtExpr::BvMul {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvSDiv { lhs, rhs, width } => SmtExpr::BvSDiv {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvUDiv { lhs, rhs, width } => SmtExpr::BvUDiv {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvURem { lhs, rhs, width } => SmtExpr::BvURem {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::TrapIfZero {
                guard,
                value,
                width,
            } => SmtExpr::TrapIfZero {
                guard: low(guard)?,
                value: low(value)?,
                width: *width,
            },
            SmtExpr::BvNeg { operand, width } => SmtExpr::BvNeg {
                operand: low(operand)?,
                width: *width,
            },
            SmtExpr::Eq { lhs, rhs } => SmtExpr::Eq {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
            },
            SmtExpr::Not { operand } => SmtExpr::Not {
                operand: low(operand)?,
            },
            SmtExpr::And { lhs, rhs } => SmtExpr::And {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
            },
            SmtExpr::Or { lhs, rhs } => SmtExpr::Or {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
            },
            SmtExpr::BvSlt { lhs, rhs, width } => SmtExpr::BvSlt {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvSge { lhs, rhs, width } => SmtExpr::BvSge {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvUge { lhs, rhs, width } => SmtExpr::BvUge {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvSgt { lhs, rhs, width } => SmtExpr::BvSgt {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvSle { lhs, rhs, width } => SmtExpr::BvSle {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvUlt { lhs, rhs, width } => SmtExpr::BvUlt {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvUgt { lhs, rhs, width } => SmtExpr::BvUgt {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvUle { lhs, rhs, width } => SmtExpr::BvUle {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::Ite {
                cond,
                then_expr,
                else_expr,
            } => SmtExpr::Ite {
                cond: low(cond)?,
                then_expr: low(then_expr)?,
                else_expr: low(else_expr)?,
            },
            SmtExpr::Extract {
                high,
                low: bit,
                operand,
                width,
            } => SmtExpr::Extract {
                high: *high,
                low: *bit,
                operand: low(operand)?,
                width: *width,
            },
            SmtExpr::BvAnd { lhs, rhs, width } => SmtExpr::BvAnd {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvOr { lhs, rhs, width } => SmtExpr::BvOr {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvXor { lhs, rhs, width } => SmtExpr::BvXor {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvShl { lhs, rhs, width } => SmtExpr::BvShl {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvLshr { lhs, rhs, width } => SmtExpr::BvLshr {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::BvAshr { lhs, rhs, width } => SmtExpr::BvAshr {
                lhs: low(lhs)?,
                rhs: low(rhs)?,
                width: *width,
            },
            SmtExpr::Concat { hi, lo, width } => SmtExpr::Concat {
                hi: low(hi)?,
                lo: low(lo)?,
                width: *width,
            },
            SmtExpr::ZeroExtend {
                operand,
                extra_bits,
                width,
            } => SmtExpr::ZeroExtend {
                operand: low(operand)?,
                extra_bits: *extra_bits,
                width: *width,
            },
            SmtExpr::SignExtend {
                operand,
                extra_bits,
                width,
            } => SmtExpr::SignExtend {
                operand: low(operand)?,
                extra_bits: *extra_bits,
                width: *width,
            },
            other => {
                return Err(format!(
                    "an array under the unexpected node {}",
                    head(other)
                ));
            }
        })
    }
}

/// Iteratively retain one opaque base and accumulate literal offsets modulo
/// the actual address width. Every visited node uses the caller's existing
/// rewrite budget. Wider words are not truncated into this u64 address model.
#[allow(clippy::type_complexity)]
fn affine_address<'a>(
    mut expr: &'a SmtExpr,
    charge: &mut impl FnMut() -> Result<(), String>,
) -> Result<Option<(Option<&'a SmtExpr>, u64, u32)>, String> {
    let SmtSort::BitVec(width @ 1..=64) = expr.sort() else {
        return Ok(None);
    };
    let mask = if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    let mut offset = 0u64;
    loop {
        charge()?;
        match expr {
            SmtExpr::BvConst { value, width: bits } if *bits == width => {
                return Ok(Some((None, offset.wrapping_add(*value) & mask, width)));
            }
            SmtExpr::BvAdd {
                lhs,
                rhs,
                width: bits,
            } if *bits == width => {
                let (base, value, constant_width) = match (lhs.as_ref(), rhs.as_ref()) {
                    (SmtExpr::BvConst { value, width }, base)
                    | (base, SmtExpr::BvConst { value, width }) => (base, *value, *width),
                    _ => return Ok(Some((Some(expr), offset, width))),
                };
                if constant_width != width || base.sort() != SmtSort::BitVec(width) {
                    return Ok(None);
                }
                offset = offset.wrapping_add(value) & mask;
                expr = base;
            }
            SmtExpr::BvSub {
                lhs,
                rhs,
                width: bits,
            } if *bits == width => {
                let SmtExpr::BvConst {
                    value,
                    width: constant_width,
                } = rhs.as_ref()
                else {
                    return Ok(Some((Some(expr), offset, width)));
                };
                if *constant_width != width || lhs.sort() != SmtSort::BitVec(width) {
                    return Ok(None);
                }
                offset = offset.wrapping_sub(*value) & mask;
                expr = lhs;
            }
            _ => return Ok(Some((Some(expr), offset, width))),
        }
    }
}

/// Equality under one shared base follows the bijection of modular addition.
/// No model value, alias assumption or mathematical unbounded integer is used.
fn same_address(
    a: &SmtExpr,
    b: &SmtExpr,
    charge: &mut impl FnMut() -> Result<(), String>,
) -> Result<Option<bool>, String> {
    charge()?;
    if a == b {
        return Ok(Some(true));
    }
    let Some((a_base, a_offset, a_width)) = affine_address(a, charge)? else {
        return Ok(None);
    };
    let Some((b_base, b_offset, b_width)) = affine_address(b, charge)? else {
        return Ok(None);
    };
    if a_width != b_width {
        return Ok(None);
    }
    Ok(match (a_base, b_base) {
        (None, None) => Some(a_offset == b_offset),
        (Some(x), Some(y)) if x == y => Some(a_offset == b_offset),
        _ => None,
    })
}

/// A short name for an expression's head, for decline messages.
fn head(expr: &SmtExpr) -> String {
    let text = expr.to_string();
    let end = text
        .char_indices()
        .skip(1)
        .find(|(_, c)| c.is_whitespace() || *c == ')')
        .map_or(text.len(), |(i, _)| i);
    text[..end.min(48)].to_string()
}

#[cfg(test)]
#[path = "array_row_lowering_tests.rs"]
mod tests;
