// trust-cg-verify/src/smt_map.rs - one exhaustive child map over SmtExpr
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! [`SmtExpr::try_map_children`]: the same node over children rewritten by a
//! caller's function, every other field kept.
//!
//! The match is EXHAUSTIVE on purpose — no `_` arm — so a new `SmtExpr`
//! variant stops this crate compiling until a rewrite knows how to descend
//! into it, instead of silently leaving its children un-rewritten.

use crate::smt::{SmtExpr, SmtSort};
use std::collections::HashMap;
use std::convert::Infallible;
use std::sync::Arc;

type Child = Arc<SmtExpr>;

/// Only UF arguments own expression values directly; all other expression
/// edges are Arcs. Copy those inline values without recursive Clone calls,
/// retaining each shared Arc rather than expanding its expression tree.
fn clone_inline_expression(input: &SmtExpr) -> SmtExpr {
    enum Frame<'a> {
        Visit(&'a SmtExpr),
        FinishUf {
            name: &'a str,
            ret_sort: &'a SmtSort,
            arity: usize,
        },
    }
    let mut pending = vec![Frame::Visit(input)];
    let mut values = Vec::new();
    while let Some(frame) = pending.pop() {
        match frame {
            Frame::Visit(SmtExpr::UF {
                name,
                args,
                ret_sort,
            }) => {
                pending.push(Frame::FinishUf {
                    name,
                    ret_sort,
                    arity: args.len(),
                });
                pending.extend(args.iter().rev().map(Frame::Visit));
            }
            Frame::Visit(node) => values.push(node.clone()),
            Frame::FinishUf {
                name,
                ret_sort,
                arity,
            } => {
                let args = values.split_off(values.len() - arity);
                values.push(SmtExpr::UF {
                    name: name.into(),
                    args,
                    ret_sort: ret_sort.clone(),
                });
            }
        }
    }
    values.pop().expect("one expression copied")
}

fn own_expression(value: Child) -> SmtExpr {
    match Arc::try_unwrap(value) {
        Ok(node) => node,
        Err(shared) => clone_inline_expression(&shared),
    }
}

impl SmtExpr {
    /// Context-independent bottom-up rewrite of each distinct input node once.
    /// Scope-sensitive substitution needs its own context-keyed traversal. `None`
    /// leaves the node unchanged; replacements are not visited again. A
    /// caller returning `Some` is responsible for its replacement semantics.
    /// The result is `None` only if no visitor requested a replacement.
    ///
    /// Preserve input DAG sharing, including unchanged child allocations and
    /// ordered, inline UF arguments. Identity keys refer to actual borrowed
    /// input nodes, never the temporary Arcs used by `try_map_children` for
    /// inline arguments. The immutable borrowed root keeps those nodes alive.
    /// Neither hashing nor equality walks subtrees. Traversal and inline-value
    /// copying are iterative; visitor work apart, they are linear in distinct
    /// input nodes/edges, not the expanded expression tree. A no-op allocates
    /// no copied expression nodes. Visitors run bottom-up, children left first.
    pub fn try_rewrite_dag<E>(
        &self,
        rewrite: &mut dyn FnMut(&SmtExpr) -> Result<Option<SmtExpr>, E>,
    ) -> Result<Option<SmtExpr>, E> {
        let mut pending = vec![(self, false)];
        // None records a visited, unchanged input; only changed nodes need an
        // owned result. This avoids cloning nested UF values on the no-op path.
        let mut results: HashMap<*const SmtExpr, Option<Child>> = HashMap::new();
        while let Some((node, children_ready)) = pending.pop() {
            let key = node as *const SmtExpr;
            if results.contains_key(&key) {
                continue;
            }
            if !children_ready {
                pending.push((node, true));
                let first_child = pending.len();
                // The existing exhaustive inventory borrows real Arc children
                // AND real inline UF arguments, without allocating wrappers.
                node.for_each_child(&mut |child| {
                    if !results.contains_key(&(child as *const SmtExpr)) {
                        pending.push((child, false));
                    }
                });
                pending[first_child..].reverse();
                continue;
            }
            let mut changed_children = false;
            node.for_each_child(&mut |child| {
                changed_children |= results[&(child as *const SmtExpr)].is_some();
            });
            let mapped = if changed_children {
                Some(match node {
                    SmtExpr::UF {
                        name,
                        args,
                        ret_sort,
                    } => SmtExpr::UF {
                        name: name.clone(),
                        args: args
                            .iter()
                            .map(|arg| {
                                // Each inline value has exactly one physical owner,
                                // this UF argument slot. Move its changed result;
                                // copying unchanged inline UFs is iterative too.
                                match results
                                    .remove(&(arg as *const SmtExpr))
                                    .expect("visited inline child")
                                {
                                    Some(value) => own_expression(value),
                                    None => clone_inline_expression(arg),
                                }
                            })
                            .collect(),
                        ret_sort: ret_sort.clone(),
                    },
                    _ => match node.try_map_children::<Infallible>(&mut |child| {
                        Ok(results[&Arc::as_ptr(child)]
                            .as_ref()
                            .unwrap_or(child)
                            .clone())
                    }) {
                        Ok(mapped) => mapped,
                        Err(never) => match never {},
                    },
                })
            } else {
                None
            };
            let result = rewrite(mapped.as_ref().unwrap_or(node))?
                .or(mapped)
                .map(Arc::new);
            results.insert(key, result);
        }
        Ok(results
            .remove(&(self as *const SmtExpr))
            .expect("visited root")
            .map(own_expression))
    }

    /// This node with every direct child replaced by `f(child)`.
    pub fn try_map_children<E>(
        &self,
        f: &mut dyn FnMut(&Child) -> Result<Child, E>,
    ) -> Result<SmtExpr, E> {
        use SmtExpr as S;
        macro_rules! binary {
            ($variant:ident, $lhs:expr, $rhs:expr, $width:expr) => {
                S::$variant {
                    lhs: f($lhs)?,
                    rhs: f($rhs)?,
                    width: *$width,
                }
            };
        }
        macro_rules! relation {
            ($variant:ident, $lhs:expr, $rhs:expr) => {
                S::$variant {
                    lhs: f($lhs)?,
                    rhs: f($rhs)?,
                }
            };
        }
        macro_rules! rounded {
            ($variant:ident, $rm:expr, $lhs:expr, $rhs:expr) => {
                S::$variant {
                    rm: *$rm,
                    lhs: f($lhs)?,
                    rhs: f($rhs)?,
                }
            };
        }
        Ok(match self {
            S::Var { .. } | S::BvConst { .. } | S::BoolConst(_) | S::FPConst { .. } => self.clone(),
            S::UFDecl { .. } => self.clone(),
            S::BvAdd { lhs, rhs, width } => binary!(BvAdd, lhs, rhs, width),
            S::BvSub { lhs, rhs, width } => binary!(BvSub, lhs, rhs, width),
            S::BvMul { lhs, rhs, width } => binary!(BvMul, lhs, rhs, width),
            S::BvSDiv { lhs, rhs, width } => binary!(BvSDiv, lhs, rhs, width),
            S::BvUDiv { lhs, rhs, width } => binary!(BvUDiv, lhs, rhs, width),
            S::BvURem { lhs, rhs, width } => binary!(BvURem, lhs, rhs, width),
            S::TrapIfZero {
                guard,
                value,
                width,
            } => S::TrapIfZero {
                guard: f(guard)?,
                value: f(value)?,
                width: *width,
            },
            S::BvNeg { operand, width } => S::BvNeg {
                operand: f(operand)?,
                width: *width,
            },
            S::Eq { lhs, rhs } => relation!(Eq, lhs, rhs),
            S::Not { operand } => S::Not {
                operand: f(operand)?,
            },
            S::BvSlt { lhs, rhs, width } => binary!(BvSlt, lhs, rhs, width),
            S::BvSge { lhs, rhs, width } => binary!(BvSge, lhs, rhs, width),
            S::BvUge { lhs, rhs, width } => binary!(BvUge, lhs, rhs, width),
            S::And { lhs, rhs } => relation!(And, lhs, rhs),
            S::Or { lhs, rhs } => relation!(Or, lhs, rhs),
            S::BvSgt { lhs, rhs, width } => binary!(BvSgt, lhs, rhs, width),
            S::BvSle { lhs, rhs, width } => binary!(BvSle, lhs, rhs, width),
            S::BvUlt { lhs, rhs, width } => binary!(BvUlt, lhs, rhs, width),
            S::BvUgt { lhs, rhs, width } => binary!(BvUgt, lhs, rhs, width),
            S::BvUle { lhs, rhs, width } => binary!(BvUle, lhs, rhs, width),
            S::Ite {
                cond,
                then_expr,
                else_expr,
            } => S::Ite {
                cond: f(cond)?,
                then_expr: f(then_expr)?,
                else_expr: f(else_expr)?,
            },
            S::Extract {
                high,
                low,
                operand,
                width,
            } => S::Extract {
                high: *high,
                low: *low,
                operand: f(operand)?,
                width: *width,
            },
            S::BvAnd { lhs, rhs, width } => binary!(BvAnd, lhs, rhs, width),
            S::BvOr { lhs, rhs, width } => binary!(BvOr, lhs, rhs, width),
            S::BvXor { lhs, rhs, width } => binary!(BvXor, lhs, rhs, width),
            S::BvShl { lhs, rhs, width } => binary!(BvShl, lhs, rhs, width),
            S::BvLshr { lhs, rhs, width } => binary!(BvLshr, lhs, rhs, width),
            S::BvAshr { lhs, rhs, width } => binary!(BvAshr, lhs, rhs, width),
            S::Concat { hi, lo, width } => S::Concat {
                hi: f(hi)?,
                lo: f(lo)?,
                width: *width,
            },
            S::ZeroExtend {
                operand,
                extra_bits,
                width,
            } => S::ZeroExtend {
                operand: f(operand)?,
                extra_bits: *extra_bits,
                width: *width,
            },
            S::SignExtend {
                operand,
                extra_bits,
                width,
            } => S::SignExtend {
                operand: f(operand)?,
                extra_bits: *extra_bits,
                width: *width,
            },
            S::Select { array, index } => S::Select {
                array: f(array)?,
                index: f(index)?,
            },
            S::Store {
                array,
                index,
                value,
            } => S::Store {
                array: f(array)?,
                index: f(index)?,
                value: f(value)?,
            },
            S::ConstArray { index_sort, value } => S::ConstArray {
                index_sort: index_sort.clone(),
                value: f(value)?,
            },
            S::MemLoad {
                addr,
                load_bits,
                signed,
                result_width,
            } => S::MemLoad {
                addr: f(addr)?,
                load_bits: *load_bits,
                signed: *signed,
                result_width: *result_width,
            },
            S::FPAdd { rm, lhs, rhs } => rounded!(FPAdd, rm, lhs, rhs),
            S::FPMul { rm, lhs, rhs } => rounded!(FPMul, rm, lhs, rhs),
            S::FPSub { rm, lhs, rhs } => rounded!(FPSub, rm, lhs, rhs),
            S::FPDiv { rm, lhs, rhs } => rounded!(FPDiv, rm, lhs, rhs),
            S::FPNeg { operand } => S::FPNeg {
                operand: f(operand)?,
            },
            S::FPEq { lhs, rhs } => relation!(FPEq, lhs, rhs),
            S::FPLt { lhs, rhs } => relation!(FPLt, lhs, rhs),
            S::FPGt { lhs, rhs } => relation!(FPGt, lhs, rhs),
            S::FPGe { lhs, rhs } => relation!(FPGe, lhs, rhs),
            S::FPLe { lhs, rhs } => relation!(FPLe, lhs, rhs),
            S::FPSqrt { rm, operand } => S::FPSqrt {
                rm: *rm,
                operand: f(operand)?,
            },
            S::FPRoundToIntegral { rm, operand } => S::FPRoundToIntegral {
                rm: *rm,
                operand: f(operand)?,
            },
            S::FPAbs { operand } => S::FPAbs {
                operand: f(operand)?,
            },
            S::FPFma { rm, a, b, c } => S::FPFma {
                rm: *rm,
                a: f(a)?,
                b: f(b)?,
                c: f(c)?,
            },
            S::FPIsNaN { operand } => S::FPIsNaN {
                operand: f(operand)?,
            },
            S::FPIsInf { operand } => S::FPIsInf {
                operand: f(operand)?,
            },
            S::FPIsZero { operand } => S::FPIsZero {
                operand: f(operand)?,
            },
            S::FPIsNormal { operand } => S::FPIsNormal {
                operand: f(operand)?,
            },
            S::FPToSBv {
                rm,
                operand,
                width,
                mode,
            } => S::FPToSBv {
                rm: *rm,
                operand: f(operand)?,
                width: *width,
                mode: *mode,
            },
            S::FPToUBv { rm, operand, width } => S::FPToUBv {
                rm: *rm,
                operand: f(operand)?,
                width: *width,
            },
            S::BvToFP {
                rm,
                operand,
                eb,
                sb,
            } => S::BvToFP {
                rm: *rm,
                operand: f(operand)?,
                eb: *eb,
                sb: *sb,
            },
            S::FPToFP {
                rm,
                operand,
                eb,
                sb,
            } => S::FPToFP {
                rm: *rm,
                operand: f(operand)?,
                eb: *eb,
                sb: *sb,
            },
            S::BvBitsToFP { operand, eb, sb } => S::BvBitsToFP {
                operand: f(operand)?,
                eb: *eb,
                sb: *sb,
            },
            S::UF {
                name,
                args,
                ret_sort,
            } => S::UF {
                name: name.clone(),
                args: args
                    .iter()
                    .map(|arg| f(&Arc::new(arg.clone())).map(|mapped| (*mapped).clone()))
                    .collect::<Result<_, E>>()?,
                ret_sort: ret_sort.clone(),
            },
            S::ForAll {
                var,
                var_width,
                lower,
                upper,
                body,
            } => S::ForAll {
                var: var.clone(),
                var_width: *var_width,
                lower: f(lower)?,
                upper: f(upper)?,
                body: f(body)?,
            },
            S::Exists {
                var,
                var_width,
                lower,
                upper,
                body,
            } => S::Exists {
                var: var.clone(),
                var_width: *var_width,
                lower: f(lower)?,
                upper: f(upper)?,
                body: f(body)?,
            },
        })
    }
}

#[cfg(test)]
#[path = "smt_map_tests.rs"]
mod tests;
