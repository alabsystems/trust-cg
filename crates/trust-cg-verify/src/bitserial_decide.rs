// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Exact, in-process decision of bit-vector equalities whose terms are
//! bit-serial: every bit of every subterm is a function of the bits at the
//! same or lower positions and of a finite amount of carried state.
//!
//! # The fragment
//!
//! Bit-vector terms: variables (at most 64 bits), constants, `bvadd`,
//! `bvsub`, `bvneg`, `bvand`, `bvor`, `bvxor`, `zero_extend`, `sign_extend`
//! and `extract` of the LOW bits (`(_ extract h 0)`). Boolean terms: `true`,
//! `false`, `not`, `and`, `or`, `ite` over Booleans, `=` between Booleans or
//! between bit-vectors, and the eight unsigned and signed orderings. Anything
//! else (a multiplication, a shift, a high `extract`, a `concat`, an `ite`
//! choosing between bit-vectors, an array, a floating-point term) is
//! [`Unsupported`]: it is refused, never approximated.
//!
//! # The procedure
//!
//! The terms of both sides are compiled into one synchronous automaton that
//! reads the input variables least-significant bit first. Its state is one
//! carry per adder, subtractor or negation, one stored sign bit per sign
//! extension and an `(lt, eq)` pair per comparison; comparisons decide the
//! most significant differing bit last, and a signed comparison inverts both
//! sign bits. Starting from the single initial state, the procedure computes
//! the set of states reachable after each bit position under EVERY assignment
//! of the input bits at that position, so after the last position it holds
//! the state of every complete input assignment. The equality holds iff it
//! holds in every reachable final state. When it fails in one, the input bits
//! that reached that state are read back along recorded predecessors, and the
//! resulting assignment is re-evaluated by [`SmtExpr::eval`]: a witness the
//! ordinary evaluator does not confirm is reported as an internal
//! disagreement, never as a refutation.
//!
//! # What a verdict is worth
//!
//! [`Exact::Holds`] covers every input assignment, not a sample, and
//! [`Exact::Refuted`] carries a concrete counterexample. Both are decisions
//! made by this unverified Rust procedure about the terms it was handed:
//! testing-grade evidence, not an independently checked certificate.

use std::collections::HashMap;
use std::sync::Arc;

use crate::smt::{EvalEnv, EvalResult, SmtExpr, SmtSort};

/// Most state bits the automaton carries.
const MAX_STATE_BITS: usize = 128;
/// Most bit positions (the widest supported bit-vector term).
const MAX_POSITIONS: u32 = 130;
/// Most reachable states kept at one position before the decision gives up.
const MAX_STATES_PER_POSITION: usize = 1 << 16;

/// The decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Exact {
    /// Both sides agree on every assignment of their variables.
    Holds,
    /// The sides differ on this assignment (every variable of either side).
    Refuted(Vec<(String, u64)>),
}

/// Why a pair of terms was not decided.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("not decided by the bit-serial procedure: {0}")]
pub struct Unsupported(pub String);

fn unsupported<T>(why: impl Into<String>) -> Result<T, Unsupported> {
    Err(Unsupported(why.into()))
}

#[derive(Clone, Copy, Debug)]
enum Bv {
    Var {
        var: usize,
        width: u32,
    },
    Const {
        value: u64,
        width: u32,
    },
    Add {
        a: usize,
        b: usize,
        width: u32,
        carry: usize,
    },
    Sub {
        a: usize,
        b: usize,
        width: u32,
        carry: usize,
    },
    Neg {
        a: usize,
        width: u32,
        carry: usize,
    },
    And {
        a: usize,
        b: usize,
        width: u32,
    },
    Or {
        a: usize,
        b: usize,
        width: u32,
    },
    Xor {
        a: usize,
        b: usize,
        width: u32,
    },
    Zext {
        a: usize,
        from: u32,
        width: u32,
    },
    Sext {
        a: usize,
        from: u32,
        width: u32,
        sign: usize,
    },
    Low {
        a: usize,
        width: u32,
    },
}

impl Bv {
    fn width(self) -> u32 {
        match self {
            Self::Var { width, .. }
            | Self::Const { width, .. }
            | Self::Add { width, .. }
            | Self::Sub { width, .. }
            | Self::Neg { width, .. }
            | Self::And { width, .. }
            | Self::Or { width, .. }
            | Self::Xor { width, .. }
            | Self::Zext { width, .. }
            | Self::Sext { width, .. }
            | Self::Low { width, .. } => width,
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Order {
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Clone, Copy, Debug)]
enum Bool {
    Const(bool),
    Not(usize),
    And(usize, usize),
    Or(usize, usize),
    Ite(usize, usize, usize),
    Iff(usize, usize),
    Compare { compare: usize, order: Order },
}

#[derive(Clone, Copy, Debug)]
struct Compare {
    a: usize,
    b: usize,
    width: u32,
    signed: bool,
    lt: usize,
    eq: usize,
}

#[derive(Default)]
struct Automaton {
    vars: Vec<(String, u32)>,
    bv: Vec<Bv>,
    bools: Vec<Bool>,
    compares: Vec<Compare>,
    state_bits: usize,
    initial: u128,
    bv_memo: HashMap<SmtExpr, usize>,
    bool_memo: HashMap<SmtExpr, usize>,
    compare_memo: HashMap<(usize, usize, bool), usize>,
}

fn bit(state: u128, index: usize) -> bool {
    (state >> index) & 1 == 1
}

fn set(state: &mut u128, index: usize, value: bool) {
    if value {
        *state |= 1 << index;
    } else {
        *state &= !(1 << index);
    }
}

impl Automaton {
    fn state_bit(&mut self, initial: bool) -> Result<usize, Unsupported> {
        if self.state_bits >= MAX_STATE_BITS {
            return unsupported(format!("more than {MAX_STATE_BITS} state bits"));
        }
        let index = self.state_bits;
        self.state_bits += 1;
        set(&mut self.initial, index, initial);
        Ok(index)
    }

    fn push_bv(&mut self, node: Bv) -> Result<usize, Unsupported> {
        if node.width() == 0 || node.width() > MAX_POSITIONS {
            return unsupported(format!("bit-vector width {}", node.width()));
        }
        self.bv.push(node);
        Ok(self.bv.len() - 1)
    }

    fn same_width(&self, a: usize, b: usize, what: &str) -> Result<u32, Unsupported> {
        let (wa, wb) = (self.bv[a].width(), self.bv[b].width());
        if wa != wb {
            return unsupported(format!("{what} of widths {wa} and {wb}"));
        }
        Ok(wa)
    }

    fn compile_bv(&mut self, expr: &SmtExpr) -> Result<usize, Unsupported> {
        if let Some(&id) = self.bv_memo.get(expr) {
            return Ok(id);
        }
        let id = match expr {
            SmtExpr::Var { name, width } => {
                if *width == 0 || *width > 64 {
                    return unsupported(format!("variable {name} of width {width}"));
                }
                let var = match self.vars.iter().position(|(seen, _)| seen == name) {
                    Some(var) if self.vars[var].1 == *width => var,
                    Some(var) => {
                        return unsupported(format!(
                            "variable {name} used at widths {} and {width}",
                            self.vars[var].1
                        ));
                    }
                    None => {
                        if self.vars.len() >= 16 {
                            return unsupported("more than 16 variables");
                        }
                        self.vars.push((name.clone(), *width));
                        self.vars.len() - 1
                    }
                };
                self.push_bv(Bv::Var { var, width: *width })?
            }
            SmtExpr::BvConst { value, width } => self.push_bv(Bv::Const {
                value: *value,
                width: *width,
            })?,
            SmtExpr::BvAdd { lhs, rhs, width }
            | SmtExpr::BvSub { lhs, rhs, width }
            | SmtExpr::BvAnd { lhs, rhs, width }
            | SmtExpr::BvOr { lhs, rhs, width }
            | SmtExpr::BvXor { lhs, rhs, width } => {
                let a = self.compile_bv(lhs)?;
                let b = self.compile_bv(rhs)?;
                let operands = self.same_width(a, b, "binary operation")?;
                if operands != *width {
                    return unsupported(format!(
                        "operands of width {operands} under a width-{width} node"
                    ));
                }
                let width = *width;
                let node = match expr {
                    SmtExpr::BvAdd { .. } => Bv::Add {
                        a,
                        b,
                        width,
                        carry: self.state_bit(false)?,
                    },
                    SmtExpr::BvSub { .. } => Bv::Sub {
                        a,
                        b,
                        width,
                        carry: self.state_bit(true)?,
                    },
                    SmtExpr::BvAnd { .. } => Bv::And { a, b, width },
                    SmtExpr::BvOr { .. } => Bv::Or { a, b, width },
                    _ => Bv::Xor { a, b, width },
                };
                self.push_bv(node)?
            }
            SmtExpr::BvNeg { operand, width } => {
                let a = self.compile_bv(operand)?;
                if self.bv[a].width() != *width {
                    return unsupported("negation width mismatch");
                }
                let carry = self.state_bit(true)?;
                self.push_bv(Bv::Neg {
                    a,
                    width: *width,
                    carry,
                })?
            }
            SmtExpr::ZeroExtend {
                operand,
                extra_bits,
                ..
            }
            | SmtExpr::SignExtend {
                operand,
                extra_bits,
                ..
            } => {
                let a = self.compile_bv(operand)?;
                let from = self.bv[a].width();
                let width = from + extra_bits;
                if *extra_bits == 0 {
                    a
                } else if matches!(expr, SmtExpr::ZeroExtend { .. }) {
                    self.push_bv(Bv::Zext { a, from, width })?
                } else {
                    let sign = self.state_bit(false)?;
                    self.push_bv(Bv::Sext {
                        a,
                        from,
                        width,
                        sign,
                    })?
                }
            }
            SmtExpr::Extract {
                high, low, operand, ..
            } => {
                if *low != 0 {
                    return unsupported(format!("extract [{high}:{low}] above bit 0"));
                }
                let a = self.compile_bv(operand)?;
                if *high >= self.bv[a].width() {
                    return unsupported("extract beyond its operand");
                }
                if *high + 1 == self.bv[a].width() {
                    a
                } else {
                    self.push_bv(Bv::Low { a, width: high + 1 })?
                }
            }
            other => {
                return unsupported(format!("bit-vector term {}", term_kind(other)));
            }
        };
        self.bv_memo.insert(expr.clone(), id);
        Ok(id)
    }

    fn compare(&mut self, a: usize, b: usize, signed: bool) -> Result<usize, Unsupported> {
        if let Some(&id) = self.compare_memo.get(&(a, b, signed)) {
            return Ok(id);
        }
        let width = self.same_width(a, b, "comparison")?;
        let lt = self.state_bit(false)?;
        let eq = self.state_bit(true)?;
        self.compares.push(Compare {
            a,
            b,
            width,
            signed,
            lt,
            eq,
        });
        let id = self.compares.len() - 1;
        self.compare_memo.insert((a, b, signed), id);
        Ok(id)
    }

    fn push_bool(&mut self, node: Bool) -> usize {
        self.bools.push(node);
        self.bools.len() - 1
    }

    fn compile_bool(&mut self, expr: &SmtExpr) -> Result<usize, Unsupported> {
        if let Some(&id) = self.bool_memo.get(expr) {
            return Ok(id);
        }
        let ordered = |lhs: &Arc<SmtExpr>, rhs: &Arc<SmtExpr>, signed, order, this: &mut Self| {
            let a = this.compile_bv(lhs)?;
            let b = this.compile_bv(rhs)?;
            let compare = this.compare(a, b, signed)?;
            Ok::<usize, Unsupported>(this.push_bool(Bool::Compare { compare, order }))
        };
        let id = match expr {
            SmtExpr::BoolConst(value) => self.push_bool(Bool::Const(*value)),
            SmtExpr::Not { operand } => {
                let a = self.compile_bool(operand)?;
                self.push_bool(Bool::Not(a))
            }
            SmtExpr::And { lhs, rhs } => {
                let a = self.compile_bool(lhs)?;
                let b = self.compile_bool(rhs)?;
                self.push_bool(Bool::And(a, b))
            }
            SmtExpr::Or { lhs, rhs } => {
                let a = self.compile_bool(lhs)?;
                let b = self.compile_bool(rhs)?;
                self.push_bool(Bool::Or(a, b))
            }
            SmtExpr::Ite {
                cond,
                then_expr,
                else_expr,
            } => {
                if then_expr.sort() != SmtSort::Bool {
                    return unsupported("ite choosing between bit-vectors");
                }
                let c = self.compile_bool(cond)?;
                let t = self.compile_bool(then_expr)?;
                let e = self.compile_bool(else_expr)?;
                self.push_bool(Bool::Ite(c, t, e))
            }
            SmtExpr::Eq { lhs, rhs } => {
                if lhs.sort() == SmtSort::Bool {
                    let a = self.compile_bool(lhs)?;
                    let b = self.compile_bool(rhs)?;
                    self.push_bool(Bool::Iff(a, b))
                } else {
                    ordered(lhs, rhs, false, Order::Eq, self)?
                }
            }
            SmtExpr::BvUlt { lhs, rhs, .. } => ordered(lhs, rhs, false, Order::Lt, self)?,
            SmtExpr::BvUle { lhs, rhs, .. } => ordered(lhs, rhs, false, Order::Le, self)?,
            SmtExpr::BvUgt { lhs, rhs, .. } => ordered(lhs, rhs, false, Order::Gt, self)?,
            SmtExpr::BvUge { lhs, rhs, .. } => ordered(lhs, rhs, false, Order::Ge, self)?,
            SmtExpr::BvSlt { lhs, rhs, .. } => ordered(lhs, rhs, true, Order::Lt, self)?,
            SmtExpr::BvSle { lhs, rhs, .. } => ordered(lhs, rhs, true, Order::Le, self)?,
            SmtExpr::BvSgt { lhs, rhs, .. } => ordered(lhs, rhs, true, Order::Gt, self)?,
            SmtExpr::BvSge { lhs, rhs, .. } => ordered(lhs, rhs, true, Order::Ge, self)?,
            other => return unsupported(format!("Boolean term {}", term_kind(other))),
        };
        self.bool_memo.insert(expr.clone(), id);
        Ok(id)
    }

    /// The state after reading position `j` with these variable bits.
    fn step(&self, j: u32, state: u128, inputs: u64, bits: &mut [bool]) -> u128 {
        let mut next = state;
        for (index, node) in self.bv.iter().enumerate() {
            if j >= node.width() {
                continue;
            }
            bits[index] = match *node {
                Bv::Var { var, .. } => (inputs >> var) & 1 == 1,
                Bv::Const { value, .. } => j < 64 && (value >> j) & 1 == 1,
                Bv::Add { a, b, carry, .. } | Bv::Sub { a, b, carry, .. } => {
                    let x = bits[a];
                    let y = if matches!(node, Bv::Sub { .. }) {
                        !bits[b]
                    } else {
                        bits[b]
                    };
                    let c = bit(state, carry);
                    set(&mut next, carry, (x & y) | (x & c) | (y & c));
                    x ^ y ^ c
                }
                Bv::Neg { a, carry, .. } => {
                    let x = !bits[a];
                    let c = bit(state, carry);
                    set(&mut next, carry, x & c);
                    x ^ c
                }
                Bv::And { a, b, .. } => bits[a] & bits[b],
                Bv::Or { a, b, .. } => bits[a] | bits[b],
                Bv::Xor { a, b, .. } => bits[a] ^ bits[b],
                Bv::Zext { a, from, .. } => j < from && bits[a],
                Bv::Sext { a, from, sign, .. } => {
                    if j < from {
                        if j + 1 == from {
                            set(&mut next, sign, bits[a]);
                        }
                        bits[a]
                    } else {
                        bit(state, sign)
                    }
                }
                Bv::Low { a, .. } => bits[a],
            };
        }
        for compare in &self.compares {
            if j >= compare.width {
                continue;
            }
            let (mut x, mut y) = (bits[compare.a], bits[compare.b]);
            if compare.signed && j + 1 == compare.width {
                x = !x;
                y = !y;
            }
            set(&mut next, compare.eq, bit(state, compare.eq) && x == y);
            if x != y {
                set(&mut next, compare.lt, y);
            }
        }
        next
    }

    fn eval_bool(&self, node: usize, state: u128) -> bool {
        match self.bools[node] {
            Bool::Const(value) => value,
            Bool::Not(a) => !self.eval_bool(a, state),
            Bool::And(a, b) => self.eval_bool(a, state) && self.eval_bool(b, state),
            Bool::Or(a, b) => self.eval_bool(a, state) || self.eval_bool(b, state),
            Bool::Ite(c, t, e) => {
                if self.eval_bool(c, state) {
                    self.eval_bool(t, state)
                } else {
                    self.eval_bool(e, state)
                }
            }
            Bool::Iff(a, b) => self.eval_bool(a, state) == self.eval_bool(b, state),
            Bool::Compare { compare, order } => {
                let compare = self.compares[compare];
                let (lt, eq) = (bit(state, compare.lt), bit(state, compare.eq));
                match order {
                    Order::Eq => eq,
                    Order::Lt => lt,
                    Order::Le => lt || eq,
                    Order::Gt => !lt && !eq,
                    Order::Ge => !lt,
                }
            }
        }
    }

    /// Decide `goal` over every assignment.
    fn decide(&self, goal: usize) -> Result<Option<Vec<u64>>, Unsupported> {
        let positions = self.bv.iter().map(|node| node.width()).max().unwrap_or(0);
        let mut bits = vec![false; self.bv.len()];
        // Per position: reached state -> (predecessor state, input bits).
        let mut trail: Vec<HashMap<u128, (u128, u64)>> = Vec::with_capacity(positions as usize);
        let mut layer: Vec<u128> = vec![self.initial];
        for j in 0..positions {
            let active: Vec<usize> = (0..self.vars.len())
                .filter(|&var| j < self.vars[var].1)
                .collect();
            let mut reached: HashMap<u128, (u128, u64)> = HashMap::new();
            for &state in &layer {
                for combo in 0u64..(1u64 << active.len()) {
                    let mut inputs = 0u64;
                    for (k, &var) in active.iter().enumerate() {
                        inputs |= ((combo >> k) & 1) << var;
                    }
                    let next = self.step(j, state, inputs, &mut bits);
                    reached.entry(next).or_insert((state, inputs));
                }
            }
            if reached.len() > MAX_STATES_PER_POSITION {
                return unsupported(format!("{} reachable states at bit {j}", reached.len()));
            }
            layer = reached.keys().copied().collect();
            layer.sort_unstable();
            trail.push(reached);
        }
        let Some(&failing) = layer.iter().find(|&&state| !self.eval_bool(goal, state)) else {
            return Ok(None);
        };
        let mut values = vec![0u64; self.vars.len()];
        let mut state = failing;
        for j in (0..positions).rev() {
            let (previous, inputs) = trail[j as usize][&state];
            for (var, value) in values.iter_mut().enumerate() {
                if j < self.vars[var].1 && (inputs >> var) & 1 == 1 {
                    *value |= 1u64 << j;
                }
            }
            state = previous;
        }
        Ok(Some(values))
    }
}

fn term_kind(expr: &SmtExpr) -> String {
    let debug = format!("{expr:?}");
    debug
        .split(|c: char| !c.is_alphanumeric())
        .next()
        .unwrap_or("?")
        .to_string()
}

/// Decide `lhs == rhs` (Boolean `iff`, or bit-vector equality of all bits) for
/// every assignment of the variables of both sides.
pub fn decide_equal(lhs: &SmtExpr, rhs: &SmtExpr) -> Result<Exact, Unsupported> {
    let mut automaton = Automaton::default();
    let goal = match (lhs.sort(), rhs.sort()) {
        (SmtSort::Bool, SmtSort::Bool) => {
            let a = automaton.compile_bool(lhs)?;
            let b = automaton.compile_bool(rhs)?;
            automaton.push_bool(Bool::Iff(a, b))
        }
        (SmtSort::BitVec(_), SmtSort::BitVec(_)) => {
            let a = automaton.compile_bv(lhs)?;
            let b = automaton.compile_bv(rhs)?;
            let compare = automaton.compare(a, b, false)?;
            automaton.push_bool(Bool::Compare {
                compare,
                order: Order::Eq,
            })
        }
        (left, right) => return unsupported(format!("sides of sorts {left:?} and {right:?}")),
    };
    let Some(values) = automaton.decide(goal)? else {
        return Ok(Exact::Holds);
    };
    let witness: Vec<(String, u64)> = automaton
        .vars
        .iter()
        .zip(values)
        .map(|((name, _), value)| (name.clone(), value))
        .collect();
    // The ordinary evaluator must confirm the witness.
    let mut env = EvalEnv::default();
    for (name, value) in &witness {
        env.insert(name.clone(), *value);
    }
    let (left, right) = (lhs.eval(&env), rhs.eval(&env));
    if evaluations_equal(&left, &right) {
        return unsupported(format!(
            "internal disagreement: the automaton's witness {witness:?} does not separate the \
             sides under the evaluator ({left:?} vs {right:?})"
        ));
    }
    Ok(Exact::Refuted(witness))
}

/// Equality of two evaluator results of the same sort.
pub(crate) fn evaluations_equal(left: &EvalResult, right: &EvalResult) -> bool {
    left.semantically_equal(right)
}

/// The direct subterms of the term kinds the trap-expansion obligations use;
/// `None` for any other kind.
pub(crate) fn children(expr: &SmtExpr) -> Option<Vec<&SmtExpr>> {
    Some(match expr {
        SmtExpr::Var { .. } | SmtExpr::BvConst { .. } | SmtExpr::BoolConst(_) => Vec::new(),
        SmtExpr::BvAdd { lhs, rhs, .. }
        | SmtExpr::BvSub { lhs, rhs, .. }
        | SmtExpr::BvMul { lhs, rhs, .. }
        | SmtExpr::BvAnd { lhs, rhs, .. }
        | SmtExpr::BvOr { lhs, rhs, .. }
        | SmtExpr::BvXor { lhs, rhs, .. }
        | SmtExpr::BvAshr { lhs, rhs, .. }
        | SmtExpr::Eq { lhs, rhs }
        | SmtExpr::And { lhs, rhs }
        | SmtExpr::Or { lhs, rhs }
        | SmtExpr::BvUlt { lhs, rhs, .. }
        | SmtExpr::BvUle { lhs, rhs, .. }
        | SmtExpr::BvUgt { lhs, rhs, .. }
        | SmtExpr::BvUge { lhs, rhs, .. }
        | SmtExpr::BvSlt { lhs, rhs, .. }
        | SmtExpr::BvSle { lhs, rhs, .. }
        | SmtExpr::BvSgt { lhs, rhs, .. }
        | SmtExpr::BvSge { lhs, rhs, .. } => vec![lhs.as_ref(), rhs.as_ref()],
        SmtExpr::Concat { hi, lo, .. } => vec![hi.as_ref(), lo.as_ref()],
        SmtExpr::BvNeg { operand, .. }
        | SmtExpr::Not { operand }
        | SmtExpr::Extract { operand, .. }
        | SmtExpr::ZeroExtend { operand, .. }
        | SmtExpr::SignExtend { operand, .. } => vec![operand.as_ref()],
        SmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => vec![cond.as_ref(), then_expr.as_ref(), else_expr.as_ref()],
        _ => return None,
    })
}

/// Variables of a term in first-seen order (name, width); `None` when the
/// term contains a kind [`children`] does not walk.
pub(crate) fn variables(expr: &SmtExpr) -> Option<Vec<(String, u32)>> {
    fn walk(expr: &SmtExpr, out: &mut Vec<(String, u32)>) -> Option<()> {
        if let SmtExpr::Var { name, width } = expr {
            if !out.iter().any(|(seen, _)| seen == name) {
                out.push((name.clone(), *width));
            }
            return Some(());
        }
        for child in children(expr)? {
            walk(child, out)?;
        }
        Some(())
    }
    let mut out = Vec::new();
    walk(expr, &mut out)?;
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(name: &str, width: u32) -> SmtExpr {
        SmtExpr::var(name, width)
    }

    fn c(value: u64, width: u32) -> SmtExpr {
        SmtExpr::bv_const(value, width)
    }

    /// Exhaustive check of `decide_equal` against the evaluator at 4 bits.
    fn agrees_with_enumeration(lhs: &SmtExpr, rhs: &SmtExpr) {
        let vars = {
            let mut all = variables(lhs).unwrap();
            for var in variables(rhs).unwrap() {
                if !all.contains(&var) {
                    all.push(var);
                }
            }
            all
        };
        let total_bits: u32 = vars.iter().map(|(_, w)| *w).sum();
        assert!(total_bits <= 16);
        let mut differs = false;
        for assignment in 0u64..(1u64 << total_bits) {
            let mut env = EvalEnv::default();
            let mut shift = 0;
            for (name, width) in &vars {
                env.insert(name.clone(), (assignment >> shift) & ((1u64 << width) - 1));
                shift += width;
            }
            if !evaluations_equal(&lhs.eval(&env), &rhs.eval(&env)) {
                differs = true;
                break;
            }
        }
        match decide_equal(lhs, rhs).unwrap() {
            Exact::Holds => assert!(!differs, "{lhs:?} vs {rhs:?}"),
            Exact::Refuted(_) => assert!(differs, "{lhs:?} vs {rhs:?}"),
        }
    }

    #[test]
    fn subtraction_carry_is_unsigned_greater_or_equal_at_every_width() {
        for width in [1u32, 4, 8, 32, 64] {
            let (a, b) = (v("a", width), v("b", width));
            let ones = if width == 64 {
                u64::MAX
            } else {
                (1u64 << width) - 1
            };
            let sum = a
                .clone()
                .zero_ext(1)
                .bvadd(b.clone().bvxor(c(ones, width)).zero_ext(1))
                .bvadd(c(1, width + 1));
            let result = sum.clone().extract(width - 1, 0);
            let carry = result.zero_ext(1).eq_expr(sum).not_expr();
            assert_eq!(
                decide_equal(&carry, &a.clone().bvuge(b.clone())),
                Ok(Exact::Holds),
                "width {width}"
            );
            // Off by one: the carry is not `a > b`.
            match decide_equal(&carry, &a.clone().bvugt(b)) {
                Ok(Exact::Refuted(witness)) => assert_eq!(witness[0].1, witness[1].1),
                other => panic!("width {width}: {other:?}"),
            }
        }
    }

    #[test]
    fn signed_overflow_and_orderings_agree_with_enumeration() {
        let (a, b) = (v("a", 4), v("b", 4));
        let wide = a.clone().sign_ext(1).bvadd(b.clone().sign_ext(1));
        let narrow = a.clone().bvadd(b.clone()).sign_ext(1);
        let overflow = wide.eq_expr(narrow).not_expr();
        let sign_rule = a
            .clone()
            .bvslt(c(0, 4))
            .eq_expr(b.clone().bvslt(c(0, 4)))
            .and_expr(
                a.clone()
                    .bvslt(c(0, 4))
                    .eq_expr(a.clone().bvadd(b.clone()).bvslt(c(0, 4)))
                    .not_expr(),
            );
        agrees_with_enumeration(&overflow, &sign_rule);
        agrees_with_enumeration(&overflow, &a.clone().bvslt(b.clone()));
        agrees_with_enumeration(&a.clone().bvsub(b.clone()), &b.clone().bvsub(a.clone()));
        agrees_with_enumeration(&a.clone().bvneg(), &c(0, 4).bvsub(a.clone()));
        agrees_with_enumeration(&a.clone().zero_ext(4).extract(3, 0), &a.clone());
    }

    #[test]
    fn refuses_terms_outside_the_fragment() {
        let (a, b) = (v("a", 8), v("b", 8));
        assert!(decide_equal(&a.clone().bvmul(b.clone()), &b.clone().bvmul(a.clone())).is_err());
        assert!(decide_equal(&a.clone().extract(7, 1), &b.extract(7, 1)).is_err());
        assert!(decide_equal(&v("wide", 65), &v("wide", 65)).is_err());
    }
}
