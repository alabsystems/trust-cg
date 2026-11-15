// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Exact, in-process decision of bit-vector equalities whose terms are affine
//! over GF(2): every bit of every subterm is a constant XOR-ed with a set of
//! input bits.
//!
//! # Why a second exact procedure
//!
//! [`crate::bitserial_decide`] decides terms whose bits depend only on bits at
//! the same or lower positions (adders, comparisons). A cyclic-redundancy
//! check is the opposite shape: polynomial division moves information from
//! the high bits down (Arm's `Poly32Mod2`) or from bit 0 across the whole word
//! (the reflected shift register), so it has no bit-serial form. It is,
//! however, linear over GF(2) in its inputs, and so is every term this module
//! accepts.
//!
//! # The fragment
//!
//! Bit-vector terms of at most 128 bits: variables, constants, `extract`,
//! `concat`, `zero_extend`, `bvxor`, `bvand`/`bvor` where at every bit one
//! operand is constant, `bvshl`/`bvlshr` by a constant amount, and `ite` whose
//! condition is affine and whose two arms differ by a constant at every bit
//! (or whose condition is constant). Boolean terms: `true`, `false`, `not`,
//! `=` between Booleans or between bit-vectors whose difference has at most one
//! non-constant bit, and `ite` over Booleans under the same arm rule. Anything
//! else (an addition, a product, a comparison, an `ite` whose arms differ by a
//! non-constant, an `and` of two input bits) is [`Gf2Error::Unsupported`]: it
//! is refused, never approximated.
//!
//! # The procedure
//!
//! Each bit of each subterm is computed as an affine form `c XOR x_i XOR ...`
//! over the bits of the input variables, by structural recursion memoized on
//! the node's address, so a term that SHARES subterms (an unrolled division
//! whose every step reads the previous remainder three times) is evaluated in
//! time linear in its distinct nodes, never as the exponential tree it spells.
//! Every rule above computes, for every input assignment, exactly the bit the
//! operator's SMT-LIB semantics gives, and an affine form over GF(2) is
//! canonical (two forms are the same function iff they have the same constant
//! and the same input set), so two terms are equal for EVERY input iff their
//! forms agree bit for bit.
//!
//! When they differ at a bit, the difference is a non-zero affine form, and
//! the assignment that sets at most one of its input bits makes it one. That
//! witness is re-evaluated by [`eval_concrete`], a separate memoized concrete
//! evaluator over the same terms; a witness it does not confirm is reported as
//! an internal disagreement ([`Gf2Error::Disagreement`]), never as a
//! refutation.
//!
//! # What a verdict is worth
//!
//! [`Gf2Exact::Holds`] covers every input assignment, not a sample, and
//! [`Gf2Exact::Refuted`] carries a confirmed counterexample. Both are decisions
//! made by this unverified Rust procedure about the terms it was handed:
//! testing-grade evidence, not an independently checked certificate.

use std::collections::HashMap;
use std::rc::Rc;

use crate::smt::SmtExpr;

/// Most input bits over all variables of one decision.
pub const MAX_INPUT_BITS: usize = 256;
/// Widest supported bit-vector term.
pub const MAX_WIDTH: u32 = 128;

const WORDS: usize = MAX_INPUT_BITS / 64;

/// An affine form over GF(2): `constant XOR (XOR of the input bits in lin)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Affine {
    lin: [u64; WORDS],
    constant: bool,
}

impl Affine {
    const ZERO: Self = Self {
        lin: [0; WORDS],
        constant: false,
    };

    fn constant(value: bool) -> Self {
        Self {
            lin: [0; WORDS],
            constant: value,
        }
    }

    fn input(index: usize) -> Self {
        let mut lin = [0; WORDS];
        lin[index / 64] |= 1u64 << (index % 64);
        Self {
            lin,
            constant: false,
        }
    }

    fn xor(self, other: Self) -> Self {
        let mut lin = self.lin;
        for (word, other) in lin.iter_mut().zip(other.lin) {
            *word ^= other;
        }
        Self {
            lin,
            constant: self.constant ^ other.constant,
        }
    }

    fn flip(self) -> Self {
        Self {
            lin: self.lin,
            constant: !self.constant,
        }
    }

    /// The value when the form reads no input bit.
    pub fn as_constant(&self) -> Option<bool> {
        self.lin
            .iter()
            .all(|word| *word == 0)
            .then_some(self.constant)
    }

    /// The input bits the form reads, ascending.
    pub fn inputs(&self) -> Vec<usize> {
        let mut out = Vec::new();
        for (w, word) in self.lin.iter().enumerate() {
            let mut bits = *word;
            while bits != 0 {
                let b = bits.trailing_zeros() as usize;
                out.push(w * 64 + b);
                bits &= bits - 1;
            }
        }
        out
    }

    /// The constant term.
    pub fn constant_term(&self) -> bool {
        self.constant
    }
}

/// Why a pair of terms was not decided.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum Gf2Error {
    /// A term outside the affine fragment: refused, never approximated.
    #[error("not decided by the GF(2)-affine procedure: {0}")]
    Unsupported(String),
    /// The concrete evaluator did not confirm the symbolic counterexample.
    #[error("GF(2)-affine procedure internal disagreement: {0}")]
    Disagreement(String),
}

fn unsupported<T>(why: impl Into<String>) -> Result<T, Gf2Error> {
    Err(Gf2Error::Unsupported(why.into()))
}

/// The decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Gf2Exact {
    /// Both sides agree on every assignment of their variables.
    Holds,
    /// The sides differ on this assignment (every variable of either side),
    /// confirmed by [`eval_concrete`].
    Refuted(Vec<(String, u128)>),
}

/// The input bits: one contiguous range per variable, in first-seen order.
#[derive(Debug, Default, Clone)]
struct Inputs {
    vars: Vec<(String, u32)>,
    offsets: HashMap<String, (usize, u32)>,
    next: usize,
}

impl Inputs {
    fn bits_of(&mut self, name: &str, width: u32) -> Result<usize, Gf2Error> {
        if let Some(&(offset, known)) = self.offsets.get(name) {
            if known != width {
                return unsupported(format!(
                    "variable {name} is used at widths {known} and {width}"
                ));
            }
            return Ok(offset);
        }
        let offset = self.next;
        if offset + width as usize > MAX_INPUT_BITS {
            return unsupported(format!(
                "more than {MAX_INPUT_BITS} input bits (variable {name})"
            ));
        }
        self.next += width as usize;
        self.offsets.insert(name.to_string(), (offset, width));
        self.vars.push((name.to_string(), width));
        Ok(offset)
    }

    /// Variable bit `index` belongs to, and its position inside it.
    fn owner(&self, index: usize) -> Option<(&str, u32)> {
        self.vars.iter().find_map(|(name, width)| {
            let (offset, _) = self.offsets[name];
            (index >= offset && index < offset + *width as usize)
                .then(|| (name.as_str(), (index - offset) as u32))
        })
    }
}

/// The symbolic evaluator: one per decision, so both sides share the input
/// numbering.
struct Gf2<'a> {
    inputs: Inputs,
    memo: HashMap<*const SmtExpr, Rc<[Affine]>>,
    _terms: std::marker::PhantomData<&'a SmtExpr>,
}

fn constant_amount(bits: &[Affine]) -> Option<u128> {
    let mut value = 0u128;
    for (i, bit) in bits.iter().enumerate() {
        match bit.as_constant()? {
            true if i >= 128 => return None,
            true => value |= 1u128 << i,
            false => {}
        }
    }
    Some(value)
}

impl<'a> Gf2<'a> {
    fn new() -> Self {
        Self {
            inputs: Inputs::default(),
            memo: HashMap::new(),
            _terms: std::marker::PhantomData,
        }
    }

    /// The affine forms of a bit-vector term, least-significant bit first.
    fn bits(&mut self, expr: &'a SmtExpr) -> Result<Rc<[Affine]>, Gf2Error> {
        let key = expr as *const SmtExpr;
        if let Some(done) = self.memo.get(&key) {
            return Ok(Rc::clone(done));
        }
        let bits: Vec<Affine> = match expr {
            SmtExpr::Var { name, width } => {
                if *width > MAX_WIDTH {
                    return unsupported(format!("variable {name} of {width} bits"));
                }
                let offset = self.inputs.bits_of(name, *width)?;
                (0..*width as usize)
                    .map(|i| Affine::input(offset + i))
                    .collect()
            }
            SmtExpr::BvConst { value, width } => {
                if *width > MAX_WIDTH {
                    return unsupported(format!("constant of {width} bits"));
                }
                (0..*width)
                    .map(|i| Affine::constant(i < 64 && (value >> i) & 1 == 1))
                    .collect()
            }
            SmtExpr::Extract {
                high, low, operand, ..
            } => {
                let inner = self.bits(operand)?;
                if *high as usize >= inner.len() || low > high {
                    return unsupported("extract outside its operand");
                }
                inner[*low as usize..=*high as usize].to_vec()
            }
            SmtExpr::Concat { hi, lo, width } => {
                if *width > MAX_WIDTH {
                    return unsupported(format!("concatenation of {width} bits"));
                }
                let lo = self.bits(lo)?;
                let hi = self.bits(hi)?;
                lo.iter().chain(hi.iter()).copied().collect()
            }
            SmtExpr::ZeroExtend { operand, width, .. } => {
                if *width > MAX_WIDTH {
                    return unsupported(format!("zero extension to {width} bits"));
                }
                let inner = self.bits(operand)?;
                let mut out = inner.to_vec();
                out.resize(*width as usize, Affine::ZERO);
                out
            }
            SmtExpr::BvXor { lhs, rhs, .. } => {
                let (a, b) = (self.bits(lhs)?, self.bits(rhs)?);
                if a.len() != b.len() {
                    return unsupported("bvxor of different widths");
                }
                a.iter().zip(b.iter()).map(|(x, y)| x.xor(*y)).collect()
            }
            SmtExpr::BvAnd { lhs, rhs, .. } | SmtExpr::BvOr { lhs, rhs, .. } => {
                let is_and = matches!(expr, SmtExpr::BvAnd { .. });
                let (a, b) = (self.bits(lhs)?, self.bits(rhs)?);
                if a.len() != b.len() {
                    return unsupported("bitwise operation of different widths");
                }
                let mut out = Vec::with_capacity(a.len());
                for (x, y) in a.iter().zip(b.iter()) {
                    let bit = match (x.as_constant(), y.as_constant(), is_and) {
                        (Some(false), _, true) | (_, Some(false), true) => Affine::ZERO,
                        (Some(true), _, false) | (_, Some(true), false) => Affine::constant(true),
                        (Some(_), _, _) => *y,
                        (_, Some(_), _) => *x,
                        (None, None, _) => {
                            return unsupported(
                                "bvand/bvor of two input-dependent bits is not affine",
                            );
                        }
                    };
                    out.push(bit);
                }
                out
            }
            SmtExpr::BvShl { lhs, rhs, .. } | SmtExpr::BvLshr { lhs, rhs, .. } => {
                let left = matches!(expr, SmtExpr::BvShl { .. });
                let value = self.bits(lhs)?;
                let amount = self.bits(rhs)?;
                let Some(amount) = constant_amount(&amount) else {
                    return unsupported("shift by an input-dependent amount");
                };
                let width = value.len();
                (0..width)
                    .map(|i| {
                        let source = if left {
                            (i as u128).checked_sub(amount)
                        } else {
                            Some(i as u128 + amount).filter(|s| *s < width as u128)
                        };
                        source.map_or(Affine::ZERO, |s| value[s as usize])
                    })
                    .collect()
            }
            SmtExpr::Ite {
                cond,
                then_expr,
                else_expr,
            } => {
                let condition = self.boolean(cond)?;
                let (t, e) = (self.bits(then_expr)?, self.bits(else_expr)?);
                if t.len() != e.len() {
                    return unsupported("ite arms of different widths");
                }
                select(condition, &t, &e)?
            }
            other => {
                return unsupported(format!(
                    "bit-vector node outside the affine fragment: {}",
                    node_kind(other)
                ));
            }
        };
        let bits: Rc<[Affine]> = bits.into();
        self.memo.insert(key, Rc::clone(&bits));
        Ok(bits)
    }

    /// The affine form of a Boolean term.
    fn boolean(&mut self, expr: &'a SmtExpr) -> Result<Affine, Gf2Error> {
        let key = expr as *const SmtExpr;
        if let Some(done) = self.memo.get(&key) {
            return Ok(done[0]);
        }
        let bit = match expr {
            SmtExpr::BoolConst(value) => Affine::constant(*value),
            SmtExpr::Not { operand } => self.boolean(operand)?.flip(),
            SmtExpr::Eq { lhs, rhs } => {
                if is_boolean(lhs) {
                    self.boolean(lhs)?.xor(self.boolean(rhs)?).flip()
                } else {
                    let (a, b) = (self.bits(lhs)?, self.bits(rhs)?);
                    if a.len() != b.len() {
                        return unsupported("= of different widths");
                    }
                    let mut open: Option<Affine> = None;
                    let mut equal = Affine::constant(true);
                    for (x, y) in a.iter().zip(b.iter()) {
                        let diff = x.xor(*y);
                        match diff.as_constant() {
                            Some(false) => {}
                            Some(true) => {
                                equal = Affine::constant(false);
                                open = None;
                                break;
                            }
                            None if open.is_none() => open = Some(diff),
                            None => {
                                return unsupported(
                                    "= whose difference has two input-dependent bits",
                                );
                            }
                        }
                    }
                    // Equal iff the one open difference bit is zero.
                    open.map_or(equal, Affine::flip)
                }
            }
            SmtExpr::Ite {
                cond,
                then_expr,
                else_expr,
            } => {
                let condition = self.boolean(cond)?;
                let t = self.boolean(then_expr)?;
                let e = self.boolean(else_expr)?;
                select(condition, &[t], &[e])?[0]
            }
            other => {
                return unsupported(format!(
                    "Boolean node outside the affine fragment: {}",
                    node_kind(other)
                ));
            }
        };
        self.memo.insert(key, Rc::from(vec![bit]));
        Ok(bit)
    }
}

/// `ite(c, t, e)` bitwise: `e XOR (c AND (t XOR e))`, affine when `t XOR e`
/// is constant at the bit or `c` is constant.
fn select(condition: Affine, t: &[Affine], e: &[Affine]) -> Result<Vec<Affine>, Gf2Error> {
    if let Some(c) = condition.as_constant() {
        return Ok(if c { t.to_vec() } else { e.to_vec() });
    }
    t.iter()
        .zip(e)
        .map(|(t, e)| match t.xor(*e).as_constant() {
            Some(false) => Ok(*e),
            Some(true) => Ok(e.xor(condition)),
            None => unsupported("ite whose arms differ by an input-dependent bit"),
        })
        .collect()
}

fn is_boolean(expr: &SmtExpr) -> bool {
    matches!(
        expr,
        SmtExpr::BoolConst(_)
            | SmtExpr::Not { .. }
            | SmtExpr::Eq { .. }
            | SmtExpr::And { .. }
            | SmtExpr::Or { .. }
            | SmtExpr::BvSlt { .. }
            | SmtExpr::BvSle { .. }
            | SmtExpr::BvSgt { .. }
            | SmtExpr::BvSge { .. }
            | SmtExpr::BvUlt { .. }
            | SmtExpr::BvUle { .. }
            | SmtExpr::BvUgt { .. }
            | SmtExpr::BvUge { .. }
    ) || matches!(expr, SmtExpr::Ite { then_expr, .. } if is_boolean(then_expr))
}

/// The operator of a refused node, named WITHOUT formatting its operands: a
/// shared term printed as a tree can be exponentially large.
fn node_kind(expr: &SmtExpr) -> &'static str {
    match expr {
        SmtExpr::BvAdd { .. } => "bvadd",
        SmtExpr::BvSub { .. } => "bvsub",
        SmtExpr::BvMul { .. } => "bvmul",
        SmtExpr::BvSDiv { .. } => "bvsdiv",
        SmtExpr::BvUDiv { .. } => "bvudiv",
        SmtExpr::BvURem { .. } => "bvurem",
        SmtExpr::BvNeg { .. } => "bvneg",
        SmtExpr::BvAshr { .. } => "bvashr",
        SmtExpr::SignExtend { .. } => "sign_extend",
        SmtExpr::BvSlt { .. }
        | SmtExpr::BvSle { .. }
        | SmtExpr::BvSgt { .. }
        | SmtExpr::BvSge { .. }
        | SmtExpr::BvUlt { .. }
        | SmtExpr::BvUle { .. }
        | SmtExpr::BvUgt { .. }
        | SmtExpr::BvUge { .. } => "an ordering",
        SmtExpr::And { .. } => "and",
        SmtExpr::Or { .. } => "or",
        SmtExpr::Select { .. } | SmtExpr::Store { .. } | SmtExpr::ConstArray { .. } => {
            "an array term"
        }
        SmtExpr::BoolConst(_) | SmtExpr::Eq { .. } | SmtExpr::Not { .. } => "a Boolean",
        SmtExpr::Var { .. }
        | SmtExpr::BvConst { .. }
        | SmtExpr::Extract { .. }
        | SmtExpr::Concat { .. }
        | SmtExpr::ZeroExtend { .. }
        | SmtExpr::BvXor { .. }
        | SmtExpr::BvAnd { .. }
        | SmtExpr::BvOr { .. }
        | SmtExpr::BvShl { .. }
        | SmtExpr::BvLshr { .. }
        | SmtExpr::Ite { .. } => "a bit-vector",
        _ => "an unsupported operator",
    }
}

/// The affine forms of a term's bits (least-significant first) and the
/// variables they read, as `(name, width)` in input order.
pub type AffineBits = (Vec<Affine>, Vec<(String, u32)>);

/// The affine forms of a bit-vector term (least-significant bit first) and
/// the variables they read, in input order.
pub fn affine_bits(expr: &SmtExpr) -> Result<AffineBits, Gf2Error> {
    let mut gf2 = Gf2::new();
    let bits = gf2.bits(expr)?;
    Ok((bits.to_vec(), gf2.inputs.vars))
}

/// Decide `lhs == rhs` for every assignment of their variables.
pub fn decide_equal(lhs: &SmtExpr, rhs: &SmtExpr) -> Result<Gf2Exact, Gf2Error> {
    let mut gf2 = Gf2::new();
    let a = gf2.bits(lhs)?;
    let b = gf2.bits(rhs)?;
    if a.len() != b.len() {
        return unsupported(format!("sides of {} and {} bits", a.len(), b.len()));
    }
    let Some(diff) = a
        .iter()
        .zip(b.iter())
        .map(|(x, y)| x.xor(*y))
        .find(|diff| diff.as_constant() != Some(false))
    else {
        return Ok(Gf2Exact::Holds);
    };
    // The all-zero assignment, with one input bit set when the constant term
    // alone does not already make the difference one.
    let mut values: HashMap<String, u128> = gf2
        .inputs
        .vars
        .iter()
        .map(|(name, _)| (name.clone(), 0u128))
        .collect();
    if !diff.constant {
        let index = diff.inputs()[0];
        let (name, bit) = gf2
            .inputs
            .owner(index)
            .ok_or_else(|| Gf2Error::Disagreement(format!("input bit {index} has no owner")))?;
        *values.get_mut(name).expect("every owner is a variable") |= 1u128 << bit;
    }
    let left = eval_concrete(lhs, &values)?;
    let right = eval_concrete(rhs, &values)?;
    if left == right {
        return Err(Gf2Error::Disagreement(format!(
            "the symbolic witness {values:?} does not separate the sides ({left:?})"
        )));
    }
    let mut witness: Vec<(String, u128)> = gf2
        .inputs
        .vars
        .iter()
        .map(|(name, _)| (name.clone(), values[name]))
        .collect();
    witness.sort();
    Ok(Gf2Exact::Refuted(witness))
}

/// A concrete value of [`eval_concrete`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Concrete {
    /// A bit-vector value and its width.
    Bv(u128, u32),
    /// A Boolean.
    Bool(bool),
}

impl Concrete {
    /// The bit-vector value, if this is one.
    pub fn bv(self) -> Option<u128> {
        match self {
            Self::Bv(value, _) => Some(value),
            Self::Bool(_) => None,
        }
    }
}

fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// Evaluate a term of the affine fragment (and the general bitwise and shift
/// operators) on concrete variable values, memoized on node addresses: the
/// independent second evaluation every refutation is confirmed by, and the
/// model a native differential compares with silicon. A missing variable is
/// an error, never a default.
pub fn eval_concrete(expr: &SmtExpr, values: &HashMap<String, u128>) -> Result<Concrete, Gf2Error> {
    let mut memo: HashMap<*const SmtExpr, Concrete> = HashMap::new();
    eval_memo(expr, values, &mut memo)
}

fn eval_memo(
    expr: &SmtExpr,
    values: &HashMap<String, u128>,
    memo: &mut HashMap<*const SmtExpr, Concrete>,
) -> Result<Concrete, Gf2Error> {
    let key = expr as *const SmtExpr;
    if let Some(done) = memo.get(&key) {
        return Ok(*done);
    }
    let bv = |e: &SmtExpr, memo: &mut HashMap<*const SmtExpr, Concrete>| match eval_memo(
        e, values, memo,
    )? {
        Concrete::Bv(value, width) => Ok((value, width)),
        Concrete::Bool(_) => unsupported("a Boolean where a bit-vector is required"),
    };
    let result = match expr {
        SmtExpr::Var { name, width } => {
            let value = values
                .get(name)
                .ok_or_else(|| Gf2Error::Unsupported(format!("no value for variable {name}")))?;
            if *width > MAX_WIDTH || value & !mask(*width) != 0 {
                return unsupported(format!("value of {name} exceeds {width} bits"));
            }
            Concrete::Bv(*value, *width)
        }
        SmtExpr::BvConst { value, width } => {
            Concrete::Bv(u128::from(*value) & mask(*width), *width)
        }
        SmtExpr::BoolConst(value) => Concrete::Bool(*value),
        SmtExpr::Extract {
            high, low, operand, ..
        } => {
            let (value, width) = bv(operand, memo)?;
            if *high >= width || low > high {
                return unsupported("extract outside its operand");
            }
            Concrete::Bv((value >> low) & mask(high - low + 1), high - low + 1)
        }
        SmtExpr::Concat { hi, lo, width } => {
            if *width > MAX_WIDTH {
                return unsupported(format!("concatenation of {width} bits"));
            }
            let (h, _) = bv(hi, memo)?;
            let (l, lw) = bv(lo, memo)?;
            Concrete::Bv((h << lw) | l, *width)
        }
        SmtExpr::ZeroExtend { operand, width, .. } => {
            if *width > MAX_WIDTH {
                return unsupported(format!("zero extension to {width} bits"));
            }
            let (value, _) = bv(operand, memo)?;
            Concrete::Bv(value, *width)
        }
        SmtExpr::BvXor { lhs, rhs, width }
        | SmtExpr::BvAnd { lhs, rhs, width }
        | SmtExpr::BvOr { lhs, rhs, width } => {
            let (a, _) = bv(lhs, memo)?;
            let (b, _) = bv(rhs, memo)?;
            let value = match expr {
                SmtExpr::BvXor { .. } => a ^ b,
                SmtExpr::BvAnd { .. } => a & b,
                _ => a | b,
            };
            Concrete::Bv(value & mask(*width), *width)
        }
        SmtExpr::BvShl { lhs, rhs, width } | SmtExpr::BvLshr { lhs, rhs, width } => {
            let (a, _) = bv(lhs, memo)?;
            let (b, _) = bv(rhs, memo)?;
            let value = if b >= u128::from(*width) {
                0
            } else if matches!(expr, SmtExpr::BvShl { .. }) {
                (a << b) & mask(*width)
            } else {
                a >> b
            };
            Concrete::Bv(value, *width)
        }
        SmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            let Concrete::Bool(c) = eval_memo(cond, values, memo)? else {
                return unsupported("ite condition is not Boolean");
            };
            eval_memo(if c { then_expr } else { else_expr }, values, memo)?
        }
        SmtExpr::Eq { lhs, rhs } => {
            let a = eval_memo(lhs, values, memo)?;
            let b = eval_memo(rhs, values, memo)?;
            Concrete::Bool(a == b)
        }
        SmtExpr::Not { operand } => match eval_memo(operand, values, memo)? {
            Concrete::Bool(b) => Concrete::Bool(!b),
            Concrete::Bv(..) => return unsupported("not of a bit-vector"),
        },
        other => {
            return unsupported(format!(
                "node outside the concrete evaluator: {}",
                node_kind(other)
            ));
        }
    };
    memo.insert(key, result);
    Ok(result)
}

#[cfg(test)]
#[path = "gf2_affine_decide_tests.rs"]
mod tests;
