// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 19 (ruling OD-195): the full canonical spelling of an x86-64 body
//! theorem, applied after slice 18's spelling of every value-numbered
//! single-query theorem, every one-path theorem `(= S M)` and every part.
//!
//! The spelling rewrites a theorem's definitions (`name := rhs`, in
//! definition order, each `rhs` over free inputs and earlier names) and its
//! claims (a right-nested conjunction of items, each an equation, a Boolean
//! literal or a guarded `(or (not G) X)`), never what they state. Each step
//! is one of three kinds, every one exact on every input that satisfies the
//! definitions (OD-182's meta-argument):
//!
//! 1. a local identity `t = t'` that holds on EVERY input (no side
//!    condition), applied bottom-up ([`Terms::rule`], to a fixpoint of at most
//!    [`MAX_NORMAL_ROUNDS`] rounds, [`Terms::normalized`]);
//! 2. a defined name replaced by its definition, or a subterm by the name
//!    defined as exactly that subterm (`cse`, `look`, `peel`, value
//!    numbering, inlining); and
//! 3. a claim that is an identity, or `true`, dropped.
//!
//! The rule groups ([`Groups`]) are slice 18's "v18" normalizer (the design
//! measurement's `smtq.py`, of which OD-188 took only the folds and the
//! `bvsub`-zero identity) and the ten groups of the slice-19 measurement
//! (`smtq19.py`: `mullo`, `addlo`, `shr`, `cmp`, `ovf2`, `sovf`, `mulpow2`,
//! `cse`, `look`, `itepull`), with `peel`. The pipeline ([`Terms::pipeline`])
//! is the measurement's `v19_pipeline`: bit moves substituted, value
//! numbering with `cse` and `look`, the claims normalized with their
//! skeleton kept, single uses inlined and identities dropped to a fixpoint,
//! the whole round repeated until nothing changes (at most
//! [`MAX_PIPELINE_ROUNDS`]). One measured departure: a name defined as bits
//! of a term wider than 64 bits that holds no product is never inlined
//! ([`Terms::wide_bits`]).
//!
//! Slice 22 (ruling OD-203) adds three identity groups of the same kind
//! ([`Terms::rule_v22`], tried between the "v18" and the slice-19 groups): a
//! 128-bit product of operands that are not both 64-bit extensions is the
//! sum of its 64-bit limbs' products (`limb`), the high bits of a sum whose
//! other addend has zero low bits are the sum of the high bits (`addhi0`),
//! and a 64-bit sum with a product leaf has its addends in one structural
//! order (`acmul`); a guarded claim whose guard's double negation was folded
//! keeps its skeleton (`guard`). Ruling OD-204 adds a normal form of bit
//! moves (`catnf`).
//!
//! The terms live in a hash-consed table ([`Terms`]): one id per distinct
//! term, so "the same term" is id equality, as `SmtExpr`'s structural
//! equality. A term outside the body theorem's vocabulary (an array, a
//! floating-point term, a trap, an uninterpreted function) declines the whole
//! spelling ([`Normal::Declined`]); so does a constant no 64-bit constant
//! field holds, which the rules never create (a rule that would is not
//! applied).

use super::*;
use std::sync::Arc;

/// A term of the table.
pub(super) type Id = u32;

/// The most bottom-up rounds [`Terms::normalized`] rewrites a term.
const MAX_NORMAL_ROUNDS: usize = 16;

/// The most rounds [`Terms::pipeline`] repeats the whole spelling.
const MAX_PIPELINE_ROUNDS: usize = 4;

/// The most rounds one pipeline round inlines and drops identities.
const MAX_CLAIM_ROUNDS: usize = 64;

/// The most nodes a definition the pipeline substitutes as a bit move may
/// have (slice 17's bound, [`super::split::moves_bits`]).
const MAX_BIT_MOVE_NODES: usize = 16;

/// The most names [`Terms::resolved`] looks through in a row (OD-196).
const MAX_LOOK_THROUGH: usize = 8;

/// The rule groups the spelling applies; production applies
/// [`Groups::CANONICAL`]. Each group can be left out, so a test can show what
/// each one moves.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Groups(u32);

impl Groups {
    /// No group: the spelling is not applied ([`Normal::Declined`]).
    pub(crate) const NONE: Self = Self(0);
    /// Extension and extract identities beyond OD-183's: an extract of a
    /// sign extension inside it, an extract above a zero extension is zero,
    /// the low bits of an extension, an extract inside a concatenation, an
    /// extension by zero, nested extensions, a zero high half of a
    /// concatenation.
    pub(crate) const EXT: Self = Self(1);
    /// Constant folding (OD-188's, [`super::split::fold_constant`]), and an
    /// equation of two distinct constants is `false`.
    pub(crate) const FOLD: Self = Self(1 << 1);
    /// Boolean constants: `(= t t)`, `(= x true)`, `(= x false)`, `not`, `and`,
    /// `or` and `ite` of constants or of one term twice.
    pub(crate) const BOOL: Self = Self(1 << 2);
    /// The one-bit encoding of a Boolean: `(= (ite c #b1 #b0) #b1)` is `c`.
    pub(crate) const BIT1: Self = Self(1 << 3);
    /// The widening product's overflow test: `(= (zext (P[n-1:0])) P)` is
    /// `(= P[W-1:n] 0)`.
    pub(crate) const OVF: Self = Self(1 << 4);
    /// `(= (bvsub x y) 0)` is `(= x y)` (OD-188's).
    pub(crate) const SUBZ: Self = Self(1 << 5);
    /// Unit and zero laws of `bvadd`, `bvor`, `bvxor`, `bvsub`, `bvand`,
    /// `bvmul` and the shifts.
    pub(crate) const ARITH: Self = Self(1 << 6);
    /// The low bits of a product are the product of the operands' low bits.
    pub(crate) const MULLO: Self = Self(1 << 7);
    /// The same for `bvadd`, `bvsub`, `bvand`, `bvor`, `bvxor` and `bvneg`.
    pub(crate) const ADDLO: Self = Self(1 << 8);
    /// A shift by a constant is an extract and an extension or concatenation.
    pub(crate) const SHR: Self = Self(1 << 9);
    /// One comparison operator per direction (`bvult`, `bvslt`).
    pub(crate) const CMP: Self = Self(1 << 10);
    /// An overflow test of a zero-extended product is a test of its high bits.
    pub(crate) const OVF2: Self = Self(1 << 11);
    /// The same for a sign-extended product (high bits all equal).
    pub(crate) const SOVF: Self = Self(1 << 12);
    /// A product by `2^k` is a shift (an extract and a concatenation).
    pub(crate) const MULPOW2: Self = Self(1 << 13);
    /// A subterm equal to an earlier kept definition's right-hand side is
    /// that definition's name.
    pub(crate) const CSE: Self = Self(1 << 14);
    /// An extract of a kept name is looked through to its definition when
    /// that gives a variable, a constant or a kept name.
    pub(crate) const LOOK: Self = Self(1 << 15);
    /// An `ite` of two equal extensions or extracts is the extension of the
    /// `ite`.
    pub(crate) const ITEPULL: Self = Self(1 << 16);
    /// The low bits of a kept name defined as an extension of `t` are `t`.
    pub(crate) const PEEL: Self = Self(1 << 17);
    /// Every identity group of OD-195.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) const IDENTITIES: Self = Self((1 << 18) - 1);
    /// OD-196: a constant-divisor multiply-high is the quotient it computes,
    /// when the Granlund-Montgomery condition holds for its constants
    /// ([`magic_divisor`]).
    pub(crate) const MAGIC: Self = Self(1 << 18);
    /// OD-196: the low bits of a quotient by a constant that fits them are
    /// the quotient.
    pub(crate) const RANGE: Self = Self(1 << 19);
    /// OD-196: a remainder by a non-zero constant is SMT-LIB's definition of
    /// it.
    pub(crate) const UREMDEF: Self = Self(1 << 20);
    /// OD-203: a 128-bit product of two operands that are not both 64-bit
    /// extensions is the sum of its 64-bit limbs' products
    /// ([`Terms::limb_product`]).
    pub(crate) const LIMB: Self = Self(1 << 21);
    /// OD-203: the high bits of a sum whose other addend has zero low bits
    /// are the sum of the high bits ([`Terms::add_high_zero`]).
    pub(crate) const ADDHI0: Self = Self(1 << 22);
    /// OD-203: a 64-bit sum with a product leaf has its addends in one
    /// structural order, nested right ([`Terms::sorted_sum`]).
    pub(crate) const ACMUL: Self = Self(1 << 23);
    /// OD-203: a guarded claim whose guard's double negation a whole-claims
    /// normalization folded keeps its guard ([`Terms::folded_guard`]).
    pub(crate) const GUARD: Self = Self(1 << 24);
    /// Slice 22's groups (OD-203).
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) const PRODUCT_LIMBS: Self = Self((1 << 21) | (1 << 22) | (1 << 23) | (1 << 24));
    /// OD-204: a normal form of bit moves ([`Terms::bit_move_normal`]).
    pub(crate) const CATNF: Self = Self(1 << 25);
    /// The groups production applies.
    pub(crate) const CANONICAL: Self = Self((1 << 26) - 1);

    /// `self` with the groups of `other`.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) const fn with(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    /// Whether every group of `other` is in `self`.
    pub(crate) const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    /// `self` without the groups of `other`.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) const fn without(self, other: Self) -> Self {
        Self(self.0 & !other.0)
    }
}

/// An operator of the table: the body theorem's vocabulary.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Op {
    Var(String, u32),
    Const(u64, u32),
    True,
    False,
    BvAdd,
    BvSub,
    BvMul,
    BvUDiv,
    BvURem,
    BvSDiv,
    BvNeg,
    BvAnd,
    BvOr,
    BvXor,
    BvShl,
    BvLshr,
    BvAshr,
    Eq,
    Not,
    And,
    Or,
    Ult,
    Ule,
    Ugt,
    Uge,
    Slt,
    Sle,
    Sgt,
    Sge,
    Ite,
    Extract(u32, u32),
    Concat,
    ZeroExtend(u32),
    SignExtend(u32),
}

/// The outcome of [`spelled`] and [`spelled_pair`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Normal<T> {
    /// No claim is left: every claim holds by the definitions.
    Emptied,
    /// The spelled theorem.
    Spelled(T),
    /// A term outside the spelling's vocabulary: the input is kept.
    Declined,
}

/// `definitions` (in order) and `claims` spelled by the pipeline with
/// `groups` ([`Terms::pipeline`]).
pub(super) fn spelled(
    definitions: &[(String, E)],
    claims: &E,
    groups: Groups,
) -> Normal<(Vec<(String, E)>, E)> {
    if groups == Groups::NONE {
        return Normal::Declined;
    }
    let mut terms = Terms::new(groups);
    let Some((definitions, claims)) = terms.import_theorem(definitions, claims) else {
        return Normal::Declined;
    };
    match terms.pipeline(definitions, claims) {
        None => Normal::Emptied,
        Some((kept, stated)) => match terms.export_theorem(&kept, stated) {
            Some(theorem) => Normal::Spelled(theorem),
            None => Normal::Declined,
        },
    }
}

/// What [`spelled_pair`] returns inside [`Normal`]: the definitions the
/// spelling kept, then the two sides of the claim it left.
pub(super) type SpelledPair = (Vec<(String, E)>, E, E);

/// A one-path theorem `(= source machine)` under `definitions`, spelled as
/// [`spelled`] spells the single claim `(= source machine)`: its sides are
/// the two sides of the claim left, which must be an equation of two
/// bit-vector terms ([`Normal::Declined`] otherwise).
pub(super) fn spelled_pair(
    definitions: &[(String, E)],
    source: &E,
    machine: &E,
    groups: Groups,
) -> Normal<SpelledPair> {
    let claim = source.clone().eq_expr(machine.clone());
    match spelled(definitions, &claim, groups) {
        Normal::Spelled((kept, E::Eq { lhs, rhs })) if lhs.try_bv_width().is_ok() => {
            Normal::Spelled((kept, lhs.as_ref().clone(), rhs.as_ref().clone()))
        }
        Normal::Spelled(_) | Normal::Declined => Normal::Declined,
        Normal::Emptied => Normal::Emptied,
    }
}

/// The hash-consed term table and the spelling's rules over it.
pub(super) struct Terms {
    nodes: Vec<(Op, Vec<Id>)>,
    widths: Vec<u32>,
    intern: HashMap<(Op, Vec<Id>), Id>,
    groups: Groups,
    t: Id,
    f: Id,
    /// OD-196: the kept definitions of the current pipeline round, by name
    /// ([`Terms::resolved`]; filled only with [`Groups::MAGIC`]).
    rhs_of: HashMap<String, Id>,
    /// OD-203: the width of one limb, half the width of the product
    /// [`Groups::LIMB`] spells and the width of the sums [`Groups::ACMUL`]
    /// orders (64; tests take narrower ones to sweep the rules exhaustively).
    limb: u32,
    /// OD-203: each term's structural key ([`Terms::structural_key`]).
    keys: HashMap<Id, u128>,
}

impl Terms {
    pub(super) fn new(groups: Groups) -> Self {
        let mut terms = Self {
            nodes: Vec::new(),
            widths: Vec::new(),
            intern: HashMap::new(),
            groups,
            t: 0,
            f: 0,
            rhs_of: HashMap::new(),
            limb: 64,
            keys: HashMap::new(),
        };
        terms.t = terms.mk(Op::True, Vec::new());
        terms.f = terms.mk(Op::False, Vec::new());
        terms
    }

    fn has(&self, group: Groups) -> bool {
        self.groups.contains(group)
    }

    /// `value` when `group` is applied (`None` otherwise).
    fn g(&self, group: Groups, value: Id) -> Option<Id> {
        self.has(group).then_some(value)
    }

    // -----------------------------------------------------------------------
    // The table
    // -----------------------------------------------------------------------

    fn op(&self, id: Id) -> &Op {
        &self.nodes[id as usize].0
    }

    fn args(&self, id: Id) -> &[Id] {
        &self.nodes[id as usize].1
    }

    fn arg(&self, id: Id, k: usize) -> Id {
        self.nodes[id as usize].1[k]
    }

    /// The width of `id` (0 for a Boolean).
    fn width(&self, id: Id) -> u32 {
        self.widths[id as usize]
    }

    fn infer_width(&self, op: &Op, args: &[Id]) -> u32 {
        match op {
            Op::Var(_, width) | Op::Const(_, width) => *width,
            Op::True
            | Op::False
            | Op::Eq
            | Op::Not
            | Op::And
            | Op::Or
            | Op::Ult
            | Op::Ule
            | Op::Ugt
            | Op::Uge
            | Op::Slt
            | Op::Sle
            | Op::Sgt
            | Op::Sge => 0,
            Op::Extract(high, low) => high - low + 1,
            Op::ZeroExtend(extra) | Op::SignExtend(extra) => extra + self.width(args[0]),
            Op::Concat => self.width(args[0]) + self.width(args[1]),
            Op::Ite => self.width(args[1]),
            _ => self.width(args[0]),
        }
    }

    /// The id of `(op args)`, interned.
    fn mk(&mut self, op: Op, args: Vec<Id>) -> Id {
        let key = (op, args);
        if let Some(&id) = self.intern.get(&key) {
            return id;
        }
        let width = self.infer_width(&key.0, &key.1);
        let id = Id::try_from(self.nodes.len()).expect("a term table below 2^32 nodes");
        self.nodes.push(key.clone());
        self.widths.push(width);
        self.intern.insert(key, id);
        id
    }

    fn var(&mut self, name: &str, width: u32) -> Id {
        self.mk(Op::Var(name.to_owned(), width), Vec::new())
    }

    /// The `width`-bit constant of `value`'s low bits, when a 64-bit
    /// constant field holds it.
    fn cnst(&mut self, value: u128, width: u32) -> Option<Id> {
        let value = if width >= 128 {
            value
        } else {
            value & ((1u128 << width) - 1)
        };
        let value = u64::try_from(value).ok()?;
        Some(self.mk(Op::Const(value, width), Vec::new()))
    }

    fn zero(&mut self, width: u32) -> Id {
        self.cnst(0, width).expect("zero fits")
    }

    fn extract(&mut self, x: Id, high: u32, low: u32) -> Id {
        self.mk(Op::Extract(high, low), vec![x])
    }

    fn not(&mut self, x: Id) -> Id {
        self.mk(Op::Not, vec![x])
    }

    fn eq(&mut self, a: Id, b: Id) -> Id {
        self.mk(Op::Eq, vec![a, b])
    }

    fn constant(&self, id: Id) -> Option<u64> {
        match self.op(id) {
            Op::Const(value, _) => Some(*value),
            _ => None,
        }
    }

    fn is_var(&self, id: Id) -> bool {
        matches!(self.op(id), Op::Var(..))
    }

    fn var_name(&self, id: Id) -> Option<&str> {
        match self.op(id) {
            Op::Var(name, _) => Some(name),
            _ => None,
        }
    }

    // -----------------------------------------------------------------------
    // Import and export
    // -----------------------------------------------------------------------

    /// `expr` in the table; `None` for a term outside the vocabulary.
    fn import(&mut self, root: &E) -> Option<Id> {
        let mut memo: HashMap<*const E, Id> = HashMap::new();
        let mut stack: Vec<(&E, bool)> = vec![(root, false)];
        while let Some((node, ready)) = stack.pop() {
            let key = node as *const E;
            if memo.contains_key(&key) {
                continue;
            }
            if !ready {
                stack.push((node, true));
                let mut children: Vec<&E> = Vec::new();
                node.for_each_child(&mut |child| children.push(child));
                for child in children.into_iter().rev() {
                    if !memo.contains_key(&(child as *const E)) {
                        stack.push((child, false));
                    }
                }
                continue;
            }
            let mut args: Vec<Id> = Vec::new();
            node.for_each_child(&mut |child| args.push(memo[&(child as *const E)]));
            let (op, arity) = match node {
                E::Var { name, width } => (Op::Var(name.clone(), *width), 0),
                E::BvConst { value, width } => (Op::Const(*value, *width), 0),
                E::BoolConst(true) => (Op::True, 0),
                E::BoolConst(false) => (Op::False, 0),
                E::BvAdd { .. } => (Op::BvAdd, 2),
                E::BvSub { .. } => (Op::BvSub, 2),
                E::BvMul { .. } => (Op::BvMul, 2),
                E::BvUDiv { .. } => (Op::BvUDiv, 2),
                E::BvURem { .. } => (Op::BvURem, 2),
                E::BvSDiv { .. } => (Op::BvSDiv, 2),
                E::BvNeg { .. } => (Op::BvNeg, 1),
                E::BvAnd { .. } => (Op::BvAnd, 2),
                E::BvOr { .. } => (Op::BvOr, 2),
                E::BvXor { .. } => (Op::BvXor, 2),
                E::BvShl { .. } => (Op::BvShl, 2),
                E::BvLshr { .. } => (Op::BvLshr, 2),
                E::BvAshr { .. } => (Op::BvAshr, 2),
                E::Eq { .. } => (Op::Eq, 2),
                E::Not { .. } => (Op::Not, 1),
                E::And { .. } => (Op::And, 2),
                E::Or { .. } => (Op::Or, 2),
                E::BvUlt { .. } => (Op::Ult, 2),
                E::BvUle { .. } => (Op::Ule, 2),
                E::BvUgt { .. } => (Op::Ugt, 2),
                E::BvUge { .. } => (Op::Uge, 2),
                E::BvSlt { .. } => (Op::Slt, 2),
                E::BvSle { .. } => (Op::Sle, 2),
                E::BvSgt { .. } => (Op::Sgt, 2),
                E::BvSge { .. } => (Op::Sge, 2),
                E::Ite { .. } => (Op::Ite, 3),
                E::Extract { high, low, .. } if high >= low => (Op::Extract(*high, *low), 1),
                E::Concat { .. } => (Op::Concat, 2),
                E::ZeroExtend { extra_bits, .. } => (Op::ZeroExtend(*extra_bits), 1),
                E::SignExtend { extra_bits, .. } => (Op::SignExtend(*extra_bits), 1),
                _ => return None,
            };
            if args.len() != arity {
                return None;
            }
            let id = self.mk(op, args);
            // The table's width is the term's own (a Boolean has none).
            match node.try_bv_width() {
                Ok(width) if width == self.width(id) && width > 0 => {}
                Err(_) if self.width(id) == 0 => {}
                _ => return None,
            }
            memo.insert(key, id);
        }
        memo.get(&(root as *const E)).copied()
    }

    fn import_theorem(
        &mut self,
        definitions: &[(String, E)],
        claims: &E,
    ) -> Option<(Vec<(String, Id)>, Id)> {
        let mut imported = Vec::with_capacity(definitions.len());
        for (name, expr) in definitions {
            imported.push((name.clone(), self.import(expr)?));
        }
        Some((imported, self.import(claims)?))
    }

    /// Every distinct term under `roots`, children first.
    fn topo(&self, roots: &[Id]) -> Vec<Id> {
        let mut seen: HashSet<Id> = HashSet::new();
        let mut order = Vec::new();
        let mut stack: Vec<(Id, bool)> = roots.iter().rev().map(|&root| (root, false)).collect();
        while let Some((id, ready)) = stack.pop() {
            if ready {
                order.push(id);
                continue;
            }
            if !seen.insert(id) {
                continue;
            }
            stack.push((id, true));
            for &child in self.args(id).iter().rev() {
                if !seen.contains(&child) {
                    stack.push((child, false));
                }
            }
        }
        order
    }

    /// `root` as an `SmtExpr`, sharing each repeated term; `None` when it
    /// holds a constant no constant field holds (never: [`Self::cnst`]).
    fn export(&self, root: Id) -> Option<E> {
        let mut out: HashMap<Id, Arc<E>> = HashMap::new();
        for id in self.topo(&[root]) {
            let arg = |k: usize| Arc::clone(&out[&self.args(id)[k]]);
            let width = self.width(id);
            let binary = |k: fn(Arc<E>, Arc<E>, u32) -> E| k(arg(0), arg(1), width);
            let relation =
                |k: fn(Arc<E>, Arc<E>, u32) -> E| k(arg(0), arg(1), self.width(self.args(id)[0]));
            let expr = match self.op(id) {
                Op::Var(name, width) => E::Var {
                    name: name.clone(),
                    width: *width,
                },
                Op::Const(value, width) => E::BvConst {
                    value: *value,
                    width: *width,
                },
                Op::True => E::BoolConst(true),
                Op::False => E::BoolConst(false),
                Op::BvAdd => binary(|lhs, rhs, width| E::BvAdd { lhs, rhs, width }),
                Op::BvSub => binary(|lhs, rhs, width| E::BvSub { lhs, rhs, width }),
                Op::BvMul => binary(|lhs, rhs, width| E::BvMul { lhs, rhs, width }),
                Op::BvUDiv => binary(|lhs, rhs, width| E::BvUDiv { lhs, rhs, width }),
                Op::BvURem => binary(|lhs, rhs, width| E::BvURem { lhs, rhs, width }),
                Op::BvSDiv => binary(|lhs, rhs, width| E::BvSDiv { lhs, rhs, width }),
                Op::BvAnd => binary(|lhs, rhs, width| E::BvAnd { lhs, rhs, width }),
                Op::BvOr => binary(|lhs, rhs, width| E::BvOr { lhs, rhs, width }),
                Op::BvXor => binary(|lhs, rhs, width| E::BvXor { lhs, rhs, width }),
                Op::BvShl => binary(|lhs, rhs, width| E::BvShl { lhs, rhs, width }),
                Op::BvLshr => binary(|lhs, rhs, width| E::BvLshr { lhs, rhs, width }),
                Op::BvAshr => binary(|lhs, rhs, width| E::BvAshr { lhs, rhs, width }),
                Op::BvNeg => E::BvNeg {
                    operand: arg(0),
                    width,
                },
                Op::Eq => E::Eq {
                    lhs: arg(0),
                    rhs: arg(1),
                },
                Op::Not => E::Not { operand: arg(0) },
                Op::And => E::And {
                    lhs: arg(0),
                    rhs: arg(1),
                },
                Op::Or => E::Or {
                    lhs: arg(0),
                    rhs: arg(1),
                },
                Op::Ult => relation(|lhs, rhs, width| E::BvUlt { lhs, rhs, width }),
                Op::Ule => relation(|lhs, rhs, width| E::BvUle { lhs, rhs, width }),
                Op::Ugt => relation(|lhs, rhs, width| E::BvUgt { lhs, rhs, width }),
                Op::Uge => relation(|lhs, rhs, width| E::BvUge { lhs, rhs, width }),
                Op::Slt => relation(|lhs, rhs, width| E::BvSlt { lhs, rhs, width }),
                Op::Sle => relation(|lhs, rhs, width| E::BvSle { lhs, rhs, width }),
                Op::Sgt => relation(|lhs, rhs, width| E::BvSgt { lhs, rhs, width }),
                Op::Sge => relation(|lhs, rhs, width| E::BvSge { lhs, rhs, width }),
                Op::Ite => E::Ite {
                    cond: arg(0),
                    then_expr: arg(1),
                    else_expr: arg(2),
                },
                Op::Extract(high, low) => E::Extract {
                    high: *high,
                    low: *low,
                    operand: arg(0),
                    width,
                },
                Op::Concat => E::Concat {
                    hi: arg(0),
                    lo: arg(1),
                    width,
                },
                Op::ZeroExtend(extra) => E::ZeroExtend {
                    operand: arg(0),
                    extra_bits: *extra,
                    width,
                },
                Op::SignExtend(extra) => E::SignExtend {
                    operand: arg(0),
                    extra_bits: *extra,
                    width,
                },
            };
            out.insert(id, Arc::new(expr));
        }
        let root = out.remove(&root)?;
        Some(Arc::try_unwrap(root).unwrap_or_else(|shared| (*shared).clone()))
    }

    fn export_theorem(&self, kept: &[(String, Id)], claims: Id) -> Option<(Vec<(String, E)>, E)> {
        let mut definitions = Vec::with_capacity(kept.len());
        for (name, id) in kept {
            definitions.push((name.clone(), self.export(*id)?));
        }
        Some((definitions, self.export(claims)?))
    }

    // -----------------------------------------------------------------------
    // Rewriting
    // -----------------------------------------------------------------------

    /// `root` rewritten bottom-up: each distinct term once, its operands
    /// already rewritten, replaced by `visit`'s term when it gives one (a
    /// replacement is not visited again).
    fn rewrite(&mut self, root: Id, visit: &mut dyn FnMut(&mut Self, Id) -> Option<Id>) -> Id {
        let order = self.topo(&[root]);
        let mut memo: HashMap<Id, Id> = HashMap::with_capacity(order.len());
        for id in order {
            let (op, args) = self.nodes[id as usize].clone();
            let mapped: Vec<Id> = args.iter().map(|arg| memo[arg]).collect();
            let node = if mapped == args {
                id
            } else {
                self.mk(op, mapped)
            };
            let replaced = visit(self, node).unwrap_or(node);
            memo.insert(id, replaced);
        }
        memo[&root]
    }

    /// `root` with every name `env` defines replaced by its term.
    fn substitute(&mut self, root: Id, env: &HashMap<String, Id>) -> Id {
        if env.is_empty() {
            return root;
        }
        self.rewrite(root, &mut |terms, node| {
            terms.var_name(node).and_then(|name| env.get(name).copied())
        })
    }

    /// `root` with [`Self::rule`] applied bottom-up to a fixpoint (at most
    /// [`MAX_NORMAL_ROUNDS`] rounds).
    fn normalized(&mut self, root: Id) -> Id {
        let mut current = root;
        for _ in 0..MAX_NORMAL_ROUNDS {
            let mut changed = false;
            let next = self.rewrite(current, &mut |terms, node| match terms.rule(node) {
                Some(rewritten) if rewritten != node => {
                    changed = true;
                    Some(rewritten)
                }
                _ => None,
            });
            if !changed {
                return next;
            }
            current = next;
        }
        current
    }

    // -----------------------------------------------------------------------
    // The rules
    // -----------------------------------------------------------------------

    /// One rewrite of `node` (its operands already rewritten): slice 18's
    /// "v18" identities ([`Self::rule_v18`]), else slice 22's product limbs
    /// ([`Self::rule_v22`]), else the slice-19 groups ([`Self::rule_v19`]).
    /// Each holds on every input.
    fn rule(&mut self, node: Id) -> Option<Id> {
        self.rule_v18(node)
            .or_else(|| self.rule_v22(node))
            .or_else(|| self.rule_v19(node))
    }

    /// `node` folded when every operand is a constant ([`Groups::FOLD`]:
    /// OD-188's [`super::split::fold_constant`], one SMT-LIB definition per
    /// operator; never an `ite` or a Boolean connective; `None` for a value
    /// no constant field holds).
    fn fold(&mut self, node: Id) -> Option<Id> {
        if !self.has(Groups::FOLD) {
            return None;
        }
        let args = self.args(node).to_vec();
        if args.is_empty()
            || !args
                .iter()
                .all(|&arg| self.constant(arg).is_some() || arg == self.t || arg == self.f)
            || matches!(self.op(node), Op::Ite | Op::And | Op::Or | Op::Not)
        {
            return None;
        }
        let expr = self.export(node)?;
        match split::fold_constant(&expr)? {
            E::BvConst { value, width } => self.cnst(u128::from(value), width),
            E::BoolConst(true) => Some(self.t),
            E::BoolConst(false) => Some(self.f),
            _ => None,
        }
    }

    /// Slice 18's "v18" identities (the design measurement's `smtq.py`
    /// `norm_rule`), by group. The extract identities of OD-183 and the
    /// concatenation of adjacent extracts of one term are always applied.
    fn rule_v18(&mut self, node: Id) -> Option<Id> {
        let op = self.op(node).clone();
        let args = self.args(node).to_vec();
        let width = self.width(node);
        match op {
            Op::Extract(high, low) => {
                let x = args[0];
                if low == 0 && high + 1 == self.width(x) {
                    return Some(x);
                }
                match self.op(x).clone() {
                    Op::Const(value, _) => self.cnst(u128::from(value) >> low, high - low + 1),
                    Op::Extract(_, inner_low) => {
                        let inner = self.arg(x, 0);
                        Some(self.extract(inner, high + inner_low, low + inner_low))
                    }
                    kind @ (Op::ZeroExtend(_) | Op::SignExtend(_)) => {
                        let zero = matches!(kind, Op::ZeroExtend(_));
                        let y = self.arg(x, 0);
                        let wy = self.width(y);
                        if high < wy {
                            // Inside the operand: its bits.
                            let bits = self.extract(y, high, low);
                            return if zero {
                                Some(bits)
                            } else {
                                self.g(Groups::EXT, bits)
                            };
                        }
                        if zero && low >= wy {
                            // Above a zero extension: zeros.
                            let zeros = self.zero(high - low + 1);
                            return self.g(Groups::EXT, zeros);
                        }
                        if low == 0 {
                            if zero && high + 1 == wy {
                                return Some(y);
                            }
                            // The low bits of an extension: a narrower one.
                            let narrower = if high + 1 == wy {
                                y
                            } else {
                                let extended = if zero {
                                    Op::ZeroExtend(high + 1 - wy)
                                } else {
                                    Op::SignExtend(high + 1 - wy)
                                };
                                self.mk(extended, vec![y])
                            };
                            return self.g(Groups::EXT, narrower);
                        }
                        None
                    }
                    Op::Concat => {
                        let (hi, lo) = (self.arg(x, 0), self.arg(x, 1));
                        let low_width = self.width(lo);
                        if high < low_width {
                            let bits = self.extract(lo, high, low);
                            return self.g(Groups::EXT, bits);
                        }
                        if low >= low_width {
                            let bits = self.extract(hi, high - low_width, low - low_width);
                            return self.g(Groups::EXT, bits);
                        }
                        None
                    }
                    _ => None,
                }
            }
            Op::ZeroExtend(extra) | Op::SignExtend(extra) => {
                let zero = matches!(op, Op::ZeroExtend(_));
                let x = args[0];
                if extra == 0 {
                    return self.g(Groups::EXT, x);
                }
                match self.op(x).clone() {
                    Op::ZeroExtend(inner) if zero => {
                        let y = self.arg(x, 0);
                        let merged = self.mk(Op::ZeroExtend(extra + inner), vec![y]);
                        self.g(Groups::EXT, merged)
                    }
                    Op::SignExtend(inner) if !zero => {
                        let y = self.arg(x, 0);
                        let merged = self.mk(Op::SignExtend(extra + inner), vec![y]);
                        self.g(Groups::EXT, merged)
                    }
                    // The sign bit of a zero extension (by one bit or more) is 0.
                    Op::ZeroExtend(inner) if !zero && inner >= 1 => {
                        let y = self.arg(x, 0);
                        let merged = self.mk(Op::ZeroExtend(extra + inner), vec![y]);
                        self.g(Groups::EXT, merged)
                    }
                    _ => self.fold(node),
                }
            }
            Op::Concat => {
                let (hi, lo) = (args[0], args[1]);
                if let (Op::Extract(h1, l1), Op::Extract(h2, l2)) =
                    (self.op(hi).clone(), self.op(lo).clone())
                {
                    let a = self.arg(hi, 0);
                    if l1 == h2 + 1 && a == self.arg(lo, 0) {
                        return Some(if l2 == 0 && h1 + 1 == self.width(a) {
                            a
                        } else {
                            self.extract(a, h1, l2)
                        });
                    }
                }
                if self.constant(hi) == Some(0) {
                    let extended = self.mk(Op::ZeroExtend(self.width(hi)), vec![lo]);
                    return self.g(Groups::EXT, extended);
                }
                self.fold(node)
            }
            Op::Eq => {
                let (a, b) = (args[0], args[1]);
                if a == b {
                    return self.g(Groups::BOOL, self.t);
                }
                let constant = |terms: &Self, x: Id| {
                    terms.constant(x).is_some() || x == terms.t || x == terms.f
                };
                if constant(self, a) && constant(self, b) {
                    // Two distinct constants (one id per term).
                    return self.g(Groups::FOLD, self.f);
                }
                for (x, y) in [(a, b), (b, a)] {
                    if self.has(Groups::BIT1)
                        && self.width(y) == 1
                        && let (Some(y_value), Op::Ite) = (self.constant(y), self.op(x))
                    {
                        let (c, t, e) = (self.arg(x, 0), self.arg(x, 1), self.arg(x, 2));
                        if let (Some(t_value), Some(e_value)) = (self.constant(t), self.constant(e))
                            && t_value != e_value
                        {
                            return Some(if y_value == t_value { c } else { self.not(c) });
                        }
                    }
                    if y == self.t && self.has(Groups::BOOL) {
                        return Some(x);
                    }
                    if y == self.f && self.has(Groups::BOOL) {
                        return Some(self.not(x));
                    }
                }
                // The widening product's overflow test.
                for (x, y) in [(a, b), (b, a)] {
                    if self.has(Groups::OVF)
                        && let Op::ZeroExtend(_) = self.op(x)
                    {
                        let inner = self.arg(x, 0);
                        if let Op::Extract(high, 0) = *self.op(inner)
                            && self.arg(inner, 0) == y
                        {
                            let (wide, narrow) = (self.width(y), high + 1);
                            if narrow < wide {
                                let top = self.extract(y, wide - 1, narrow);
                                let zero = self.zero(wide - narrow);
                                return Some(self.eq(top, zero));
                            }
                        }
                    }
                }
                // `(= (bvsub x y) 0)` is `(= x y)`.
                for (x, y) in [(a, b), (b, a)] {
                    if self.has(Groups::SUBZ)
                        && self.constant(y) == Some(0)
                        && let Op::BvSub = self.op(x)
                    {
                        let (p, q) = (self.arg(x, 0), self.arg(x, 1));
                        return Some(if p == q { self.t } else { self.eq(p, q) });
                    }
                }
                None
            }
            Op::Not => {
                let x = args[0];
                if x == self.t {
                    return self.g(Groups::BOOL, self.f);
                }
                if x == self.f {
                    return self.g(Groups::BOOL, self.t);
                }
                if let Op::Not = self.op(x) {
                    let inner = self.arg(x, 0);
                    return self.g(Groups::BOOL, inner);
                }
                None
            }
            Op::And => {
                let (a, b) = (args[0], args[1]);
                if a == self.f || b == self.f {
                    return self.g(Groups::BOOL, self.f);
                }
                if a == self.t {
                    return self.g(Groups::BOOL, b);
                }
                if b == self.t {
                    return self.g(Groups::BOOL, a);
                }
                if a == b {
                    return self.g(Groups::BOOL, a);
                }
                None
            }
            Op::Or => {
                let (a, b) = (args[0], args[1]);
                if a == self.t || b == self.t {
                    return self.g(Groups::BOOL, self.t);
                }
                if a == self.f {
                    return self.g(Groups::BOOL, b);
                }
                if b == self.f {
                    return self.g(Groups::BOOL, a);
                }
                if a == b {
                    return self.g(Groups::BOOL, a);
                }
                None
            }
            Op::Ite => {
                let (c, t, e) = (args[0], args[1], args[2]);
                if c == self.t {
                    return self.g(Groups::BOOL, t);
                }
                if c == self.f {
                    return self.g(Groups::BOOL, e);
                }
                if t == e {
                    return self.g(Groups::BOOL, t);
                }
                if t == self.t && e == self.f {
                    return self.g(Groups::BOOL, c);
                }
                None
            }
            Op::BvAdd | Op::BvOr | Op::BvXor => {
                let (a, b) = (args[0], args[1]);
                if self.constant(a) == Some(0) {
                    return self.g(Groups::ARITH, b);
                }
                if self.constant(b) == Some(0) {
                    return self.g(Groups::ARITH, a);
                }
                if op == Op::BvXor && a == b {
                    let zero = self.zero(width);
                    return self.g(Groups::ARITH, zero);
                }
                if op == Op::BvOr && a == b {
                    return self.g(Groups::ARITH, a);
                }
                self.fold(node)
            }
            Op::BvSub => {
                let (a, b) = (args[0], args[1]);
                if self.constant(b) == Some(0) {
                    return self.g(Groups::ARITH, a);
                }
                if a == b {
                    let zero = self.zero(width);
                    return self.g(Groups::ARITH, zero);
                }
                self.fold(node)
            }
            Op::BvAnd => {
                let (a, b) = (args[0], args[1]);
                if self.has(Groups::ARITH) {
                    for (x, y) in [(a, b), (b, a)] {
                        if let Some(value) = self.constant(y) {
                            if value == 0 {
                                return Some(self.zero(width));
                            }
                            if width <= 64 && u128::from(value) == (1u128 << width) - 1 {
                                return Some(x);
                            }
                        }
                    }
                    if a == b {
                        return Some(a);
                    }
                }
                self.fold(node)
            }
            Op::BvMul => {
                let (a, b) = (args[0], args[1]);
                if self.has(Groups::ARITH) {
                    for (x, y) in [(a, b), (b, a)] {
                        match self.constant(y) {
                            Some(0) => return Some(self.zero(width)),
                            Some(1) => return Some(x),
                            _ => {}
                        }
                    }
                }
                self.fold(node)
            }
            Op::BvShl | Op::BvLshr | Op::BvAshr => {
                if self.constant(args[1]) == Some(0) {
                    return self.g(Groups::ARITH, args[0]);
                }
                self.fold(node)
            }
            _ => self.fold(node),
        }
    }

    // -----------------------------------------------------------------------
    // OD-203: the 128-bit product by its 64-bit limbs
    // -----------------------------------------------------------------------

    /// Slice 22's identity groups (the design's `smtq22.py` `norm_rule22`),
    /// tried after the "v18" identities and before the slice-19 groups:
    /// `limb` ([`Self::limb_product`]), `addhi0` ([`Self::add_high_zero`]) and
    /// `acmul` ([`Self::sorted_sum`]).
    fn rule_v22(&mut self, node: Id) -> Option<Id> {
        if self.has(Groups::LIMB)
            && let Some(limbs) = self.limb_product(node)
        {
            return Some(limbs);
        }
        if self.has(Groups::ADDHI0)
            && let Some(sum) = self.add_high_zero(node)
        {
            return Some(sum);
        }
        if self.has(Groups::CATNF)
            && let Some(moved) = self.bit_move_normal(node)
        {
            return Some(moved);
        }
        if self.has(Groups::ACMUL) {
            return self.sorted_sum(node);
        }
        None
    }

    /// `catnf` ([`Groups::CATNF`], OD-204): a normal form of bit moves, each
    /// an identity on every input:
    ///
    /// * an extract across both halves of a concatenation is the
    ///   concatenation of the two extracts: `extract[h:l](concat a b)`, `l <
    ///   |b| <= h`, is `(concat a[h-|b|:0] b[|b|-1:l])`;
    /// * an extract across a zero extension's boundary is a zero extension:
    ///   `extract[h:l](zext y)`, `l < |y| <= h`, is `(zext_{h-|y|+1}
    ///   y[|y|-1:l])`;
    /// * concatenations nest right: `(concat (concat a b) c)` is `(concat a
    ///   (concat b c))`;
    /// * adjacent extracts of one term at the head of a concatenation chain
    ///   merge: `(concat t[h:m] (concat t[m-1:l] r))` is `(concat t[h:l] r)`;
    /// * the `bvor` of a zero extension of `x` and a right-nested
    ///   concatenation chain ending in `0_|x|` (disjoint bits) is the chain
    ///   with `x` in place of its zeros.
    ///
    /// Each new extract is built with one "v18" step.
    fn bit_move_normal(&mut self, node: Id) -> Option<Id> {
        let one_step = |terms: &mut Self, term: Id| terms.rule_v18(term).unwrap_or(term);
        match self.op(node).clone() {
            Op::Extract(high, low) => {
                let x = self.arg(node, 0);
                match self.op(x).clone() {
                    Op::Concat => {
                        let (a, b) = (self.arg(x, 0), self.arg(x, 1));
                        let wb = self.width(b);
                        if low < wb && wb <= high {
                            let top = self.extract(a, high - wb, 0);
                            let top = one_step(self, top);
                            let bottom = self.extract(b, wb - 1, low);
                            let bottom = one_step(self, bottom);
                            return Some(self.mk(Op::Concat, vec![top, bottom]));
                        }
                    }
                    Op::ZeroExtend(_) => {
                        let y = self.arg(x, 0);
                        let wy = self.width(y);
                        if low < wy && wy <= high {
                            let inner = self.extract(y, wy - 1, low);
                            let inner = one_step(self, inner);
                            return Some(self.mk(Op::ZeroExtend(high - wy + 1), vec![inner]));
                        }
                    }
                    _ => {}
                }
                None
            }
            Op::Concat => {
                let (a, b) = (self.arg(node, 0), self.arg(node, 1));
                if *self.op(a) == Op::Concat {
                    let (a1, a2) = (self.arg(a, 0), self.arg(a, 1));
                    let inner = self.mk(Op::Concat, vec![a2, b]);
                    return Some(self.mk(Op::Concat, vec![a1, inner]));
                }
                if let Op::Extract(h1, l1) = *self.op(a)
                    && *self.op(b) == Op::Concat
                {
                    let (c, rest) = (self.arg(b, 0), self.arg(b, 1));
                    if let Op::Extract(h2, l2) = *self.op(c)
                        && self.arg(c, 0) == self.arg(a, 0)
                        && l1 == h2 + 1
                    {
                        let merged = self.extract(self.arg(a, 0), h1, l2);
                        let merged = one_step(self, merged);
                        return Some(self.mk(Op::Concat, vec![merged, rest]));
                    }
                }
                None
            }
            Op::BvOr => {
                let (p0, p1) = (self.arg(node, 0), self.arg(node, 1));
                for (p, q) in [(p0, p1), (p1, p0)] {
                    if !matches!(self.op(p), Op::ZeroExtend(_)) || *self.op(q) != Op::Concat {
                        continue;
                    }
                    let x = self.arg(p, 0);
                    let mut chain = Vec::new();
                    let mut tail = q;
                    while *self.op(tail) == Op::Concat {
                        chain.push(self.arg(tail, 0));
                        tail = self.arg(tail, 1);
                    }
                    if self.constant(tail) == Some(0) && self.width(tail) == self.width(x) {
                        let mut joined = x;
                        for piece in chain.into_iter().rev() {
                            joined = self.mk(Op::Concat, vec![piece, joined]);
                        }
                        return Some(joined);
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Whether `x` (of the product's width `2h`, `h` [`Self::limb`]) is the
    /// extension of a term of at most `h` bits, or a constant below `2^h`:
    /// its high limb is zeros or copies of its sign bit. A product of two
    /// such operands is a widening product, which `ovf`, `ovf2`, `sovf` and
    /// `magic` read and `limb` leaves as it is (so it never rewrites its own
    /// partial product).
    fn is_limb_extension(&self, x: Id) -> bool {
        let half = self.limb;
        match self.op(x) {
            Op::ZeroExtend(_) | Op::SignExtend(_) => self.width(self.arg(x, 0)) <= half,
            Op::Const(value, _) => below_pow2(u128::from(*value), half),
            _ => false,
        }
    }

    /// `limb` ([`Groups::LIMB`]): a product `(bvmul x y)` of width `2h` (`h`
    /// [`Self::limb`], 64 in production), unless both operands are
    /// [`Self::is_limb_extension`], is
    ///
    /// ```text
    /// (bvadd (bvmul (zero_extend_h x[h-1:0]) (zero_extend_h y[h-1:0]))
    ///        (concat (bvadd (bvmul x[2h-1:h] y[h-1:0]) (bvmul x[h-1:0] y[2h-1:h]))
    ///                0_h))
    /// ```
    ///
    /// Exact on every input: with `x = xH 2^h + xL` and `y = yH 2^h + yL`,
    /// `x y = xL yL + (xH yL + xL yH) 2^h + xH yH 2^2h`, and modulo `2^2h`
    /// the last term vanishes and the middle one is its residue modulo `2^h`
    /// times `2^h`. Each operand's limbs and the partial product's operands
    /// are built with one "v18" step, so a constant operand comes out folded
    /// (a zero extension of a constant is the wide constant) and the rule
    /// does not oscillate with constant folding.
    fn limb_product(&mut self, node: Id) -> Option<Id> {
        let half = self.limb;
        if *self.op(node) != Op::BvMul || self.width(node) != 2 * half {
            return None;
        }
        let (x, y) = (self.arg(node, 0), self.arg(node, 1));
        if self.is_limb_extension(x) && self.is_limb_extension(y) {
            return None;
        }
        let one_step = |terms: &mut Self, term: Id| terms.rule_v18(term).unwrap_or(term);
        let (x_low, y_low) = (self.extract(x, half - 1, 0), self.extract(y, half - 1, 0));
        let (x_low, y_low) = (one_step(self, x_low), one_step(self, y_low));
        let (x_high, y_high) = (
            self.extract(x, 2 * half - 1, half),
            self.extract(y, 2 * half - 1, half),
        );
        let (x_high, y_high) = (one_step(self, x_high), one_step(self, y_high));
        let x_wide = self.mk(Op::ZeroExtend(half), vec![x_low]);
        let y_wide = self.mk(Op::ZeroExtend(half), vec![y_low]);
        let (x_wide, y_wide) = (one_step(self, x_wide), one_step(self, y_wide));
        let partial = self.mk(Op::BvMul, vec![x_wide, y_wide]);
        let high_low = self.mk(Op::BvMul, vec![x_high, y_low]);
        let low_high = self.mk(Op::BvMul, vec![x_low, y_high]);
        let cross = self.mk(Op::BvAdd, vec![high_low, low_high]);
        let zeros = self.zero(half);
        let shifted = self.mk(Op::Concat, vec![cross, zeros]);
        Some(self.mk(Op::BvAdd, vec![partial, shifted]))
    }

    /// `addhi0` ([`Groups::ADDHI0`]): `extract[W-1:k](bvadd a (concat x 0_k))`,
    /// `k > 0`, either addend order, is `(bvadd a[W-1:k] x)`. Exact on every
    /// input: the other addend's low `k` bits are zero, so no carry leaves
    /// them, and the high bits of the sum are the sum of the high bits modulo
    /// `2^(W-k)`.
    fn add_high_zero(&mut self, node: Id) -> Option<Id> {
        let Op::Extract(high, low) = *self.op(node) else {
            return None;
        };
        let sum = self.arg(node, 0);
        if low == 0 || high + 1 != self.width(sum) || *self.op(sum) != Op::BvAdd {
            return None;
        }
        let (s0, s1) = (self.arg(sum, 0), self.arg(sum, 1));
        for (a, b) in [(s0, s1), (s1, s0)] {
            if *self.op(b) != Op::Concat {
                continue;
            }
            let (x, zeros) = (self.arg(b, 0), self.arg(b, 1));
            if self.width(zeros) == low && self.constant(zeros) == Some(0) {
                let a_high = self.extract(a, high, low);
                return Some(self.mk(Op::BvAdd, vec![a_high, x]));
            }
        }
        None
    }

    /// Whether `t` is a product leaf of a limb-wide sum: a product of the
    /// limb's width, or the high limb of a widening product of two limbs
    /// (`extract[2h-1:h]` of a `2h`-bit product of two zero extensions of
    /// `h`-bit terms or constants below `2^h`), the addends `limb` and the
    /// selector's `mul`/`imul` chain leave in the high limb of a product.
    fn is_product_leaf(&self, t: Id) -> bool {
        let half = self.limb;
        match *self.op(t) {
            Op::BvMul => self.width(t) == half,
            Op::Extract(high, low) if high == 2 * half - 1 && low == half => {
                let product = self.arg(t, 0);
                *self.op(product) == Op::BvMul
                    && self.width(product) == 2 * half
                    && self
                        .args(product)
                        .iter()
                        .all(|&operand| match self.op(operand) {
                            Op::ZeroExtend(extra) => *extra == half,
                            Op::Const(value, _) => below_pow2(u128::from(*value), half),
                            _ => false,
                        })
            }
            _ => false,
        }
    }

    /// The addends of the `bvadd` tree at `t` (a non-sum is its own addend),
    /// left to right.
    fn addends(&self, t: Id, out: &mut Vec<Id>) {
        if *self.op(t) == Op::BvAdd {
            self.addends(self.arg(t, 0), out);
            self.addends(self.arg(t, 1), out);
        } else {
            out.push(t);
        }
    }

    /// `acmul` ([`Groups::ACMUL`]): a `bvadd` tree of the limb's width with a
    /// product leaf ([`Self::is_product_leaf`]) is its addends sorted by
    /// [`Self::structural_key`] and nested right. Exact on every input:
    /// `bvadd` is associative and commutative modulo `2^w`. Scoped to sums
    /// with a product leaf, measured (the slice-22 design, §2.3): sorting
    /// every sum reorders unrelated ones, and `u64::carrying_mul_add`'s
    /// theorem, certified in 8.5 s, then times out on bytes that differ only
    /// in addend order. The key is the term's structure, never the order the
    /// table created it in, so a sum is spelled alike in every theorem.
    fn sorted_sum(&mut self, node: Id) -> Option<Id> {
        if *self.op(node) != Op::BvAdd || self.width(node) != self.limb {
            return None;
        }
        let mut leaves = Vec::new();
        self.addends(node, &mut leaves);
        if !leaves.iter().any(|&leaf| self.is_product_leaf(leaf)) {
            return None;
        }
        let mut keyed: Vec<(u128, Id)> = leaves
            .iter()
            .map(|&leaf| (self.structural_key(leaf), leaf))
            .collect();
        // Equal keys are one term (or a 128-bit collision, which only
        // leaves those two in their tree order): the sort is stable.
        keyed.sort_by_key(|(key, _)| *key);
        let (&(_, last), rest) = keyed.split_last()?;
        let sorted = rest.iter().rev().fold(last, |tail, &(_, leaf)| {
            self.mk(Op::BvAdd, vec![leaf, tail])
        });
        (sorted != node).then_some(sorted)
    }

    /// A key of `root`'s structure alone: an FNV-1a hash, 128 bits, of its
    /// operator, payload (a variable's name, a constant's value, an
    /// extract's or extension's bits), width and its operands' keys. Two
    /// terms of one structure get one key, whenever and in whatever theorem
    /// the table created them.
    fn structural_key(&mut self, root: Id) -> u128 {
        // Children first, never below a term already keyed.
        let mut order: Vec<Id> = Vec::new();
        let mut seen: HashSet<Id> = HashSet::new();
        let mut stack: Vec<(Id, bool)> = vec![(root, false)];
        while let Some((id, ready)) = stack.pop() {
            if self.keys.contains_key(&id) {
                continue;
            }
            if ready {
                order.push(id);
                continue;
            }
            if !seen.insert(id) {
                continue;
            }
            stack.push((id, true));
            for &child in self.args(id).iter().rev() {
                if !self.keys.contains_key(&child) {
                    stack.push((child, false));
                }
            }
        }
        for id in order {
            if self.keys.contains_key(&id) {
                continue;
            }
            const PRIME: u128 = 0x0000_0000_0100_0000_0000_0000_0000_013b;
            let mut hash: u128 = 0x6c62_272e_07bb_0142_62b8_2175_6295_c58d;
            let mut feed = |bytes: &[u8]| {
                for byte in bytes {
                    hash ^= u128::from(*byte);
                    hash = hash.wrapping_mul(PRIME);
                }
            };
            let (op, args) = &self.nodes[id as usize];
            let (tag, payload): (u8, Vec<u8>) = match op {
                Op::Var(name, _) => (0, name.as_bytes().to_vec()),
                Op::Const(value, _) => (1, value.to_le_bytes().to_vec()),
                Op::True => (2, Vec::new()),
                Op::False => (3, Vec::new()),
                Op::BvAdd => (4, Vec::new()),
                Op::BvSub => (5, Vec::new()),
                Op::BvMul => (6, Vec::new()),
                Op::BvUDiv => (7, Vec::new()),
                Op::BvURem => (8, Vec::new()),
                Op::BvSDiv => (9, Vec::new()),
                Op::BvNeg => (10, Vec::new()),
                Op::BvAnd => (11, Vec::new()),
                Op::BvOr => (12, Vec::new()),
                Op::BvXor => (13, Vec::new()),
                Op::BvShl => (14, Vec::new()),
                Op::BvLshr => (15, Vec::new()),
                Op::BvAshr => (16, Vec::new()),
                Op::Eq => (17, Vec::new()),
                Op::Not => (18, Vec::new()),
                Op::And => (19, Vec::new()),
                Op::Or => (20, Vec::new()),
                Op::Ult => (21, Vec::new()),
                Op::Ule => (22, Vec::new()),
                Op::Ugt => (23, Vec::new()),
                Op::Uge => (24, Vec::new()),
                Op::Slt => (25, Vec::new()),
                Op::Sle => (26, Vec::new()),
                Op::Sgt => (27, Vec::new()),
                Op::Sge => (28, Vec::new()),
                Op::Ite => (29, Vec::new()),
                Op::Extract(high, low) => (30, [high.to_le_bytes(), low.to_le_bytes()].concat()),
                Op::Concat => (31, Vec::new()),
                Op::ZeroExtend(extra) => (32, extra.to_le_bytes().to_vec()),
                Op::SignExtend(extra) => (33, extra.to_le_bytes().to_vec()),
            };
            feed(&[tag]);
            feed(&(payload.len() as u32).to_le_bytes());
            feed(&payload);
            feed(&self.widths[id as usize].to_le_bytes());
            for arg in args {
                feed(&self.keys[arg].to_le_bytes());
            }
            self.keys.insert(id, hash);
        }
        self.keys[&root]
    }

    /// `x[high:0]`, one [`Self::rule_v18`] step applied when one applies.
    fn low_bits(&mut self, x: Id, high: u32) -> Id {
        if high + 1 == self.width(x) {
            return x;
        }
        let bits = self.extract(x, high, 0);
        self.rule_v18(bits).unwrap_or(bits)
    }

    /// The slice-19 identity groups (the measurement's `smtq19.py`
    /// `norm_rule19`), tried when no "v18" identity applies.
    fn rule_v19(&mut self, node: Id) -> Option<Id> {
        let op = self.op(node).clone();
        let args = self.args(node).to_vec();
        let width = self.width(node);
        if let Op::Extract(high, 0) = op {
            // `mullo` / `addlo`: the low bits of a product, a sum, a
            // difference, a bitwise operation or a negation depend only on
            // the operands' low bits.
            let x = args[0];
            if high + 1 < self.width(x) {
                let inner = self.op(x).clone();
                let operands = self.args(x).to_vec();
                match inner {
                    Op::BvMul if self.has(Groups::MULLO) => {
                        let a = self.low_bits(operands[0], high);
                        let b = self.low_bits(operands[1], high);
                        return Some(self.mk(Op::BvMul, vec![a, b]));
                    }
                    Op::BvAdd | Op::BvSub | Op::BvAnd | Op::BvOr | Op::BvXor
                        if self.has(Groups::ADDLO) =>
                    {
                        let a = self.low_bits(operands[0], high);
                        let b = self.low_bits(operands[1], high);
                        return Some(self.mk(inner, vec![a, b]));
                    }
                    Op::BvNeg if self.has(Groups::ADDLO) => {
                        let a = self.low_bits(operands[0], high);
                        return Some(self.mk(Op::BvNeg, vec![a]));
                    }
                    _ => {}
                }
            }
            return None;
        }
        if matches!(op, Op::BvLshr | Op::BvShl) && self.has(Groups::SHR) {
            // A shift by a constant `0 < k < W`: the bits moved, zeros in.
            let (x, amount) = (args[0], args[1]);
            if let Some(k) = self.constant(amount)
                && k > 0
                && k < u64::from(width)
            {
                let k = k as u32;
                return Some(if op == Op::BvLshr {
                    let bits = self.extract(x, width - 1, k);
                    self.mk(Op::ZeroExtend(k), vec![bits])
                } else {
                    let bits = self.extract(x, width - 1 - k, 0);
                    let zeros = self.zero(k);
                    self.mk(Op::Concat, vec![bits, zeros])
                });
            }
            return None;
        }
        if self.has(Groups::CMP) {
            let (a, b) = match args.as_slice() {
                [a, b] => (*a, *b),
                _ => (0, 0),
            };
            match op {
                Op::Uge => {
                    let lt = self.mk(Op::Ult, vec![a, b]);
                    return Some(self.not(lt));
                }
                Op::Ugt => return Some(self.mk(Op::Ult, vec![b, a])),
                Op::Ule => {
                    let lt = self.mk(Op::Ult, vec![b, a]);
                    return Some(self.not(lt));
                }
                Op::Sge => {
                    let lt = self.mk(Op::Slt, vec![a, b]);
                    return Some(self.not(lt));
                }
                Op::Sgt => return Some(self.mk(Op::Slt, vec![b, a])),
                Op::Sle => {
                    let lt = self.mk(Op::Slt, vec![b, a]);
                    return Some(self.not(lt));
                }
                Op::Or => {
                    // `(or (bvult p q) (= p q))` is `(not (bvult q p))`.
                    for (x, y) in [(a, b), (b, a)] {
                        if let (Op::Ult, Op::Eq) = (self.op(x), self.op(y)) {
                            let (p, q) = (self.arg(x, 0), self.arg(x, 1));
                            let compared: HashSet<Id> = self.args(x).iter().copied().collect();
                            let equated: HashSet<Id> = self.args(y).iter().copied().collect();
                            if compared == equated {
                                let lt = self.mk(Op::Ult, vec![q, p]);
                                return Some(self.not(lt));
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        if op == Op::Ite && self.has(Groups::ITEPULL) {
            let (c, t, e) = (args[0], args[1], args[2]);
            let (to, eo) = (self.op(t).clone(), self.op(e).clone());
            if to == eo
                && matches!(to, Op::ZeroExtend(_) | Op::SignExtend(_) | Op::Extract(..))
                && self.width(self.arg(t, 0)) == self.width(self.arg(e, 0))
            {
                let (ta, ea) = (self.arg(t, 0), self.arg(e, 0));
                let chosen = self.mk(Op::Ite, vec![c, ta, ea]);
                return Some(self.mk(to, vec![chosen]));
            }
        }
        if op == Op::Eq && (self.has(Groups::OVF2) || self.has(Groups::SOVF)) {
            // `(= (zext L) P)` with `P` a product whose low bits are `L` (not
            // an extract: `ovf` takes that one): `P`'s high bits are zero;
            // `(= (sext L) P)`: they are all equal to `L`'s sign bit.
            let (a, b) = (args[0], args[1]);
            for (x, y) in [(a, b), (b, a)] {
                let extension = self.op(x).clone();
                if !matches!(extension, Op::ZeroExtend(_) | Op::SignExtend(_))
                    || *self.op(y) != Op::BvMul
                {
                    continue;
                }
                let low = self.arg(x, 0);
                if matches!(self.op(low), Op::Extract(..)) {
                    continue;
                }
                let (wide, narrow) = (self.width(y), self.width(low));
                if narrow >= wide {
                    continue;
                }
                let bits = self.extract(y, narrow - 1, 0);
                if self.normalized(bits) != low {
                    continue;
                }
                if matches!(extension, Op::ZeroExtend(_)) && self.has(Groups::OVF2) {
                    let top = self.extract(y, wide - 1, narrow);
                    let zero = self.zero(wide - narrow);
                    return Some(self.eq(top, zero));
                }
                if matches!(extension, Op::SignExtend(_))
                    && self.has(Groups::SOVF)
                    && let Some(sign) = self.sign_test(y, wide, narrow)
                {
                    return Some(sign);
                }
            }
        }
        if op == Op::BvMul && self.has(Groups::MULPOW2) {
            // A product by `2^k` (k below the width): the low bits shifted up.
            let (a, b) = (args[0], args[1]);
            for (x, y) in [(a, b), (b, a)] {
                if let Some(value) = self.constant(y)
                    && value > 1
                    && value.is_power_of_two()
                {
                    let k = value.trailing_zeros();
                    if k < width {
                        let bits = self.extract(x, width - 1 - k, 0);
                        let zeros = self.zero(k);
                        return Some(self.mk(Op::Concat, vec![bits, zeros]));
                    }
                }
            }
        }
        if op == Op::Eq && self.has(Groups::SOVF) {
            // `(= (sext (y[n-1:0])) y)`: `y`'s high bits all equal its bit
            // `n - 1`.
            let (a, b) = (args[0], args[1]);
            for (x, y) in [(a, b), (b, a)] {
                if let Op::SignExtend(_) = self.op(x) {
                    let inner = self.arg(x, 0);
                    if let Op::Extract(high, 0) = *self.op(inner)
                        && self.arg(inner, 0) == y
                    {
                        let (wide, narrow) = (self.width(y), high + 1);
                        if narrow < wide
                            && let Some(sign) = self.sign_test(y, wide, narrow)
                        {
                            return Some(sign);
                        }
                    }
                }
            }
        }
        // OD-196, last: the quotient range, `magic`, `uremdef`.
        if self.has(Groups::RANGE)
            && let Some(quotient) = self.quotient_range(node)
        {
            return Some(quotient);
        }
        if self.has(Groups::MAGIC)
            && let Some(quotient) = self.magic(node)
        {
            return Some(quotient);
        }
        if self.has(Groups::UREMDEF) {
            return self.remainder_definition(node);
        }
        None
    }

    /// `y[W-1:n-1]` all zeros or all ones: `y` (`W` bits) is the sign
    /// extension of its low `n` bits. `None` when the all-ones constant is
    /// wider than a constant field holds (the test is then left as it is).
    fn sign_test(&mut self, y: Id, wide: u32, narrow: u32) -> Option<Id> {
        let top_width = wide - narrow + 1;
        if top_width > 64 {
            return None;
        }
        let ones = self.cnst((1u128 << top_width) - 1, top_width)?;
        let top = self.extract(y, wide - 1, narrow - 1);
        let zero = self.zero(top_width);
        let zeros = self.eq(top, zero);
        let all_ones = self.eq(top, ones);
        Some(self.mk(Op::Or, vec![zeros, all_ones]))
    }

    // -----------------------------------------------------------------------
    // OD-196: a constant-divisor multiply-high is the quotient it computes
    // -----------------------------------------------------------------------

    /// `id` with names looked through: while it is a name the round has
    /// numbered ([`Terms::rhs_of`], filled only with [`Groups::MAGIC`]), its
    /// right-hand side (at most [`MAX_LOOK_THROUGH`] names). Exact: a name
    /// equals its right-hand side on every input that satisfies the
    /// definitions.
    fn resolved(&self, mut id: Id) -> Id {
        for _ in 0..MAX_LOOK_THROUGH {
            match self.var_name(id).and_then(|name| self.rhs_of.get(name)) {
                Some(&rhs) => id = rhs,
                None => break,
            }
        }
        id
    }

    /// [`Self::resolved`], and the low `w` bits of a name defined as
    /// `zero_extend(t)` with `t` of `w` bits are `t` (an extension leaves the
    /// low bits unchanged).
    fn peeled(&self, id: Id) -> Id {
        if let Op::Extract(high, 0) = *self.op(id) {
            let extended = self.resolved(self.arg(id, 0));
            if let Op::ZeroExtend(_) = self.op(extended) {
                let t = self.arg(extended, 0);
                if self.width(t) == high + 1 {
                    return self.resolved(t);
                }
            }
        }
        self.resolved(id)
    }

    /// Whether `a` and `b` are one term, through names and peeled low bits.
    fn same(&self, a: Id, b: Id) -> bool {
        a == b || self.peeled(a) == self.peeled(b)
    }

    /// The plain multiply-high: `t = extract[hi:lo](P)` with `P` (looked
    /// through) `(bvmul (zero_extend x) C)` in either order, `C` a constant,
    /// such that the product never wraps its width `W` (`(2^N - 1) * C <
    /// 2^W`, `x` of `N` bits) and no bit of `floor(x * C / 2^lo)` lies above
    /// `hi` (`floor((2^N - 1) * C / 2^lo) < 2^(hi - lo + 1)`): then `t` is
    /// exactly `floor(x * C / 2^lo)` for every `x`. Returns `(x, C, lo)`.
    fn multiply_high(&self, t: Id) -> Option<(Id, u128, u32)> {
        let Op::Extract(high, low) = *self.op(t) else {
            return None;
        };
        let product = self.resolved(self.arg(t, 0));
        if *self.op(product) != Op::BvMul {
            return None;
        }
        let wide = self.width(product);
        let (p0, p1) = (self.arg(product, 0), self.arg(product, 1));
        for (a, b) in [(p0, p1), (p1, p0)] {
            let Some(multiplier) = self.constant(b) else {
                continue;
            };
            let Op::ZeroExtend(_) = self.op(a) else {
                continue;
            };
            let x = self.arg(a, 0);
            let n = self.width(x);
            // The largest product, `(2^N - 1) * C`, below `2^W`: no wrap.
            let top = match max_of(n).checked_mul(u128::from(multiplier)) {
                Some(top) if below_pow2(top, wide) => top,
                _ => return None,
            };
            // No quotient bit above `hi`.
            if !below_pow2(top >> low, high - low + 1) {
                return None;
            }
            return Some((x, u128::from(multiplier), low));
        }
        None
    }

    /// `x` (of `n` bits) divided by `d` as a term of `t`'s width: the
    /// quotient, zero-extended or its low bits (exact: the callers have shown
    /// the quotient fits `t`'s width).
    fn quotient_as(&mut self, t: Id, x: Id, d: u128) -> Option<Id> {
        let n = self.width(x);
        let divisor = self.cnst(d, n)?;
        let quotient = self.mk(Op::BvUDiv, vec![x, divisor]);
        let r = self.width(t);
        Some(match r.cmp(&n) {
            std::cmp::Ordering::Equal => quotient,
            std::cmp::Ordering::Greater => self.mk(Op::ZeroExtend(r - n), vec![quotient]),
            std::cmp::Ordering::Less => self.extract(quotient, r - 1, 0),
        })
    }

    /// `magic` ([`Groups::MAGIC`]): a multiply-high by a constant that
    /// computes `floor(x / d)` for EVERY `n`-bit `x` is `(bvudiv x d)`, in two
    /// machine shapes, each only when [`magic_divisor`]'s integer condition
    /// holds for the instance's own constants:
    ///
    /// * plain: `extract[hi:lo](bvmul (zero_extend x) C)`, lo > 0, which is
    ///   `floor(x * C / 2^lo)` ([`Self::multiply_high`]): `M = C`, `k = lo`;
    /// * add: `extract[n-1:lo](bvadd h (zero_extend_1 (extract[n-1:1]
    ///   (bvsub x h))))` with `h` the plain multiply-high
    ///   `extract[2n-1:n](bvmul (zero_extend_n x) C)`, `C < 2^n`: `h <= x`, so
    ///   the sum is `floor((x + h) / 2)` without wrap, and the term is
    ///   `floor(x * (2^n + C) / 2^(n + 1 + lo))`: `M = 2^n + C`, `k = n + 1 +
    ///   lo`.
    fn magic(&mut self, node: Id) -> Option<Id> {
        let Op::Extract(high, low) = *self.op(node) else {
            return None;
        };
        if let Some((x, multiplier, shift)) = self.multiply_high(node)
            && shift > 0
            && let Some(d) = magic_divisor(self.width(x), multiplier, shift)
        {
            return self.quotient_as(node, x, d);
        }
        let sum = self.resolved(self.arg(node, 0));
        if *self.op(sum) != Op::BvAdd {
            return None;
        }
        let n = self.width(sum);
        // The add shape's `h` is the high half of a `2n`-bit product.
        if !(2..=64).contains(&n) {
            return None;
        }
        let (s0, s1) = (self.arg(sum, 0), self.arg(sum, 1));
        for (h, z) in [(s0, s1), (s1, s0)] {
            let Op::ZeroExtend(1) = *self.op(z) else {
                continue;
            };
            let halved = self.arg(z, 0);
            if *self.op(halved) != Op::Extract(n - 1, 1) {
                continue;
            }
            let difference = self.resolved(self.arg(halved, 0));
            if *self.op(difference) != Op::BvSub || !self.same(self.arg(difference, 1), h) {
                continue;
            }
            let Some((x, multiplier, shift)) = self.multiply_high(self.peeled(h)) else {
                continue;
            };
            if shift != n
                || self.width(x) != n
                || !self.same(self.arg(difference, 0), x)
                || !below_pow2(multiplier, n)
                || high != n - 1
            {
                continue;
            }
            let effective = (1u128 << n) + multiplier;
            if let Some(d) = magic_divisor(n, effective, n + 1 + low) {
                return self.quotient_as(node, x, d);
            }
        }
        None
    }

    /// The quotient range ([`Groups::RANGE`]): `(zero_extend_j (extract[R-1:0]
    /// (bvudiv x C)))`, `C` a non-zero constant, `x` of `n` bits, the
    /// quotient below `2^R` for every `x` (`(2^n - 1) div C < 2^R`) and `j +
    /// R >= n`, is `(zero_extend_{j+R-n} (bvudiv x C))` (exact: the bits the
    /// extract drops are zero).
    fn quotient_range(&mut self, node: Id) -> Option<Id> {
        let Op::ZeroExtend(j) = *self.op(node) else {
            return None;
        };
        let low_bits = self.arg(node, 0);
        let Op::Extract(high, 0) = *self.op(low_bits) else {
            return None;
        };
        let r = high + 1;
        let quotient = self.arg(low_bits, 0);
        if *self.op(quotient) != Op::BvUDiv {
            return None;
        }
        let divisor = self.constant(self.arg(quotient, 1)).filter(|&c| c != 0)?;
        let n = self.width(quotient);
        if !below_pow2(max_of(n) / u128::from(divisor), r) || j + r < n {
            return None;
        }
        let extra = j + r - n;
        Some(if extra == 0 {
            quotient
        } else {
            self.mk(Op::ZeroExtend(extra), vec![quotient])
        })
    }

    /// `uremdef` ([`Groups::UREMDEF`]): `(bvurem x C)`, `C` a non-zero
    /// constant, is `(bvsub x (bvmul (bvudiv x C) C))`, SMT-LIB's own
    /// definition of the remainder.
    fn remainder_definition(&mut self, node: Id) -> Option<Id> {
        if *self.op(node) != Op::BvURem {
            return None;
        }
        let (x, c) = (self.arg(node, 0), self.arg(node, 1));
        self.constant(c).filter(|&value| value != 0)?;
        let quotient = self.mk(Op::BvUDiv, vec![x, c]);
        let product = self.mk(Op::BvMul, vec![quotient, c]);
        Some(self.mk(Op::BvSub, vec![x, product]))
    }

    // -----------------------------------------------------------------------
    // The definitions and the claims
    // -----------------------------------------------------------------------

    /// Whether `expr` only moves bits of variables and constants (an
    /// extract, an extension or a concatenation of them) in at most
    /// `budget` nodes.
    fn moves_bits(&self, expr: Id, budget: &mut usize) -> bool {
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        match self.op(expr) {
            Op::Var(..) | Op::Const(..) => true,
            Op::Extract(..) | Op::ZeroExtend(_) | Op::SignExtend(_) => {
                self.moves_bits(self.arg(expr, 0), budget)
            }
            Op::Concat => {
                self.moves_bits(self.arg(expr, 0), budget)
                    && self.moves_bits(self.arg(expr, 1), budget)
            }
            _ => false,
        }
    }

    /// `cse`: every proper subterm of `root` (and `root` itself once its
    /// operands are renamed) equal to an earlier kept definition's
    /// right-hand side is that definition's name.
    fn cse(&mut self, root: Id, numbered: &HashMap<Id, String>) -> Id {
        if numbered.is_empty() {
            return root;
        }
        self.rewrite(root, &mut |terms, node| {
            let name = numbered.get(&node)?;
            (node != root).then(|| {
                let width = terms.width(node);
                terms.var(name, width)
            })
        })
    }

    /// `look` (and `peel`): an extract of a kept name whose definition,
    /// extracted and normalized, is a variable, a constant, a kept name's
    /// right-hand side, or an extension or extract of a variable is that
    /// term; with [`Groups::PEEL`], the low `w` bits of a kept name defined
    /// as an extension of a `w`-bit `t` are `t`.
    fn look(
        &mut self,
        root: Id,
        rhs_of: &HashMap<String, Id>,
        numbered: &HashMap<Id, String>,
    ) -> Id {
        let rewritten = self.rewrite(root, &mut |terms, node| {
            let Op::Extract(high, low) = *terms.op(node) else {
                return None;
            };
            let named = terms.arg(node, 0);
            let rhs = *rhs_of.get(terms.var_name(named)?)?;
            let bits = terms.extract(rhs, high, low);
            let candidate = terms.normalized(bits);
            let candidate = match numbered.get(&candidate) {
                Some(name) => {
                    let width = terms.width(candidate);
                    terms.var(name, width)
                }
                None => {
                    let renamed = terms.cse(candidate, numbered);
                    terms.normalized(renamed)
                }
            };
            if terms.is_var(candidate) || terms.constant(candidate).is_some() {
                return Some(candidate);
            }
            if terms.has(Groups::PEEL)
                && low == 0
                && let Op::ZeroExtend(_) | Op::SignExtend(_) = terms.op(rhs)
            {
                let t = terms.arg(rhs, 0);
                if high + 1 == terms.width(t) {
                    return Some(match numbered.get(&t) {
                        Some(name) => {
                            let width = terms.width(t);
                            terms.var(name, width)
                        }
                        None => t,
                    });
                }
            }
            if let Some(name) = numbered.get(&candidate) {
                let width = terms.width(candidate);
                return Some(terms.var(name, width));
            }
            match terms.op(candidate) {
                Op::ZeroExtend(_) | Op::SignExtend(_) | Op::Extract(..)
                    if terms.is_var(terms.arg(candidate, 0)) =>
                {
                    Some(candidate)
                }
                _ => None,
            }
        });
        if rewritten != root {
            self.normalized(rewritten)
        } else {
            root
        }
    }

    /// The conjuncts of a right-nested conjunction.
    fn conjuncts(&self, mut root: Id) -> Vec<Id> {
        let mut terms = Vec::new();
        while let Op::And = self.op(root) {
            terms.push(self.arg(root, 0));
            root = self.arg(root, 1);
        }
        terms.push(root);
        terms
    }

    /// The right-nested conjunction of `terms` (`None` when empty).
    fn conjunction(&mut self, terms: &[Id]) -> Option<Id> {
        let (&last, rest) = terms.split_last()?;
        Some(
            rest.iter()
                .rev()
                .fold(last, |tail, &term| self.mk(Op::And, vec![term, tail])),
        )
    }

    /// A guarded item `(or (not G) X)`: `(G, X)`.
    fn guarded(&self, item: Id) -> Option<(Id, Id)> {
        if *self.op(item) != Op::Or {
            return None;
        }
        let (lhs, rhs) = (self.arg(item, 0), self.arg(item, 1));
        (*self.op(lhs) == Op::Not).then(|| (self.arg(lhs, 0), rhs))
    }

    /// OD-203 ([`Groups::GUARD`]): a guarded item `(or (not G) X)` whose
    /// guard a normalization of the whole claims folded (`look` normalizes
    /// the claims it rewrites as one term, and `(not (not L))` is `L`), so
    /// it reads `(or L X)` with `L` a Boolean term that is no negation: the
    /// guard `(not L)` and the body `X`. Exact: `(or L X)` is `(or (not (not
    /// L)) X)`. Without it the item fails the structural check (a DAG's
    /// claim must read `(or (not C) X)`) and the theorem keeps slice 18's
    /// spelling (measured on `checked_mul`'s `u128` and `i128` theorems).
    /// A top-level `(or ...)` item fails that check in every other form, so
    /// no theorem the canonical spelling states today is changed.
    fn folded_guard(&mut self, item: Id) -> Option<(Id, Id)> {
        if !self.has(Groups::GUARD) || *self.op(item) != Op::Or {
            return None;
        }
        let (literal, body) = (self.arg(item, 0), self.arg(item, 1));
        if self.width(literal) != 0 || *self.op(literal) == Op::Not {
            return None;
        }
        Some((self.not(literal), body))
    }

    /// One claim conjunct normalized: an equation of two bit-vectors keeps
    /// its shape (both sides normalized; dropped when they are one term);
    /// anything else is normalized and split into its conjuncts, `true`
    /// dropped.
    fn normal_conjunct(&mut self, claim: Id) -> Vec<Id> {
        if *self.op(claim) == Op::Eq && self.width(self.arg(claim, 0)) > 0 {
            let lhs = self.arg(claim, 0);
            let rhs = self.arg(claim, 1);
            let (lhs, rhs) = (self.normalized(lhs), self.normalized(rhs));
            return if lhs == rhs {
                Vec::new()
            } else {
                vec![self.eq(lhs, rhs)]
            };
        }
        let normal = self.normalized(claim);
        if normal == self.t {
            return Vec::new();
        }
        self.conjuncts(normal)
            .into_iter()
            .filter(|&term| term != self.t)
            .collect()
    }

    /// The claims normalized with the skeleton the structural check reads
    /// kept (OD-188's `folded_claims` with [`Self::normalized`]): a guard
    /// literal normalized to `true` is dropped from its guard, an item whose
    /// guard has a literal normalized to `false` holds and is dropped, an item
    /// whose body empties is dropped, and an item whose guard empties is its
    /// body's conjuncts. `None` when no claim is left.
    fn normalize_claims(&mut self, claims: Id) -> Option<Id> {
        let mut items: Vec<Id> = Vec::new();
        for item in self.conjuncts(claims) {
            match self.guarded(item).or_else(|| self.folded_guard(item)) {
                Some((guard, body)) => {
                    let mut literals = Vec::new();
                    for literal in self.conjuncts(guard) {
                        literals.push(self.normalized(literal));
                    }
                    if literals.contains(&self.f) {
                        continue;
                    }
                    literals.retain(|&literal| literal != self.t);
                    let mut normal_body = Vec::new();
                    for conjunct in self.conjuncts(body) {
                        normal_body.extend(self.normal_conjunct(conjunct));
                    }
                    let Some(conjoined) = self.conjunction(&normal_body) else {
                        continue;
                    };
                    match self.conjunction(&literals) {
                        Some(guard) => {
                            let negated = self.not(guard);
                            items.push(self.mk(Op::Or, vec![negated, conjoined]));
                        }
                        None => items.extend(normal_body),
                    }
                }
                None => {
                    let normal = self.normal_conjunct(item);
                    items.extend(normal);
                }
            }
        }
        self.conjunction(&items)
    }

    /// Every definition used at most once (counted in the written, tree form
    /// of the definitions and the claims) substituted into its use, in
    /// definition order (slice 9's `inline_single_use`), except a name
    /// defined as bits of a term wider than 64 bits that holds no product
    /// ([`Self::wide_bits`]), which is kept.
    fn inline_single_use(
        &mut self,
        definitions: Vec<(String, Id)>,
        claims: Id,
    ) -> (Vec<(String, Id)>, Id) {
        let roots: Vec<Id> = definitions
            .iter()
            .map(|(_, rhs)| *rhs)
            .chain([claims])
            .collect();
        let mut multiplicity: HashMap<Id, u64> = HashMap::new();
        for &root in &roots {
            *multiplicity.entry(root).or_default() += 1;
        }
        let mut uses: HashMap<String, u64> = HashMap::new();
        for id in self.topo(&roots).into_iter().rev() {
            let count = multiplicity.get(&id).copied().unwrap_or(0);
            if count == 0 {
                continue;
            }
            if let Some(name) = self.var_name(id) {
                let entry = uses.entry(name.to_owned()).or_default();
                *entry = entry.saturating_add(count);
            }
            for &child in self.args(id) {
                let entry = multiplicity.entry(child).or_default();
                *entry = entry.saturating_add(count);
            }
        }
        let mut env: HashMap<String, Id> = HashMap::new();
        let mut kept = Vec::with_capacity(definitions.len());
        for (name, rhs) in definitions {
            let rhs = self.substitute(rhs, &env);
            if uses.get(&name).copied().unwrap_or(0) <= 1 && !self.wide_bits(rhs) {
                env.insert(name, rhs);
            } else {
                kept.push((name, rhs));
            }
        }
        let claims = self.substitute(claims, &env);
        (kept, claims)
    }

    /// Whether `rhs` is bits of a term wider than 64 bits that holds no
    /// product (an `extract` of one: the half of a 128-bit sum, difference,
    /// negation, bitwise operation or selection), a definition
    /// [`Self::inline_single_use`] keeps as a name. Measured (AY 13556,
    /// 2026-10-26): `i128::wrapping_sub`'s theorem, whose only claim is the
    /// high half of its 128-bit difference, certifies in 1.5 s with that
    /// half named and times out at 30 s with it inlined. A half of a
    /// 128-bit product is inlined as the design's pipeline does: kept as a
    /// name, the multiply-highs of five roots' divisions by a constant kept
    /// their 128-bit products in the query after `magic` had rewritten
    /// their uses, and those queries, which certify inlined, timed out.
    /// Keeping a name is exact (the definition is unchanged).
    fn wide_bits(&self, rhs: Id) -> bool {
        if !matches!(self.op(rhs), Op::Extract(..)) || self.width(self.arg(rhs, 0)) <= 64 {
            return false;
        }
        !self
            .topo(&[rhs])
            .into_iter()
            .any(|id| *self.op(id) == Op::BvMul)
    }

    /// The claims without their identities (slice 9's `drop_identities`),
    /// with whether anything was dropped; `None` when no claim is left.
    fn drop_identities(&mut self, claims: Id) -> Option<(Id, bool)> {
        let identity = |terms: &Self, term: Id| {
            *terms.op(term) == Op::Eq && terms.arg(term, 0) == terms.arg(term, 1)
        };
        let mut dropped = false;
        let mut kept = Vec::new();
        for claim in self.conjuncts(claims) {
            if identity(self, claim) {
                dropped = true;
                continue;
            }
            if let Some((_, body)) = self.guarded(claim) {
                let terms = self.conjuncts(body);
                let rest: Vec<Id> = terms
                    .iter()
                    .copied()
                    .filter(|&term| !identity(self, term))
                    .collect();
                if rest.len() == terms.len() {
                    kept.push(claim);
                    continue;
                }
                dropped = true;
                if let Some(rest) = self.conjunction(&rest) {
                    let negated_guard = self.arg(claim, 0);
                    kept.push(self.mk(Op::Or, vec![negated_guard, rest]));
                }
                continue;
            }
            kept.push(claim);
        }
        let conjoined = self.conjunction(&kept)?;
        Some((conjoined, dropped))
    }

    /// One round of the pipeline (the measurement's `_one_round`):
    ///
    /// 1. in definition order, each right-hand side (earlier substitutions
    ///    made) normalized; one that only moves bits (at most
    ///    [`MAX_BIT_MOVE_NODES`] nodes) or is a Boolean constant is
    ///    substituted;
    /// 2. in order, each remaining right-hand side normalized, renamed by
    ///    `cse` and looked through by `look`; one that is a variable or a
    ///    constant is substituted, one that repeats an earlier kept
    ///    right-hand side is that name;
    /// 3. the claims renamed and looked through the same way and normalized
    ///    ([`Self::normalize_claims`]); then, to a fixpoint (at most
    ///    [`MAX_CLAIM_ROUNDS`]), single uses inlined, the claims normalized
    ///    and identities dropped.
    ///
    /// `None` when no claim is left.
    fn one_round(
        &mut self,
        definitions: &[(String, Id)],
        claims: Id,
    ) -> Option<(Vec<(String, Id)>, Id)> {
        // OD-196: `magic` looks through this round's kept names only.
        self.rhs_of.clear();
        let mut env: HashMap<String, Id> = HashMap::new();
        let mut kept: Vec<(String, Id)> = Vec::new();
        for (name, rhs) in definitions {
            let substituted = self.substitute(*rhs, &env);
            let rhs = self.normalized(substituted);
            let mut budget = MAX_BIT_MOVE_NODES;
            if self.moves_bits(rhs, &mut budget) || rhs == self.t || rhs == self.f {
                env.insert(name.clone(), rhs);
                continue;
            }
            kept.push((name.clone(), rhs));
        }
        let claims = self.substitute(claims, &env);
        let mut env: HashMap<String, Id> = HashMap::new();
        let mut numbered: HashMap<Id, String> = HashMap::new();
        let mut rhs_of: HashMap<String, Id> = HashMap::new();
        let mut numbered_kept: Vec<(String, Id)> = Vec::new();
        for (name, rhs) in kept {
            let substituted = self.substitute(rhs, &env);
            let mut rhs = self.normalized(substituted);
            if self.has(Groups::CSE) {
                let renamed = self.cse(rhs, &numbered);
                rhs = self.normalized(renamed);
            }
            if self.has(Groups::LOOK) {
                rhs = self.look(rhs, &rhs_of, &numbered);
            }
            if self.is_var(rhs) || self.constant(rhs).is_some() {
                env.insert(name, rhs);
                continue;
            }
            if let Some(earlier) = numbered.get(&rhs) {
                let width = self.width(rhs);
                let earlier = earlier.clone();
                let renamed = self.var(&earlier, width);
                env.insert(name, renamed);
                continue;
            }
            numbered.insert(rhs, name.clone());
            rhs_of.insert(name.clone(), rhs);
            if self.has(Groups::MAGIC) {
                self.rhs_of.insert(name.clone(), rhs);
            }
            numbered_kept.push((name, rhs));
        }
        let mut claims = self.substitute(claims, &env);
        if self.has(Groups::CSE) {
            claims = self.cse(claims, &numbered);
        }
        if self.has(Groups::LOOK) {
            claims = self.look(claims, &rhs_of, &numbered);
        }
        let claims = self.normalize_claims(claims)?;
        let (mut kept, mut stated) = self.inline_single_use(numbered_kept, claims);
        for _ in 0..MAX_CLAIM_ROUNDS {
            stated = self.normalize_claims(stated)?;
            let (dropped_claims, dropped) = self.drop_identities(stated)?;
            let (next, next_claims) = self.inline_single_use(kept.clone(), dropped_claims);
            if !dropped && next == kept && next_claims == stated {
                break;
            }
            kept = next;
            stated = next_claims;
        }
        Some((kept, stated))
    }

    /// The pipeline: [`Self::one_round`] repeated until it changes nothing
    /// (at most [`MAX_PIPELINE_ROUNDS`] rounds). `None` when no claim is left.
    pub(super) fn pipeline(
        &mut self,
        definitions: Vec<(String, Id)>,
        claims: Id,
    ) -> Option<(Vec<(String, Id)>, Id)> {
        let mut current = (definitions, claims);
        for _ in 0..MAX_PIPELINE_ROUNDS {
            let next = self.one_round(&current.0, current.1)?;
            if next == current {
                break;
            }
            current = next;
        }
        Some(current)
    }
}

/// `2^n - 1` (`n` at most 128).
fn max_of(n: u32) -> u128 {
    if n >= 128 {
        u128::MAX
    } else {
        (1u128 << n) - 1
    }
}

/// Whether `value < 2^k`.
fn below_pow2(value: u128, k: u32) -> bool {
    k >= 128 || value >> k == 0
}

/// THE integer side condition of `magic` (OD-196): the divisor `d` such that
/// `floor(x * m / 2^k) = floor(x / d)` for every `0 <= x < 2^n`, checked in
/// exact integers for the instance's own `n`, `m` and `k`; `None` when the
/// condition fails.
///
/// `d = ceil(2^k / m)` (`m >= 1`, `1 <= d < 2^n`), `e = m * d - 2^k >= 0`,
/// and the condition is `(2^n - 1) * e < 2^k`. It suffices (the sufficient
/// condition behind Granlund and Montgomery, "Division by Invariant Integers
/// using Multiplication", PLDI 1994, Theorem 4.2): writing `x = q d + r` with
/// `0 <= r < d`, `x m / 2^k = x / d + x e / (d 2^k) = q + (r 2^k + x e) /
/// (d 2^k)`, and `0 <= r 2^k + x e <= (d - 1) 2^k + x e < d 2^k` because `x
/// e <= (2^n - 1) e < 2^k`; so the floor is `q`. Unsigned only: no signed
/// shape is matched.
///
/// Every quantity is held exactly in 128 bits: `k <= 128`, `m < 2^128`;
/// with `2^k - 1 = q m + r'`, `d = q + 1` (`2^128` only for `m = 1`, `k =
/// 128`, which fails `d < 2^n`) and `e = m - 1 - r'` (no product is formed),
/// and `(2^n - 1) * e` overflowing 128 bits is at least `2^128 >= 2^k` (the
/// condition fails).
pub(super) fn magic_divisor(n: u32, m: u128, k: u32) -> Option<u128> {
    if m == 0 || n == 0 || n > 127 || k > 128 {
        return None;
    }
    // 2^k - 1, exactly (k <= 128).
    let below = max_of(k);
    let d = (below / m).checked_add(1)?;
    if !below_pow2(d, n) {
        return None;
    }
    let e = m - 1 - below % m;
    match max_of(n).checked_mul(e) {
        Some(product) if below_pow2(product, k) => Some(d),
        _ => None,
    }
}

/// Tests only: `expr` normalized ([`Terms::normalized`]) with `groups`;
/// `None` for a term outside the vocabulary.
#[cfg(test)]
pub(super) fn normalized_term(expr: &E, groups: Groups) -> Option<E> {
    normalized_term_with_limb(expr, groups, 64)
}

/// Tests only: [`normalized_term`] with limbs of `limb` bits (OD-203's
/// groups at a narrower width, to sweep them exhaustively).
#[cfg(test)]
pub(super) fn normalized_term_with_limb(expr: &E, groups: Groups, limb: u32) -> Option<E> {
    let mut terms = Terms::new(groups);
    terms.limb = limb;
    let id = terms.import(expr)?;
    let normal = terms.normalized(id);
    terms.export(normal)
}

/// Tests only: `claims` through [`Terms::normalize_claims`] (`None`: no
/// claim left, or a term outside the vocabulary).
#[cfg(test)]
pub(super) fn normalized_claims_term(claims: &E, groups: Groups) -> Option<E> {
    let mut terms = Terms::new(groups);
    let id = terms.import(claims)?;
    let normal = terms.normalize_claims(id)?;
    terms.export(normal)
}

/// Tests only: `expr` normalized in a table that has first imported
/// `first` (OD-203's `acmul` must spell a sum alike whatever the table
/// created before it).
#[cfg(test)]
pub(super) fn normalized_after(first: &E, expr: &E, groups: Groups) -> Option<E> {
    let mut terms = Terms::new(groups);
    terms.import(first)?;
    let id = terms.import(expr)?;
    let normal = terms.normalized(id);
    terms.export(normal)
}

/// Tests only: `expr` rewritten by `look` (and `peel`) under the kept
/// definitions `definitions` (each its own right-hand side's name, none
/// numbered); `None` for a term outside the vocabulary.
#[cfg(test)]
pub(super) fn looked_through(expr: &E, definitions: &[(String, E)], groups: Groups) -> Option<E> {
    let mut terms = Terms::new(groups);
    let mut rhs_of: HashMap<String, Id> = HashMap::new();
    for (name, rhs) in definitions {
        let id = terms.import(rhs)?;
        rhs_of.insert(name.clone(), id);
    }
    let id = terms.import(expr)?;
    let looked = terms.look(id, &rhs_of, &HashMap::new());
    terms.export(looked)
}

// ---------------------------------------------------------------------------
// Slice 23 (ruling OD-206): the generalization over arithmetic leaves
// ---------------------------------------------------------------------------

/// Slice 23 (OD-206): the free input naming the `k`-th arithmetic leaf of a
/// generalized obligation.
pub(crate) fn arith_leaf_name(k: usize) -> String {
    format!("ar{k}")
}

/// Whether `name` is an arithmetic leaf's name ([`arith_leaf_name`]).
pub(crate) fn is_arith_leaf_name(name: &str) -> bool {
    name.strip_prefix("ar")
        .is_some_and(|digits| !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()))
}

/// Slice 23 (OD-206): a theorem's definitions and sides generalized
/// ([`generalized`]): the definitions kept (in order), the sides, and the
/// leaves (each name and width, in number order).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Generalized {
    pub(super) definitions: Vec<(String, E)>,
    pub(super) sides: Vec<E>,
    pub(super) leaves: Vec<(String, u32)>,
    /// The term each leaf stands for (in leaf order), over the theorem's
    /// free inputs and names, in the canonical forms: what instantiation
    /// gives the leaf.
    pub(super) nodes: Vec<E>,
}

/// The kinds a barrel stage's shift may be ([`Terms::barrel_stage`]): a set
/// of [`SHL`], [`LSHR`] and [`ASHR`] (a stage whose arms are constants may
/// be several).
type ShiftKinds = u8;
const SHL: ShiftKinds = 1;
const LSHR: ShiftKinds = 2;
const ASHR: ShiftKinds = 4;

/// Slice 23 (ruling OD-206): `definitions` (in order) and `sides` (the
/// claims, or a one-path theorem's two sides) generalized over their
/// arithmetic leaves:
/// 1. `comm`: the operands of every product of two non-constant terms in one
///    order, by their structural keys ([`Terms::structural_key`], never the
///    table's creation order), so `a*b` and `b*a` are one term;
/// 2. `wide`: a product `(bvmul a b)` at `n` bits, where the widening
///    product of the same operands occurs (unsigned first, else signed), is
///    `((_ extract n-1 0) W)` of it;
/// 3. the leaves: every ARITHMETIC NODE ([`Terms::is_arith_node`]: a product
///    of two non-constant terms, a quotient or remainder by a non-constant
///    divisor, a variable shift's barrel) is a fresh free input `ar{k}` of
///    its width, one per distinct node, numbered in structural first
///    occurrence (definitions in order, then the sides, children first; the
///    operands of a node a leaf replaces are not visited);
/// 4. a definition that is then a bare leaf is that leaf (substituted), and
///    the definitions no side reaches are dropped.
///
/// Steps 1 and 2 are identities on every input (`comm`: `bvmul` is
/// commutative; `wide`: the low `n` bits of either extension's product are
/// the `n`-bit product; both swept exhaustively at small widths); step 3 is
/// a GENERALIZATION: what holds for every value of the leaves holds for the
/// values the operations compute (instantiation), never the converse (a
/// claim may need a bit of an operation: then the generalization is
/// satisfiable and only the exact theorem can credit). `None` for a term
/// outside the vocabulary, a theorem that already names a free input `ar{k}`,
/// or one with no arithmetic node.
pub(super) fn generalized(definitions: &[(String, E)], sides: &[E]) -> Option<Generalized> {
    let mut terms = Terms::new(Groups::NONE);
    let mut imported: Vec<(String, Id)> = Vec::with_capacity(definitions.len());
    for (name, expr) in definitions {
        imported.push((name.clone(), terms.import(expr)?));
    }
    let mut roots: Vec<Id> = Vec::with_capacity(sides.len());
    for side in sides {
        roots.push(terms.import(side)?);
    }
    terms.generalize(imported, roots)
}

impl Terms {
    /// Whether `root` reads no free input but the names of `constants`
    /// (definitions whose right-hand side reads none): a constant BY VALUE.
    fn closed_id(
        &self,
        root: Id,
        constants: &HashSet<String>,
        memo: &mut HashMap<Id, bool>,
    ) -> bool {
        let mut stack: Vec<(Id, bool)> = vec![(root, false)];
        while let Some((id, ready)) = stack.pop() {
            if memo.contains_key(&id) {
                continue;
            }
            if !ready {
                stack.push((id, true));
                for &child in self.args(id) {
                    if !memo.contains_key(&child) {
                        stack.push((child, false));
                    }
                }
                continue;
            }
            let closed = match self.op(id) {
                Op::Var(name, _) => constants.contains(name),
                Op::Const(..) | Op::True | Op::False => true,
                _ => self.args(id).iter().all(|arg| memo[arg]),
            };
            memo.insert(id, closed);
        }
        memo[&root]
    }

    /// `x` (of `2 * n` bits) as the `n`-bit operand of a widening product:
    /// `t` when `x` is the extension of kind `sign` of an `n`-bit `t`, or the
    /// extension of a narrower `t` re-spelled as its extension to `n` bits
    /// (`zext_2n(t) = zext_(2n-|t|)(t) = zext_n(zext_(n-|t|)(t))`, and the same
    /// for `sext`).
    fn wide_operand(&mut self, x: Id, sign: bool, n: u32) -> Option<Id> {
        let extra = match (self.op(x), sign) {
            (Op::ZeroExtend(extra), false) | (Op::SignExtend(extra), true) => *extra,
            _ => return None,
        };
        let t = self.arg(x, 0);
        let width = self.width(t);
        if width > n || extra + width != 2 * n {
            return None;
        }
        Some(if width == n {
            t
        } else if sign {
            self.mk(Op::SignExtend(n - width), vec![t])
        } else {
            self.mk(Op::ZeroExtend(n - width), vec![t])
        })
    }

    /// A product's operator key and operands: `(MulLo, w, x, y)` for
    /// `(bvmul x y)` at `w` bits, `(UMulWide, n, a, b)` / `(SMulWide, n, a,
    /// b)` when both operands are zero / sign extensions of terms of at most
    /// `n = w / 2` bits ([`Self::wide_operand`]); `None` for anything else.
    /// The caller excludes constant operands.
    fn product_key(&mut self, node: Id) -> Option<(ArithOp, u32, Id, Id)> {
        if *self.op(node) != Op::BvMul {
            return None;
        }
        let (x, y) = (self.arg(node, 0), self.arg(node, 1));
        let w = self.width(node);
        if w % 2 == 0 {
            let n = w / 2;
            for (sign, op) in [(false, ArithOp::UMulWide), (true, ArithOp::SMulWide)] {
                if let (Some(a), Some(b)) =
                    (self.wide_operand(x, sign, n), self.wide_operand(y, sign, n))
                {
                    return Some((op, n, a, b));
                }
            }
        }
        Some((ArithOp::MulLo, w, x, y))
    }

    /// `(k, j)` for the bit test `(= ((_ extract j j) k) #b1)` (either
    /// order).
    fn bit_test(&self, condition: Id) -> Option<(Id, u32)> {
        if *self.op(condition) != Op::Eq {
            return None;
        }
        let (a, b) = (self.arg(condition, 0), self.arg(condition, 1));
        let (extract, one) = if *self.op(b) == Op::Const(1, 1) {
            (a, b)
        } else {
            (b, a)
        };
        if *self.op(one) != Op::Const(1, 1) {
            return None;
        }
        match self.op(extract) {
            Op::Extract(high, low) if high == low => Some((self.arg(extract, 0), *low)),
            _ => None,
        }
    }

    /// One stage of [`super::shift_modulo_width`]'s barrel at `node`: `(ite
    /// (= ((_ extract j j) k) #b1) t e)` with `t` the shift of `e` by `2^j`
    /// (left: `(concat ((_ extract w-1-2^j 0) e) 0)`; logical right: `(concat
    /// 0 ((_ extract w-1 2^j) e))` or its zero extension; arithmetic right:
    /// the sign extension), or both arms constants that one shift relates
    /// (a stage over a constant, folded). Its kinds, `j`, `k` and `e`.
    fn barrel_stage(&self, node: Id) -> Option<(ShiftKinds, u32, Id, Id)> {
        if *self.op(node) != Op::Ite {
            return None;
        }
        let (condition, t, e) = (self.arg(node, 0), self.arg(node, 1), self.arg(node, 2));
        let w = self.width(node);
        let (k, j) = self.bit_test(condition)?;
        let by = 1u32.checked_shl(j).filter(|by| *by < w)?;
        let is_extract = |id: Id, high: u32, low: u32| {
            *self.op(id) == Op::Extract(high, low) && self.arg(id, 0) == e
        };
        let is_zero = |id: Id, width: u32| *self.op(id) == Op::Const(0, width);
        let kinds = match self.op(t) {
            Op::ZeroExtend(extra) if *extra == by && is_extract(self.arg(t, 0), w - 1, by) => LSHR,
            Op::SignExtend(extra) if *extra == by && is_extract(self.arg(t, 0), w - 1, by) => ASHR,
            Op::Concat => {
                let (high, low) = (self.arg(t, 0), self.arg(t, 1));
                if is_zero(high, by) && is_extract(low, w - 1, by) {
                    LSHR
                } else if is_zero(low, by) && is_extract(high, w - 1 - by, 0) {
                    SHL
                } else {
                    return None;
                }
            }
            Op::Const(shifted, _) if w <= 64 => {
                let Op::Const(value, _) = self.op(e) else {
                    return None;
                };
                let mask = if w == 64 { u64::MAX } else { (1u64 << w) - 1 };
                let signed = ((*value << (64 - w)) as i64 >> (64 - w)) as u64;
                let mut kinds = 0;
                if *shifted == (value << by) & mask {
                    kinds |= SHL;
                }
                if *shifted == value >> by {
                    kinds |= LSHR;
                }
                if *shifted == ((signed as i64) >> by) as u64 & mask {
                    kinds |= ASHR;
                }
                if kinds == 0 {
                    return None;
                }
                kinds
            }
            _ => return None,
        };
        Some((kinds, j, k, e))
    }

    /// The kind of [`super::shift_modulo_width`]'s barrel at `node`, when it
    /// is one: at least two stages over one amount term `k`, the stage bits
    /// strictly decreasing inward (a stage the spelling folded away, as an
    /// amount bit known zero, may be missing), one kind of shift.
    fn barrel(&self, node: Id) -> Option<ArithOp> {
        let w = self.width(node);
        if !w.is_power_of_two() || w < 2 {
            return None;
        }
        let (mut current, mut kinds, mut amount, mut above, mut stages) =
            (node, SHL | LSHR | ASHR, None, w.trailing_zeros(), 0usize);
        while let Some((stage_kinds, j, k, inner)) = self.barrel_stage(current) {
            if j >= above || amount.is_some_and(|amount| amount != k) || stage_kinds & kinds == 0 {
                break;
            }
            kinds &= stage_kinds;
            amount = Some(k);
            above = j;
            stages += 1;
            current = inner;
        }
        if stages < 2 {
            return None;
        }
        match kinds {
            SHL => Some(ArithOp::Shl),
            LSHR => Some(ArithOp::Lshr),
            ASHR => Some(ArithOp::Ashr),
            _ => None,
        }
    }

    /// Whether `node` is an ARITHMETIC NODE (OD-206): a product of two terms
    /// neither of which is a constant by value, a quotient or remainder
    /// (`bvudiv`, `bvurem`, `bvsdiv`) by a divisor that is no constant by
    /// value, or a variable shift's barrel ([`Self::barrel`]).
    fn is_arith_node(
        &mut self,
        node: Id,
        constants: &HashSet<String>,
        memo: &mut HashMap<Id, bool>,
    ) -> bool {
        match self.op(node) {
            Op::BvMul => {
                let (x, y) = (self.arg(node, 0), self.arg(node, 1));
                !self.closed_id(x, constants, memo) && !self.closed_id(y, constants, memo)
            }
            Op::BvUDiv | Op::BvURem | Op::BvSDiv => {
                let divisor = self.arg(node, 1);
                !self.closed_id(divisor, constants, memo)
            }
            Op::Ite => self.barrel(node).is_some(),
            _ => false,
        }
    }

    /// `comm` ([`generalized`], step 1): a product of two non-constant terms
    /// with its operands ordered by their structural keys.
    fn commuted(
        &mut self,
        node: Id,
        constants: &HashSet<String>,
        memo: &mut HashMap<Id, bool>,
    ) -> Option<Id> {
        if *self.op(node) != Op::BvMul || !self.is_arith_node(node, constants, memo) {
            return None;
        }
        let (x, y) = (self.arg(node, 0), self.arg(node, 1));
        (self.operand_order(x) > self.operand_order(y)).then(|| self.mk(Op::BvMul, vec![y, x]))
    }

    /// The order `comm` sorts a product's operands by: the structural key.
    fn operand_order(&mut self, id: Id) -> u128 {
        self.structural_key(id)
    }

    /// The unordered operand pair of a widening product, in `comm`'s order.
    fn operand_pair(&mut self, a: Id, b: Id) -> (Id, Id) {
        if self.operand_order(a) > self.operand_order(b) {
            (b, a)
        } else {
            (a, b)
        }
    }

    /// The order the leaves are numbered in: each arithmetic node's first
    /// occurrence ([`generalized`], step 3).
    fn leaf_order(&self, first_occurrence: Vec<Id>) -> Vec<Id> {
        first_occurrence
    }

    /// [`generalized`] over the table: `definitions` (in order) and `roots`
    /// (the sides).
    fn generalize(
        &mut self,
        definitions: Vec<(String, Id)>,
        roots: Vec<Id>,
    ) -> Option<Generalized> {
        // A theorem that already names a leaf's free input is not
        // generalized (its leaves would not be fresh).
        let every: Vec<Id> = definitions
            .iter()
            .map(|(_, id)| *id)
            .chain(roots.iter().copied())
            .collect();
        if self
            .topo(&every)
            .into_iter()
            .any(|id| self.var_name(id).is_some_and(is_arith_leaf_name))
            || definitions.iter().any(|(name, _)| is_arith_leaf_name(name))
        {
            return None;
        }
        // The names a constant defines (a constant by value).
        let mut constants: HashSet<String> = HashSet::new();
        let mut closed: HashMap<Id, bool> = HashMap::new();
        for (name, id) in &definitions {
            if self.closed_id(*id, &constants, &mut closed) {
                constants.insert(name.clone());
                // A name now known constant changes what reads it.
                closed.clear();
            }
        }
        closed.clear();
        // Step 1, `comm`.
        let mut commuted: Vec<Id> = Vec::with_capacity(every.len());
        for root in every {
            commuted.push(self.rewrite(root, &mut |terms, node| {
                terms.commuted(node, &constants, &mut closed)
            }));
        }
        // Step 2, `wide`: the widening products present, by width and
        // operand pair (an unsigned one first).
        let mut wides: HashMap<(u32, Id, Id), (ArithOp, Id)> = HashMap::new();
        for id in self.topo(&commuted) {
            if !self.is_arith_node(id, &constants, &mut closed) {
                continue;
            }
            if let Some((op @ (ArithOp::UMulWide | ArithOp::SMulWide), n, a, b)) =
                self.product_key(id)
            {
                let pair = self.operand_pair(a, b);
                let entry = wides.entry((n, pair.0, pair.1)).or_insert((op, id));
                if entry.0 == ArithOp::SMulWide && op == ArithOp::UMulWide {
                    *entry = (op, id);
                }
            }
        }
        let mut widened: Vec<Id> = Vec::with_capacity(commuted.len());
        for root in commuted {
            widened.push(self.rewrite(root, &mut |terms, node| {
                if !terms.is_arith_node(node, &constants, &mut closed) {
                    return None;
                }
                let (ArithOp::MulLo, n, x, y) = terms.product_key(node)? else {
                    return None;
                };
                let (x, y) = terms.operand_pair(x, y);
                let (_, wide) = *wides.get(&(n, x, y))?;
                Some(terms.extract(wide, n - 1, 0))
            }));
        }
        // Step 3, the leaves: the arithmetic nodes in first occurrence
        // (children first, never inside a node a leaf replaces).
        let mut first: Vec<Id> = Vec::new();
        let mut seen: HashSet<Id> = HashSet::new();
        for &root in &widened {
            let mut stack: Vec<(Id, bool)> = vec![(root, false)];
            while let Some((id, ready)) = stack.pop() {
                if ready {
                    continue;
                }
                if !seen.insert(id) {
                    continue;
                }
                if self.is_arith_node(id, &constants, &mut closed) {
                    first.push(id);
                    continue;
                }
                stack.push((id, true));
                for &child in self.args(id).iter().rev() {
                    if !seen.contains(&child) {
                        stack.push((child, false));
                    }
                }
            }
        }
        if first.is_empty() {
            return None;
        }
        let order = self.leaf_order(first);
        let mut leaf_of: HashMap<Id, Id> = HashMap::with_capacity(order.len());
        let mut leaves: Vec<(String, u32)> = Vec::with_capacity(order.len());
        let leaf_nodes = order.clone();
        for (k, node) in order.into_iter().enumerate() {
            let name = arith_leaf_name(k);
            let width = self.width(node);
            leaf_of.insert(node, self.var(&name, width));
            leaves.push((name, width));
        }
        let mut replaced: Vec<Id> = Vec::with_capacity(widened.len());
        let mut memo: HashMap<Id, Id> = HashMap::new();
        for root in widened {
            replaced.push(self.replace_nodes(root, &leaf_of, &mut memo));
        }
        // Step 4: a definition that is a bare leaf is that leaf; then the
        // cone of the sides.
        let (definition_ids, side_ids) = replaced.split_at(definitions.len());
        let mut env: HashMap<String, Id> = HashMap::new();
        let mut kept: Vec<(String, Id)> = Vec::new();
        for ((name, _), &id) in definitions.iter().zip(definition_ids) {
            let id = self.substitute(id, &env);
            if self.var_name(id).is_some_and(is_arith_leaf_name) {
                env.insert(name.clone(), id);
            } else {
                kept.push((name.clone(), id));
            }
        }
        let sides: Vec<Id> = side_ids
            .iter()
            .map(|&side| self.substitute(side, &env))
            .collect();
        let rhs_of: HashMap<&str, Id> =
            kept.iter().map(|(name, id)| (name.as_str(), *id)).collect();
        let mut reached: HashSet<String> = HashSet::new();
        let mut pending: Vec<Id> = sides.clone();
        while let Some(root) = pending.pop() {
            for id in self.topo(&[root]) {
                if let Some(name) = self.var_name(id)
                    && let Some(&rhs) = rhs_of.get(name)
                    && reached.insert(name.to_owned())
                {
                    pending.push(rhs);
                }
            }
        }
        kept.retain(|(name, _)| reached.contains(name));
        let used: HashSet<String> = self
            .topo(
                &kept
                    .iter()
                    .map(|(_, id)| *id)
                    .chain(sides.iter().copied())
                    .collect::<Vec<_>>(),
            )
            .into_iter()
            .filter_map(|id| self.var_name(id).map(str::to_owned))
            .collect();
        // The leaves the generalization still reads, renumbered from 0 in
        // their order (a leaf only a dropped definition read leaves no gap).
        let live: Vec<(Id, u32)> = leaves
            .iter()
            .filter(|(name, _)| used.contains(name))
            .map(|(name, width)| (self.var(name, *width), *width))
            .collect();
        let live_nodes: Vec<Id> = leaves
            .iter()
            .zip(&leaf_nodes)
            .filter(|((name, _), _)| used.contains(name))
            .map(|(_, node)| *node)
            .collect();
        let mut renamed: HashMap<String, Id> = HashMap::new();
        leaves = Vec::with_capacity(live.len());
        for (k, (leaf, width)) in live.into_iter().enumerate() {
            let name = arith_leaf_name(k);
            let old = self.var_name(leaf).expect("a leaf").to_owned();
            if old != name {
                renamed.insert(old, self.var(&name, width));
            }
            leaves.push((name, width));
        }
        let kept: Vec<(String, Id)> = kept
            .into_iter()
            .map(|(name, id)| (name, self.substitute(id, &renamed)))
            .collect();
        let sides: Vec<Id> = sides
            .into_iter()
            .map(|side| self.substitute(side, &renamed))
            .collect();
        let mut exported_definitions = Vec::with_capacity(kept.len());
        for (name, id) in &kept {
            exported_definitions.push((name.clone(), self.export(*id)?));
        }
        let mut exported_sides = Vec::with_capacity(sides.len());
        for side in sides {
            exported_sides.push(self.export(side)?);
        }
        let mut nodes = Vec::with_capacity(live_nodes.len());
        for node in live_nodes {
            nodes.push(self.export(node)?);
        }
        Some(Generalized {
            definitions: exported_definitions,
            sides: exported_sides,
            leaves,
            nodes,
        })
    }

    /// `root` with every node of `leaf_of` replaced by its leaf, never
    /// looking inside a replaced node (`memo` is shared across roots).
    fn replace_nodes(
        &mut self,
        root: Id,
        leaf_of: &HashMap<Id, Id>,
        memo: &mut HashMap<Id, Id>,
    ) -> Id {
        let mut stack: Vec<(Id, bool)> = vec![(root, false)];
        while let Some((id, ready)) = stack.pop() {
            if memo.contains_key(&id) {
                continue;
            }
            if let Some(&leaf) = leaf_of.get(&id) {
                memo.insert(id, leaf);
                continue;
            }
            if !ready {
                stack.push((id, true));
                for &child in self.args(id).iter().rev() {
                    if !memo.contains_key(&child) {
                        stack.push((child, false));
                    }
                }
                continue;
            }
            let (op, args) = self.nodes[id as usize].clone();
            let mapped: Vec<Id> = args.iter().map(|arg| memo[arg]).collect();
            let node = if mapped == args {
                id
            } else {
                self.mk(op, mapped)
            };
            memo.insert(id, node);
        }
        memo[&root]
    }
}

/// Tests only: `expr`'s arithmetic generalization's single side, in a table
/// that has first imported `first` (OD-206's `comm` and leaf numbering must
/// not depend on what the table created before).
#[cfg(test)]
pub(super) fn generalized_after(
    first: &E,
    definitions: &[(String, E)],
    expr: &E,
) -> Option<Generalized> {
    let mut terms = Terms::new(Groups::NONE);
    terms.import(first)?;
    let mut imported: Vec<(String, Id)> = Vec::with_capacity(definitions.len());
    for (name, rhs) in definitions {
        imported.push((name.clone(), terms.import(rhs)?));
    }
    let root = terms.import(expr)?;
    terms.generalize(imported, vec![root])
}

/// Tests only: `expr` with `comm` applied in a table that has first imported
/// `first`: the product's operand order depends on structure alone.
#[cfg(test)]
pub(super) fn commuted_after(first: &E, expr: &E) -> Option<E> {
    let mut terms = Terms::new(Groups::NONE);
    terms.import(first)?;
    let root = terms.import(expr)?;
    let constants = HashSet::new();
    let mut closed = HashMap::new();
    let commuted = terms.rewrite(root, &mut |terms, node| {
        terms.commuted(node, &constants, &mut closed)
    });
    terms.export(commuted)
}

/// Tests only: whether `expr` is one arithmetic node (OD-206's key nodes),
/// with no named constant.
#[cfg(test)]
pub(super) fn is_arithmetic_node(expr: &E) -> Option<bool> {
    let mut terms = Terms::new(Groups::NONE);
    let root = terms.import(expr)?;
    let constants = HashSet::new();
    let mut closed = HashMap::new();
    Some(terms.is_arith_node(root, &constants, &mut closed))
}
