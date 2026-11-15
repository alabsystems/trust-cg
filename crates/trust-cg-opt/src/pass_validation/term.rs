// trust-cg-opt - Per-pass translation validation: symbolic terms
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Hash-consed symbolic terms with a small set of sound normalizations.
//!
//! Two machine computations are judged equal when their normalized terms are
//! the SAME [`TermId`]. Equality of ids is therefore the only verdict this
//! module produces; distinct ids mean "not shown equal", never "different".
//!
//! Every rewrite applied by the smart constructors is an identity of
//! fixed-width two's-complement arithmetic (or of the memory model in
//! [`TermArena::load`] / [`TermArena::store`]). Each rule states its side
//! condition next to its code, and `tests.rs` checks the constructors
//! against a concrete evaluator ([`TermArena::eval`]) on random inputs.
//!
//! # Value model
//!
//! A register value is a bit-vector of at most 128 bits held as a term. A
//! `width`-bit operation reads the low `width` bits of its arguments and
//! produces a value whose bits above `width` are zero (the AArch64 W-register
//! write rule). [`TermArena::clean`] tracks which terms are already known to
//! have zero high bits, so the zero-extension `Zext` can be dropped when it is
//! an identity.

use std::fmt;

use crate::fast_hash::FxHashMap as HashMap;

/// Identifier of an interned term. Equal ids mean equal terms.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct TermId(u32);

impl fmt::Debug for TermId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "t{}", self.0)
    }
}

/// A storage location whose value at a sync-point entry is a symbol.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub(crate) enum Loc {
    /// Virtual register, keyed by id (the class is a width view).
    VReg(u32),
    /// General-purpose register `n` (X/W views).
    Gpr(u8),
    /// SIMD/FP register `n` (Q/D/S/H/B views).
    Fpr(u8),
    /// The stack pointer.
    Sp,
    /// The NZCV condition flags.
    Flags,
    /// A system register other than NZCV (FPCR, FPSR), by encoding.
    Sys(u16),
    /// Memory plus every other observable effect, threaded as one token.
    World,
}

/// Leaves of the term language.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Atom {
    /// The value of `loc` on entry to sync block `block` (both functions
    /// agree on it by the induction the region checker maintains). `fpr`
    /// records the register bank it was read through, so a general-purpose
    /// read and a SIMD/FP read of one id never share a leaf.
    Input { block: u32, loc: Loc, fpr: bool },
    /// Address of a fixed stack slot.
    Slot(u32),
    /// Frame-index address.
    FrameIndex(i32),
    /// Incoming stack-argument address.
    IncomingArg(i64),
    /// Address of a named symbol (`exact` distinguishes a retained module
    /// function name from an interposable symbol).
    Symbol { name: String, exact: bool },
}

/// Interpreted operations other than the linear ones.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Prim {
    And,
    Or,
    Xor,
    /// Bitwise NOT within the operation width.
    Not,
    /// Logical shift right by a constant amount (`args[1]` is a constant).
    Lshr,
    /// Arithmetic shift right by a constant amount.
    Ashr,
    /// Rotate right by a constant amount.
    Ror,
    /// Variable shifts: the amount register is taken modulo the width.
    Lslv,
    Lsrv,
    Asrv,
    /// Product of two non-constant operands (a constant factor is linear).
    Mul,
    /// Unsigned / signed division; division by zero yields zero (AArch64).
    Udiv,
    Sdiv,
    /// High 64 bits of the 128-bit unsigned / signed product.
    Umulh,
    Smulh,
    /// Keep the low `bits` bits (`args[1]` is the constant bit count).
    Zext,
    /// Sign-extend from the low `bits` bits to the operation width.
    Sext,
}

/// Boolean comparison kinds.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Cmp {
    Eq,
    /// Unsigned less-than.
    Ult,
    /// Signed less-than.
    Slt,
}

/// NZCV producers that conditions can be derived from.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum FlagKind {
    /// `SUBS a, b` / `CMP a, b`.
    Sub,
    /// `ADDS a, b` / `CMN a, b`.
    Add,
    /// `ANDS a, b` / `TST a, b`.
    And,
}

/// How a load's bytes become the register value.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum LoadExt {
    /// Zero-extend the loaded bytes.
    Zero,
    /// Sign-extend to 32 bits (then zero the high half).
    Sign32,
    /// Sign-extend to 64 bits.
    Sign64,
}

/// Non-register operand data that identifies an uninterpreted operation.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Aux {
    Imm(i64),
    FImm(u64),
    Block(u32),
    JumpTable(u32),
    MemOffset(i64),
    /// The operand position of a register operand (so `f(a, b)` and
    /// `f(b, a)` stay distinct when a register is absent from one side).
    Reg(u8),
    /// Width/class code of a defined register.
    Class(u8),
    /// Implicit physical-register use or def list, by encoding.
    Implicit(Vec<u16>),
    /// Instruction flag bits that change behavior.
    Flags(u16),
}

/// An interned term.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Term {
    /// A constant (at most 64 significant bits; higher bits are zero).
    Const(u64),
    /// Boolean constant.
    Bool(bool),
    Atom(Atom),
    /// `constant + sum(coeff * atom)` modulo `2^width`, zero-extended.
    /// Atoms are sorted by id with non-zero coefficients; at least one atom.
    Lin {
        width: u8,
        constant: u64,
        atoms: Vec<(TermId, u64)>,
    },
    Op {
        op: Prim,
        width: u8,
        args: Vec<TermId>,
    },
    /// Boolean comparison of the low `width` bits.
    Cmp {
        cmp: Cmp,
        width: u8,
        a: TermId,
        b: TermId,
    },
    /// Boolean negation.
    BoolNot(TermId),
    /// A condition code applied to flags it could not be resolved against.
    CondRaw {
        cc: u8,
        flags: TermId,
    },
    /// NZCV produced by a modeled flag setter.
    Flags {
        kind: FlagKind,
        width: u8,
        a: TermId,
        b: TermId,
    },
    Ite {
        cond: TermId,
        then: TermId,
        els: TermId,
    },
    /// A deterministic operation without an interpretation, keyed by its
    /// opcode, auxiliary operands and register inputs; `out` selects one
    /// of its results.
    Opaque {
        opcode: u16,
        aux: Vec<Aux>,
        args: Vec<TermId>,
        out: u16,
    },
    /// Value read from `world` at `addr` (`bytes` wide).
    Load {
        world: TermId,
        addr: TermId,
        bytes: u8,
        ext: LoadExt,
        width: u8,
    },
    /// World after storing the low `bytes` of `value` at `addr`.
    Store {
        world: TermId,
        addr: TermId,
        value: TermId,
        bytes: u8,
    },
    /// World after an observable effect (call, trap, volatile access,
    /// unmodeled memory operation).
    Effect {
        world: TermId,
        opcode: u16,
        aux: Vec<Aux>,
        args: Vec<TermId>,
    },
    /// The `slot`th register result of an effect.
    EffectOut {
        effect: TermId,
        slot: u16,
    },
    /// Undefined: a path that does not reach the merge target.
    Bottom,
}

fn mask(width: u8) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

fn sext_from(value: u64, bits: u8) -> u64 {
    if bits == 0 {
        return 0;
    }
    if bits >= 64 {
        return value;
    }
    let shift = 64 - u32::from(bits);
    (((value << shift) as i64) >> shift) as u64
}

/// Interning arena shared by the before and after evaluation of one check.
pub(crate) struct TermArena {
    terms: Vec<Term>,
    /// Bit width above which the term is known to be zero (`None`: unknown).
    clean: Vec<Option<u8>>,
    index: HashMap<Term, TermId>,
    /// Interned ids of a few constants the constructors use constantly.
    true_id: TermId,
    false_id: TermId,
    bottom_id: TermId,
}

impl Default for TermArena {
    fn default() -> Self {
        Self::new()
    }
}

impl TermArena {
    pub(crate) fn new() -> Self {
        let mut arena = Self {
            terms: Vec::new(),
            clean: Vec::new(),
            index: HashMap::default(),
            true_id: TermId(0),
            false_id: TermId(0),
            bottom_id: TermId(0),
        };
        arena.true_id = arena.intern(Term::Bool(true), Some(1));
        arena.false_id = arena.intern(Term::Bool(false), Some(1));
        arena.bottom_id = arena.intern(Term::Bottom, None);
        arena
    }

    fn intern(&mut self, term: Term, clean: Option<u8>) -> TermId {
        if let Some(&id) = self.index.get(&term) {
            return id;
        }
        let id = TermId(self.terms.len() as u32);
        self.terms.push(term.clone());
        self.clean.push(clean);
        self.index.insert(term, id);
        id
    }

    pub(crate) fn get(&self, id: TermId) -> &Term {
        &self.terms[id.0 as usize]
    }

    /// Whether every bit of `id` at or above `width` is known to be zero.
    pub(crate) fn clean(&self, id: TermId, width: u8) -> bool {
        self.clean[id.0 as usize].is_some_and(|w| w <= width)
    }

    pub(crate) fn tru(&self) -> TermId {
        self.true_id
    }

    pub(crate) fn fals(&self) -> TermId {
        self.false_id
    }

    pub(crate) fn bottom(&self) -> TermId {
        self.bottom_id
    }

    pub(crate) fn as_const(&self, id: TermId) -> Option<u64> {
        match self.get(id) {
            Term::Const(v) => Some(*v),
            _ => None,
        }
    }

    pub(crate) fn as_bool(&self, id: TermId) -> Option<bool> {
        match self.get(id) {
            Term::Bool(b) => Some(*b),
            _ => None,
        }
    }

    pub(crate) fn konst(&mut self, value: u64) -> TermId {
        let bits = 64 - value.leading_zeros() as u8;
        self.intern(Term::Const(value), Some(bits))
    }

    pub(crate) fn boolean(&mut self, value: bool) -> TermId {
        if value { self.true_id } else { self.false_id }
    }

    /// Intern a leaf. `clean` is the width its value is known to fit in
    /// (64 for a general-purpose register or an address); it must be the
    /// same every time the same atom is built, which holds because the
    /// atom's key determines its register bank.
    pub(crate) fn atom(&mut self, atom: Atom, clean: Option<u8>) -> TermId {
        self.intern(Term::Atom(atom), clean)
    }

    /// Zero-extend the low `bits` bits of `x`.
    pub(crate) fn zext(&mut self, x: TermId, bits: u8) -> TermId {
        if bits >= 128 || self.clean(x, bits) {
            return x;
        }
        if let Some(c) = self.as_const(x) {
            return self.konst(c & mask(bits));
        }
        // Zext(Zext(y, j), k) = Zext(y, min(j, k)).
        if let Term::Op {
            op: Prim::Zext,
            args,
            ..
        } = self.get(x).clone()
            && let Some(inner) = self.as_const(args[1])
        {
            let j = inner as u8;
            return self.zext(args[0], j.min(bits));
        }
        let b = self.konst(u64::from(bits));
        self.intern(
            Term::Op {
                op: Prim::Zext,
                width: 128,
                args: vec![x, b],
            },
            Some(bits),
        )
    }

    /// Decompose a value into `constant + sum(coeff * atom)` at `width`.
    fn linear_parts(&mut self, x: TermId, width: u8) -> (u64, Vec<(TermId, u64)>) {
        let m = mask(width);
        match self.get(x).clone() {
            Term::Const(c) => (c & m, Vec::new()),
            // A narrower linear form is only reusable at its own width or a
            // narrower one: its value is zero-extended above its width.
            Term::Lin {
                width: w,
                constant,
                atoms,
            } if w >= width => (
                constant & m,
                atoms.into_iter().map(|(a, c)| (a, c & m)).collect(),
            ),
            // Zext(y, k) agrees with y in the low k >= width bits.
            Term::Op {
                op: Prim::Zext,
                args,
                ..
            } if self
                .as_const(args[1])
                .is_some_and(|k| k >= u64::from(width)) =>
            {
                self.linear_parts(args[0], width)
            }
            _ => (0, vec![(x, 1)]),
        }
    }

    /// Build the canonical linear term `constant + sum(coeff * atom)`.
    fn make_lin(&mut self, width: u8, constant: u64, mut atoms: Vec<(TermId, u64)>) -> TermId {
        let m = mask(width);
        atoms.sort_by_key(|(a, _)| *a);
        let mut merged: Vec<(TermId, u64)> = Vec::with_capacity(atoms.len());
        for (a, c) in atoms {
            match merged.last_mut() {
                Some((last, lc)) if *last == a => *lc = lc.wrapping_add(c) & m,
                _ => merged.push((a, c & m)),
            }
        }
        merged.retain(|(_, c)| *c != 0);
        let constant = constant & m;
        if merged.is_empty() {
            return self.konst(constant);
        }
        // `1 * a + 0` is `a` itself when `a` already fits the width.
        if constant == 0 && merged.len() == 1 && merged[0].1 == 1 && self.clean(merged[0].0, width)
        {
            return merged[0].0;
        }
        self.intern(
            Term::Lin {
                width,
                constant,
                atoms: merged,
            },
            Some(width),
        )
    }

    pub(crate) fn add(&mut self, width: u8, a: TermId, b: TermId) -> TermId {
        let (ca, mut la) = self.linear_parts(a, width);
        let (cb, lb) = self.linear_parts(b, width);
        la.extend(lb);
        self.make_lin(width, ca.wrapping_add(cb), la)
    }

    pub(crate) fn sub(&mut self, width: u8, a: TermId, b: TermId) -> TermId {
        let (ca, mut la) = self.linear_parts(a, width);
        let (cb, lb) = self.linear_parts(b, width);
        la.extend(lb.into_iter().map(|(t, c)| (t, c.wrapping_neg())));
        self.make_lin(width, ca.wrapping_sub(cb), la)
    }

    pub(crate) fn add_const(&mut self, width: u8, a: TermId, k: u64) -> TermId {
        let k = self.konst(k & mask(width));
        self.add(width, a, k)
    }

    pub(crate) fn neg(&mut self, width: u8, a: TermId) -> TermId {
        let zero = self.konst(0);
        self.sub(width, zero, a)
    }

    /// Multiply; a constant factor keeps the result linear.
    pub(crate) fn mul(&mut self, width: u8, a: TermId, b: TermId) -> TermId {
        let (a, b) = if self.as_const(a).is_some() {
            (b, a)
        } else {
            (a, b)
        };
        if let Some(k) = self.as_const(b) {
            let (c, atoms) = self.linear_parts(a, width);
            let atoms = atoms
                .into_iter()
                .map(|(t, coeff)| (t, coeff.wrapping_mul(k)))
                .collect();
            return self.make_lin(width, c.wrapping_mul(k), atoms);
        }
        self.op_commutative(Prim::Mul, width, a, b)
    }

    /// Shift left by a constant amount (`amount < width`).
    pub(crate) fn shl(&mut self, width: u8, a: TermId, amount: u32) -> TermId {
        debug_assert!(amount < u32::from(width));
        let factor = self.konst(1u64 << amount);
        self.mul(width, a, factor)
    }

    fn op_commutative(&mut self, op: Prim, width: u8, a: TermId, b: TermId) -> TermId {
        let (a, b) = if a <= b { (a, b) } else { (b, a) };
        self.intern(
            Term::Op {
                op,
                width,
                args: vec![a, b],
            },
            Some(width),
        )
    }

    pub(crate) fn and(&mut self, width: u8, a: TermId, b: TermId) -> TermId {
        let m = mask(width);
        let (a, b) = if self.as_const(a).is_some() {
            (b, a)
        } else {
            (a, b)
        };
        match (self.as_const(a), self.as_const(b)) {
            (Some(x), Some(y)) => return self.konst(x & y & m),
            (None, Some(k)) => {
                let k = k & m;
                if k == 0 {
                    return self.konst(0);
                }
                // `a & (2^n - 1)` keeps the low n bits.
                if (k & k.wrapping_add(1)) == 0 {
                    let bits = k.count_ones() as u8;
                    return self.zext(a, bits.min(width));
                }
            }
            _ => {}
        }
        if a == b {
            return self.zext(a, width);
        }
        self.op_commutative(Prim::And, width, a, b)
    }

    pub(crate) fn or(&mut self, width: u8, a: TermId, b: TermId) -> TermId {
        let m = mask(width);
        let (a, b) = if self.as_const(a).is_some() {
            (b, a)
        } else {
            (a, b)
        };
        match (self.as_const(a), self.as_const(b)) {
            (Some(x), Some(y)) => return self.konst((x | y) & m),
            (None, Some(0)) => return self.zext(a, width),
            _ => {}
        }
        if a == b {
            return self.zext(a, width);
        }
        self.op_commutative(Prim::Or, width, a, b)
    }

    pub(crate) fn xor(&mut self, width: u8, a: TermId, b: TermId) -> TermId {
        let m = mask(width);
        let (a, b) = if self.as_const(a).is_some() {
            (b, a)
        } else {
            (a, b)
        };
        match (self.as_const(a), self.as_const(b)) {
            (Some(x), Some(y)) => return self.konst((x ^ y) & m),
            (None, Some(0)) => return self.zext(a, width),
            _ => {}
        }
        if a == b {
            return self.konst(0);
        }
        self.op_commutative(Prim::Xor, width, a, b)
    }

    pub(crate) fn not(&mut self, width: u8, a: TermId) -> TermId {
        if let Some(x) = self.as_const(a) {
            return self.konst(!x & mask(width));
        }
        self.intern(
            Term::Op {
                op: Prim::Not,
                width,
                args: vec![a],
            },
            Some(width),
        )
    }

    /// Shift or rotate by a constant amount in `0..width`.
    pub(crate) fn shift_const(&mut self, op: Prim, width: u8, a: TermId, amount: u32) -> TermId {
        debug_assert!(matches!(op, Prim::Lshr | Prim::Ashr | Prim::Ror));
        if amount == 0 {
            return self.zext(a, width);
        }
        if let Some(x) = self.as_const(a) {
            let x = x & mask(width);
            let w = u32::from(width);
            let v = match op {
                Prim::Lshr => x >> amount,
                Prim::Ashr => ((sext_from(x, width) as i64) >> amount) as u64,
                _ => (x >> amount) | (x << (w - amount)),
            };
            return self.konst(v & mask(width));
        }
        let k = self.konst(u64::from(amount));
        self.intern(
            Term::Op {
                op,
                width,
                args: vec![a, k],
            },
            Some(width),
        )
    }

    /// Sign-extend the low `bits` bits of `a` to `width` bits.
    pub(crate) fn sext(&mut self, width: u8, a: TermId, bits: u8) -> TermId {
        if bits >= width {
            return self.zext(a, width);
        }
        if let Some(x) = self.as_const(a) {
            return self.konst(sext_from(x, bits) & mask(width));
        }
        let b = self.konst(u64::from(bits));
        self.intern(
            Term::Op {
                op: Prim::Sext,
                width,
                args: vec![a, b],
            },
            Some(width),
        )
    }

    /// A non-commutative interpreted binary operation without folding
    /// beyond constants.
    pub(crate) fn binop(&mut self, op: Prim, width: u8, a: TermId, b: TermId) -> TermId {
        if let (Some(x), Some(y)) = (self.as_const(a), self.as_const(b)) {
            let m = mask(width);
            let w = u32::from(width);
            let (x, y) = (x & m, y & m);
            let amount = (y % u64::from(w)) as u32;
            let folded = match op {
                Prim::Lslv => Some(if amount == 0 { x } else { x << amount }),
                Prim::Lsrv => Some(if amount == 0 { x } else { x >> amount }),
                Prim::Asrv => Some(((sext_from(x, width) as i64) >> amount) as u64),
                Prim::Udiv => Some(x.checked_div(y).unwrap_or(0)),
                Prim::Sdiv => Some(if y == 0 {
                    0
                } else {
                    let (sx, sy) = (sext_from(x, width) as i64, sext_from(y, width) as i64);
                    if width == 64 {
                        sx.wrapping_div(sy) as u64
                    } else {
                        (sx / sy) as u64
                    }
                }),
                Prim::Umulh if width == 64 => Some(((u128::from(x) * u128::from(y)) >> 64) as u64),
                Prim::Smulh if width == 64 => {
                    Some(((i128::from(x as i64) * i128::from(y as i64)) >> 64) as u64)
                }
                _ => None,
            };
            if let Some(v) = folded {
                return self.konst(v & m);
            }
        }
        self.intern(
            Term::Op {
                op,
                width,
                args: vec![a, b],
            },
            Some(width),
        )
    }

    pub(crate) fn cmp(&mut self, cmp: Cmp, width: u8, a: TermId, b: TermId) -> TermId {
        let a = self.zext(a, width);
        let b = self.zext(b, width);
        if let (Some(x), Some(y)) = (self.as_const(a), self.as_const(b)) {
            let v = match cmp {
                Cmp::Eq => x == y,
                Cmp::Ult => x < y,
                Cmp::Slt => (sext_from(x, width) as i64) < (sext_from(y, width) as i64),
            };
            return self.boolean(v);
        }
        if a == b {
            return self.boolean(cmp == Cmp::Eq);
        }
        let (a, b) = if cmp == Cmp::Eq && b < a {
            (b, a)
        } else {
            (a, b)
        };
        self.intern(Term::Cmp { cmp, width, a, b }, Some(1))
    }

    pub(crate) fn bool_not(&mut self, c: TermId) -> TermId {
        match self.get(c) {
            Term::Bool(b) => {
                let b = !*b;
                self.boolean(b)
            }
            Term::BoolNot(inner) => *inner,
            _ => self.intern(Term::BoolNot(c), Some(1)),
        }
    }

    pub(crate) fn ite(&mut self, cond: TermId, then: TermId, els: TermId) -> TermId {
        if then == els {
            return then;
        }
        match self.get(cond) {
            Term::Bool(true) => return then,
            Term::Bool(false) => return els,
            Term::BoolNot(inner) => {
                let inner = *inner;
                return self.ite(inner, els, then);
            }
            _ => {}
        }
        // A boolean ITE between the two constants is the condition itself.
        if then == self.true_id && els == self.false_id {
            return cond;
        }
        if then == self.false_id && els == self.true_id {
            return self.bool_not(cond);
        }
        // ite(c, ite(c, a, b), d) = ite(c, a, d); ite(c, a, ite(c, b, d)) = ite(c, a, d).
        if let Term::Ite {
            cond: c2, then: a, ..
        } = self.get(then)
            && *c2 == cond
        {
            let a = *a;
            return self.ite(cond, a, els);
        }
        if let Term::Ite {
            cond: c2, els: d, ..
        } = self.get(els)
            && *c2 == cond
        {
            let d = *d;
            return self.ite(cond, then, d);
        }
        // AArch64 division by zero yields zero (UDIV/SDIV, ARM ARM C6.2.371 /
        // C6.2.254): `ite(x == 0, 0, div(a, x)) = div(a, x)` when the
        // comparison and the division read the same low bits of `x`.
        if self.as_const(then) == Some(0)
            && let Term::Cmp {
                cmp: Cmp::Eq,
                width,
                a: ca,
                b: cb,
            } = self.get(cond).clone()
            && let Term::Op {
                op: Prim::Udiv | Prim::Sdiv,
                width: dw,
                args,
            } = self.get(els).clone()
            && dw == width
        {
            let tested = if self.as_const(ca) == Some(0) {
                Some(cb)
            } else if self.as_const(cb) == Some(0) {
                Some(ca)
            } else {
                None
            };
            if let Some(x) = tested {
                let divisor = self.zext(args[1], width);
                let x = self.zext(x, width);
                if divisor == x {
                    return els;
                }
            }
        }
        let clean = match (self.clean[then.0 as usize], self.clean[els.0 as usize]) {
            (Some(x), Some(y)) => Some(x.max(y)),
            _ => None,
        };
        self.intern(Term::Ite { cond, then, els }, clean)
    }

    pub(crate) fn flags(&mut self, kind: FlagKind, width: u8, a: TermId, b: TermId) -> TermId {
        let a = self.zext(a, width);
        let b = self.zext(b, width);
        self.intern(Term::Flags { kind, width, a, b }, None)
    }

    /// The boolean a condition code (`0..=15`, AArch64 encoding) selects
    /// from `flags`.
    pub(crate) fn cond(&mut self, cc: u8, flags: TermId) -> TermId {
        // AL / NV always hold.
        if cc >= 14 {
            return self.true_id;
        }
        // Odd codes are the negation of the even code below them.
        if cc & 1 == 1 {
            let base = self.cond(cc & !1, flags);
            return self.bool_not(base);
        }
        if let Term::Flags { kind, width, a, b } = self.get(flags).clone() {
            match (kind, cc) {
                // EQ: Z
                (FlagKind::Sub, 0) => return self.cmp(Cmp::Eq, width, a, b),
                (FlagKind::Add, 0) => {
                    let sum = self.add(width, a, b);
                    let zero = self.konst(0);
                    return self.cmp(Cmp::Eq, width, sum, zero);
                }
                (FlagKind::And, 0) => {
                    let r = self.and(width, a, b);
                    let zero = self.konst(0);
                    return self.cmp(Cmp::Eq, width, r, zero);
                }
                // HS (C set): for SUBS, a >= b unsigned.
                (FlagKind::Sub, 2) => {
                    let lt = self.cmp(Cmp::Ult, width, a, b);
                    return self.bool_not(lt);
                }
                // MI (N set): sign bit of the result.
                (FlagKind::And, 4) => {
                    let r = self.and(width, a, b);
                    let zero = self.konst(0);
                    return self.cmp(Cmp::Slt, width, r, zero);
                }
                // HS / VS: logical flag setters clear C and V.
                (FlagKind::And, 2) | (FlagKind::And, 6) => return self.false_id,
                // HI (C && !Z): for SUBS, a > b unsigned.
                (FlagKind::Sub, 8) => return self.cmp(Cmp::Ult, width, b, a),
                // GE (N == V): for SUBS, a >= b signed.
                (FlagKind::Sub, 10) => {
                    let lt = self.cmp(Cmp::Slt, width, a, b);
                    return self.bool_not(lt);
                }
                // GE for ANDS: V = 0, so N == 0.
                (FlagKind::And, 10) => {
                    let r = self.and(width, a, b);
                    let zero = self.konst(0);
                    let neg = self.cmp(Cmp::Slt, width, r, zero);
                    return self.bool_not(neg);
                }
                // GT (!Z && N == V): for SUBS, a > b signed.
                (FlagKind::Sub, 12) => return self.cmp(Cmp::Slt, width, b, a),
                _ => {}
            }
        }
        self.intern(Term::CondRaw { cc, flags }, Some(1))
    }

    /// An uninterpreted deterministic result. `clean` is the width of the
    /// register it defines (a W or narrower FP write zeroes the rest).
    pub(crate) fn opaque(
        &mut self,
        opcode: u16,
        aux: Vec<Aux>,
        args: Vec<TermId>,
        out: u16,
        clean: Option<u8>,
    ) -> TermId {
        self.intern(
            Term::Opaque {
                opcode,
                aux,
                args,
                out,
            },
            clean,
        )
    }

    pub(crate) fn effect(
        &mut self,
        world: TermId,
        opcode: u16,
        aux: Vec<Aux>,
        args: Vec<TermId>,
    ) -> TermId {
        self.intern(
            Term::Effect {
                world,
                opcode,
                aux,
                args,
            },
            None,
        )
    }

    pub(crate) fn effect_out(&mut self, effect: TermId, slot: u16, clean: Option<u8>) -> TermId {
        self.intern(Term::EffectOut { effect, slot }, clean)
    }

    /// `(constant, atoms)` of an address, for disjointness.
    fn address_parts(&mut self, addr: TermId) -> (u64, Vec<(TermId, u64)>) {
        self.linear_parts(addr, 64)
    }

    /// Whether `[a1, a1+n1)` and `[a2, a2+n2)` are provably disjoint:
    /// the same symbolic base with constant offsets whose byte ranges do
    /// not overlap.
    pub(crate) fn disjoint(&mut self, a1: TermId, n1: u8, a2: TermId, n2: u8) -> bool {
        let (c1, b1) = self.address_parts(a1);
        let (c2, b2) = self.address_parts(a2);
        if b1 != b2 {
            return false;
        }
        // Offsets are compared as a signed 64-bit difference; any distance
        // beyond 2^62 is treated as unknown (never wrapping into "disjoint").
        let delta = c2.wrapping_sub(c1) as i64;
        if !(-(1i64 << 62)..(1i64 << 62)).contains(&delta) {
            return false;
        }
        delta >= i64::from(n1) || -delta >= i64::from(n2)
    }

    /// Whether two addresses are provably the same.
    pub(crate) fn same_address(&mut self, a1: TermId, a2: TermId) -> bool {
        a1 == a2 || self.address_parts(a1) == self.address_parts(a2)
    }

    /// Read `bytes` at `addr` from `world`.
    ///
    /// Store-to-load forwarding: a load of exactly the bytes a store wrote
    /// returns the stored value (extended as the load requires); a load
    /// provably disjoint from a store reads the world before it. Nothing
    /// is looked through an [`Term::Effect`].
    pub(crate) fn load(
        &mut self,
        world: TermId,
        addr: TermId,
        bytes: u8,
        ext: LoadExt,
        width: u8,
    ) -> TermId {
        let mut cur = world;
        // Bounded walk: a long store chain is still sound to stop in.
        for _ in 0..64 {
            let Term::Store {
                world: inner,
                addr: saddr,
                value,
                bytes: sbytes,
            } = self.get(cur).clone()
            else {
                break;
            };
            if sbytes == bytes && self.same_address(saddr, addr) {
                let bits = bytes.saturating_mul(8);
                return match ext {
                    LoadExt::Zero => {
                        let v = self.zext(value, bits);
                        self.zext(v, width)
                    }
                    LoadExt::Sign32 => self.sext(32, value, bits),
                    LoadExt::Sign64 => self.sext(64, value, bits),
                };
            }
            if self.disjoint(saddr, sbytes, addr, bytes) {
                cur = inner;
                continue;
            }
            break;
        }
        let clean = match ext {
            LoadExt::Zero => Some(bytes.saturating_mul(8)),
            LoadExt::Sign32 => Some(32),
            LoadExt::Sign64 => Some(64),
        };
        self.intern(
            Term::Load {
                world: cur,
                addr,
                bytes,
                ext,
                width,
            },
            clean,
        )
    }

    /// Write the low `bytes` of `value` at `addr`.
    ///
    /// A store that exactly overwrites the previous store drops it; two
    /// provably disjoint adjacent stores are put in a canonical order
    /// (they commute).
    pub(crate) fn store(
        &mut self,
        world: TermId,
        addr: TermId,
        value: TermId,
        bytes: u8,
    ) -> TermId {
        let bits = bytes.saturating_mul(8);
        let value = self.zext(value, bits);
        if let Term::Store {
            world: inner,
            addr: paddr,
            value: pvalue,
            bytes: pbytes,
        } = self.get(world).clone()
        {
            if pbytes == bytes && self.same_address(paddr, addr) {
                return self.store(inner, addr, value, bytes);
            }
            if self.disjoint(paddr, pbytes, addr, bytes)
                && self.address_key(addr) < self.address_key(paddr)
            {
                let lower = self.store(inner, addr, value, bytes);
                return self.store(lower, paddr, pvalue, pbytes);
            }
        }
        self.intern(
            Term::Store {
                world,
                addr,
                value,
                bytes,
            },
            None,
        )
    }

    /// Order key of an address for canonical store ordering: its symbolic
    /// base, then its constant offset (signed).
    fn address_key(&mut self, addr: TermId) -> (Vec<(TermId, u64)>, i64) {
        let (c, base) = self.address_parts(addr);
        (base, c as i64)
    }

    /// The terms `id` is built from.
    pub(crate) fn children(&self, id: TermId) -> Vec<TermId> {
        match self.get(id) {
            Term::Const(_) | Term::Bool(_) | Term::Atom(_) | Term::Bottom => Vec::new(),
            Term::Lin { atoms, .. } => atoms.iter().map(|(a, _)| *a).collect(),
            Term::Op { args, .. } | Term::Opaque { args, .. } => args.clone(),
            Term::Cmp { a, b, .. } | Term::Flags { a, b, .. } => vec![*a, *b],
            Term::BoolNot(a) => vec![*a],
            Term::CondRaw { flags, .. } => vec![*flags],
            Term::Ite { cond, then, els } => vec![*cond, *then, *els],
            Term::Load { world, addr, .. } => vec![*world, *addr],
            Term::Store {
                world, addr, value, ..
            } => vec![*world, *addr, *value],
            Term::Effect { world, args, .. } => {
                let mut out = vec![*world];
                out.extend(args.iter().copied());
                out
            }
            Term::EffectOut { effect, .. } => vec![*effect],
        }
    }

    /// Render a term for diagnostics (depth-limited).
    pub(crate) fn render(&self, id: TermId) -> String {
        let mut out = String::new();
        self.render_into(id, 4, &mut out);
        out
    }

    fn render_into(&self, id: TermId, depth: u32, out: &mut String) {
        use std::fmt::Write;
        if depth == 0 {
            let _ = write!(out, "{id:?}");
            return;
        }
        let sub = |s: &Self, t: TermId, out: &mut String| s.render_into(t, depth - 1, out);
        match self.get(id) {
            Term::Const(v) => {
                let _ = write!(out, "{v:#x}");
            }
            Term::Bool(b) => {
                let _ = write!(out, "{b}");
            }
            Term::Atom(a) => {
                let _ = write!(out, "{a:?}");
            }
            Term::Lin {
                width,
                constant,
                atoms,
            } => {
                let _ = write!(out, "lin{width}({constant:#x}");
                for (a, c) in atoms {
                    let _ = write!(out, " + {c:#x}*");
                    sub(self, *a, out);
                }
                out.push(')');
            }
            Term::Op { op, width, args } => {
                let _ = write!(out, "{op:?}{width}(");
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    sub(self, *a, out);
                }
                out.push(')');
            }
            Term::Cmp { cmp, width, a, b } => {
                let _ = write!(out, "{cmp:?}{width}(");
                sub(self, *a, out);
                out.push_str(", ");
                sub(self, *b, out);
                out.push(')');
            }
            Term::BoolNot(a) => {
                out.push('!');
                sub(self, *a, out);
            }
            Term::CondRaw { cc, flags } => {
                let _ = write!(out, "cc{cc}(");
                sub(self, *flags, out);
                out.push(')');
            }
            Term::Flags { kind, width, a, b } => {
                let _ = write!(out, "nzcv.{kind:?}{width}(");
                sub(self, *a, out);
                out.push_str(", ");
                sub(self, *b, out);
                out.push(')');
            }
            Term::Ite { cond, then, els } => {
                out.push_str("ite(");
                sub(self, *cond, out);
                out.push_str(", ");
                sub(self, *then, out);
                out.push_str(", ");
                sub(self, *els, out);
                out.push(')');
            }
            Term::Opaque {
                opcode,
                args,
                out: o,
                ..
            } => {
                let _ = write!(out, "op#{opcode}.{o}(");
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    sub(self, *a, out);
                }
                out.push(')');
            }
            Term::Load {
                world, addr, bytes, ..
            } => {
                let _ = write!(out, "load{bytes}(");
                sub(self, *world, out);
                out.push_str(", ");
                sub(self, *addr, out);
                out.push(')');
            }
            Term::Store {
                world,
                addr,
                value,
                bytes,
            } => {
                let _ = write!(out, "store{bytes}(");
                sub(self, *world, out);
                out.push_str(", ");
                sub(self, *addr, out);
                out.push_str(", ");
                sub(self, *value, out);
                out.push(')');
            }
            Term::Effect {
                world,
                opcode,
                args,
                ..
            } => {
                let _ = write!(out, "effect#{opcode}(");
                sub(self, *world, out);
                for a in args {
                    out.push_str(", ");
                    sub(self, *a, out);
                }
                out.push(')');
            }
            Term::EffectOut { effect, slot } => {
                let _ = write!(out, "out{slot}(");
                sub(self, *effect, out);
                out.push(')');
            }
            Term::Bottom => out.push('⊥'),
        }
    }

    /// Concretely evaluate an integer/boolean term under `env` (atoms and
    /// opaque terms are looked up in `env`; anything else unsupported
    /// returns `None`). Test-only reference semantics for the constructors.
    #[cfg(test)]
    pub(crate) fn eval(&self, id: TermId, env: &dyn Fn(TermId) -> Option<u128>) -> Option<u128> {
        let m128 = |w: u8| -> u128 {
            if w >= 128 {
                u128::MAX
            } else {
                (1u128 << w) - 1
            }
        };
        let sx = |v: u128, bits: u8| -> i128 {
            if bits >= 128 {
                return v as i128;
            }
            let shift = 128 - u32::from(bits);
            ((v << shift) as i128) >> shift
        };
        Some(match self.get(id) {
            Term::Const(v) => u128::from(*v),
            Term::Bool(b) => u128::from(*b),
            Term::Lin {
                width,
                constant,
                atoms,
            } => {
                let mut acc = u128::from(*constant);
                for (a, c) in atoms {
                    acc = acc.wrapping_add(self.eval(*a, env)?.wrapping_mul(u128::from(*c)));
                }
                acc & m128(*width)
            }
            Term::Op { op, width, args } => {
                let w = *width;
                let m = m128(w);
                let x = self.eval(args[0], env)? & m;
                let y = match args.get(1) {
                    Some(a) => self.eval(*a, env)?,
                    None => 0,
                };
                let wu = u32::from(w);
                let r = match op {
                    Prim::And => x & y,
                    Prim::Or => x | y,
                    Prim::Xor => x ^ y,
                    Prim::Not => !x,
                    Prim::Lshr => x >> (y as u32),
                    Prim::Ashr => (sx(x, w) >> (y as u32)) as u128,
                    Prim::Ror => {
                        let k = y as u32 % wu;
                        if k == 0 {
                            x
                        } else {
                            (x >> k) | (x << (wu - k))
                        }
                    }
                    Prim::Lslv => x << ((y & m) as u32 % wu),
                    Prim::Lsrv => x >> ((y & m) as u32 % wu),
                    Prim::Asrv => (sx(x, w) >> ((y & m) as u32 % wu)) as u128,
                    Prim::Mul => x.wrapping_mul(y & m),
                    Prim::Udiv => x.checked_div(y & m).unwrap_or(0),
                    Prim::Sdiv => {
                        let (a, b) = (sx(x, w), sx(y & m, w));
                        if b == 0 { 0 } else { a.wrapping_div(b) as u128 }
                    }
                    Prim::Umulh => (x * (y & m)) >> 64,
                    Prim::Smulh => ((sx(x, 64) * sx(y & m, 64)) >> 64) as u128,
                    Prim::Zext => x & m128(y as u8),
                    Prim::Sext => sx(x, y as u8) as u128,
                };
                r & m
            }
            Term::Cmp { cmp, width, a, b } => {
                let m = m128(*width);
                let x = self.eval(*a, env)? & m;
                let y = self.eval(*b, env)? & m;
                u128::from(match cmp {
                    Cmp::Eq => x == y,
                    Cmp::Ult => x < y,
                    Cmp::Slt => sx(x, *width) < sx(y, *width),
                })
            }
            Term::BoolNot(a) => u128::from(self.eval(*a, env)? == 0),
            Term::Ite { cond, then, els } => {
                if self.eval(*cond, env)? != 0 {
                    self.eval(*then, env)?
                } else {
                    self.eval(*els, env)?
                }
            }
            Term::Atom(_) | Term::Opaque { .. } => env(id)?,
            _ => return None,
        })
    }
}
