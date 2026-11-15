// trust-cg-verify/post_ra_value_flow/term.rs - hash-consed value terms
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Hash-consed value terms shared by the two functions under comparison.
//!
//! Two values are judged equal exactly when their normalized terms are the
//! same [`TermId`]; distinct ids mean "not shown equal". Every rewrite the
//! smart constructors apply is an identity of fixed-width bit-vector
//! arithmetic, stated next to its code:
//!
//! * `trunc(w, t)` keeps the low `w` bits of `t`; `zext(w, t)` zero-extends.
//!   `trunc(w, zext(W, u)) = u` when `u` has `w` bits, `trunc(w, trunc(_, u))
//!   = trunc(w, u)`, and constants fold.
//! * `widen(low, unknown)` is a value whose low bits are `low` and whose upper
//!   bits are unknown (a block-entry register that holds a narrower virtual
//!   register): `trunc(low.bits, widen) = low`.
//! * `lin(base, k)` is the 64-bit sum `base + k`; `lin(lin(b, a), c) =
//!   lin(b, a + c)` (wrapping), `lin(b, 0) = b`, `lin(const, k)` folds.
//! * 64-bit integer sums, differences and multiples by a constant (`add64`,
//!   `scale64`) are kept as affine forms `c + Σ kᵢ·tᵢ` over the ring of
//!   integers modulo 2^64: atoms sorted by id, no zero coefficient, the
//!   constant carried by `lin`. Two spellings of the same affine combination
//!   of the same atoms are one term (`(a + b) + c = a + (b + c)`, `a + a =
//!   2·a`, `(x + 1)·4 = 4·x + 4`).
//!
//! Everything else is uninterpreted: an operation term is keyed by its
//! operation key (opcode or normalized event class plus every non-register
//! operand), its input terms and its output slot, so two computations agree
//! only when they are the same operation on the same inputs.

use trust_cg_ir::fast_hash::FxHashMap as HashMap;

/// Identifier of an interned term. Equal ids mean equal (normalized) terms.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub(crate) struct TermId(pub(crate) u32);

/// The most atoms an interpreted affine form keeps: address arithmetic needs
/// a handful; past this an add stays an uninterpreted operation.
pub(crate) const MAX_AFFINE_ATOMS: usize = 8;

/// A 64-bit affine form `constant + Σ coef·atom` (wrapping): atoms sorted by
/// id, no coefficient zero (see [`TermArena::affine`]).
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub(crate) struct Affine {
    pub(crate) constant: u64,
    pub(crate) atoms: Vec<(TermId, u64)>,
}

impl Affine {
    /// `self += k·other` (wrapping), keeping the form canonical.
    pub(crate) fn add_scaled(&mut self, other: &Affine, k: u64) {
        self.constant = self.constant.wrapping_add(other.constant.wrapping_mul(k));
        for &(atom, coef) in &other.atoms {
            let add = coef.wrapping_mul(k);
            match self.atoms.binary_search_by_key(&atom, |&(a, _)| a) {
                Ok(at) => {
                    let sum = self.atoms[at].1.wrapping_add(add);
                    if sum == 0 {
                        self.atoms.remove(at);
                    } else {
                        self.atoms[at].1 = sum;
                    }
                }
                Err(at) => {
                    if add != 0 {
                        self.atoms.insert(at, (atom, add));
                    }
                }
            }
        }
    }

    /// `self - k·other`.
    pub(crate) fn minus_scaled(&self, other: &Affine, k: u64) -> Affine {
        let mut out = self.clone();
        out.add_scaled(other, k.wrapping_neg());
        out
    }

    /// A constant `k` with `self = k·step`, when `step` is not zero and one
    /// exists over the integers (checked exactly).
    pub(crate) fn ratio_to(&self, step: &Affine) -> Option<u64> {
        let (num, den) = match step.atoms.first() {
            Some(&(atom, coef)) => {
                let at = self.atoms.binary_search_by_key(&atom, |&(a, _)| a).ok()?;
                (self.atoms[at].1 as i64, coef as i64)
            }
            None if step.constant != 0 => (self.constant as i64, step.constant as i64),
            None => return None,
        };
        if den == 0 || num.checked_rem(den)? != 0 {
            return None;
        }
        let k = num.checked_div(den)? as u64;
        let mut scaled = Affine::default();
        scaled.add_scaled(step, k);
        (scaled == *self).then_some(k)
    }
}

/// Identifier of an interned operation key.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub(crate) struct OpId(pub(crate) u32);

/// Non-register operand data that identifies an operation.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Aux {
    /// An immediate operand at an operand position.
    Imm(u8, i64),
    /// A floating-point immediate (bit pattern).
    FImm(u8, u64),
    /// A symbol reference (`true` for an exact module symbol).
    Sym(u8, String, bool),
    /// A jump table reference.
    JumpTable(u8, u32),
    /// Width (bits) and bank of a register operand at a position
    /// (`fpr` = SIMD/FP view), so `add w0` and `add x0` stay distinct.
    View(u8, u16, bool),
    /// A zero register read at a position, with its width.
    Zero(u8, u16),
    /// A physical register named by an implicit use or definition list.
    Implicit(u16),
    /// Instruction flag bits that change behavior.
    Flags(u32),
    /// An operand shape that carries no value but distinguishes forms
    /// (block, stack slot or frame index position markers).
    Shape(u8, u8),
}

/// What an operation key names.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum OpTag {
    /// An AArch64 opcode, by discriminant.
    Inst(u16),
    /// A normalized plain memory access (any spelling of the same access:
    /// offset, pre/post-index, split or resolved addressing).
    Load,
    Store,
    /// A call.
    Call,
    /// A return.
    Ret,
    /// A tail call.
    TailCall,
    /// Condition atoms of a branch: NZCV condition (base code), compare
    /// with zero, test bit.
    CondFlags,
    CondZero,
    CondBit,
    /// A multi-way indirect branch target.
    IndirectTarget,
}

/// An interned operation key.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) struct OpKey {
    pub(crate) tag: OpTag,
    pub(crate) aux: Vec<Aux>,
}

/// An interned term.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Term {
    /// A constant of `bits` bits (higher bits zero).
    Const { bits: u16, value: u128 },
    /// The value of a physical location on function entry (full width).
    Entry { loc: u16, bits: u16 },
    /// The canonical frame address: SP on function entry.
    Cfa,
    /// Address of a pre-frame stack slot (stage 1 only).
    Slot(u32),
    /// Address of an incoming stack argument (stage 1 only).
    IncomingArg(i64),
    /// A block-entry value of the specification (an inferred join).
    Leaf { block: u32, index: u32, bits: u16 },
    /// A value known to be nothing in particular, keyed by the function
    /// (`side`), block, site and slot that produced it, so the same program
    /// point yields the same unknown on every fixpoint iteration while the
    /// two functions never share one.
    Unknown {
        side: u8,
        block: u32,
        site: u32,
        slot: u64,
        bits: u16,
    },
    /// A value whose low `low.bits` bits are `low` and whose upper bits are
    /// unknown (keyed like [`Term::Unknown`]).
    Widen {
        low: TermId,
        side: u8,
        block: u32,
        site: u32,
        slot: u64,
        bits: u16,
    },
    /// The low `bits` bits of `arg`.
    Trunc { bits: u16, arg: TermId },
    /// `arg` zero-extended to `bits` bits.
    Zext { bits: u16, arg: TermId },
    /// The 64-bit sum `base + offset` (wrapping).
    Lin { base: TermId, offset: i64 },
    /// The 64-bit sum `Σ coef·atom` (wrapping) of at least two atoms, or of
    /// one atom whose coefficient is not one: atoms sorted by id, none a
    /// constant, [`Term::Lin`] or [`Term::Sum`], no coefficient zero.
    Sum { atoms: Box<[(TermId, u64)]> },
    /// Output `slot` of operation `op` on `args`.
    Op {
        op: OpId,
        args: Box<[TermId]>,
        slot: u16,
        bits: u16,
    },
    /// Output `slot` of the `ordinal`-th effect of block `block` (the same in
    /// both functions once their effects matched).
    Ev {
        block: u32,
        ordinal: u32,
        slot: u16,
        bits: u16,
    },
}

/// The arena of interned terms and operation keys.
#[derive(Default)]
pub(crate) struct TermArena {
    terms: Vec<Term>,
    /// Whether a term depends only on function-entry facts (no block leaf,
    /// effect result or unknown), so it may cross any join unchanged.
    rooted: Vec<bool>,
    /// Open-addressing index of `terms` by hash (`u32::MAX` empty): each
    /// term is stored once, in `terms`.
    slots: Vec<u32>,
    ops: Vec<OpKey>,
    op_index: HashMap<OpKey, OpId>,
    /// Operation results whose bits above a width are known zero (an AND
    /// with a narrow mask, a logical shift right), by result term.
    significant: HashMap<TermId, u16>,
}

/// The number of value bits a width-`bits` term holds, as a mask.
fn mask(bits: u16) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

impl TermArena {
    /// An arena sized for about `terms` terms.
    pub(crate) fn with_capacity(terms: usize) -> Self {
        let slots = (terms.max(16) * 2).next_power_of_two();
        Self {
            terms: Vec::with_capacity(terms),
            rooted: Vec::with_capacity(terms),
            slots: vec![u32::MAX; slots],
            ..Self::default()
        }
    }

    fn hash_term(term: &Term) -> u64 {
        use std::hash::BuildHasher;
        if let Term::Op {
            op,
            args,
            slot,
            bits,
        } = term
        {
            return Self::hash_op(*op, args, *slot, *bits);
        }
        trust_cg_ir::fast_hash::FxBuildHasher::default().hash_one(term)
    }

    /// The hash of `Term::Op { op, args, slot, bits }`, computed from its
    /// parts (so a lookup builds no boxed key).
    fn hash_op(op: OpId, args: &[TermId], slot: u16, bits: u16) -> u64 {
        use std::hash::{BuildHasher, Hasher};
        let mut hasher = trust_cg_ir::fast_hash::FxBuildHasher::default().build_hasher();
        hasher.write_u64(0x6f70_5f74_6572_6d73);
        hasher.write_u32(op.0);
        hasher.write_usize(args.len());
        for arg in args {
            hasher.write_u32(arg.0);
        }
        hasher.write_u16(slot);
        hasher.write_u16(bits);
        hasher.finish()
    }

    /// Double the slot table and re-insert every term.
    fn grow(&mut self) {
        let size = (self.slots.len() * 2).max(32);
        self.slots = vec![u32::MAX; size];
        let mask = size - 1;
        for (id, term) in self.terms.iter().enumerate() {
            let mut at = (Self::hash_term(term) as usize) & mask;
            while self.slots[at] != u32::MAX {
                at = (at + 1) & mask;
            }
            self.slots[at] = id as u32;
        }
    }

    /// Number of interned terms (a deterministic work measure).
    pub(crate) fn len(&self) -> usize {
        self.terms.len()
    }

    pub(crate) fn get(&self, id: TermId) -> &Term {
        &self.terms[id.0 as usize]
    }

    pub(crate) fn op(&self, id: OpId) -> &OpKey {
        &self.ops[id.0 as usize]
    }

    /// Whether `id` depends only on function-entry facts.
    pub(crate) fn rooted(&self, id: TermId) -> bool {
        self.rooted[id.0 as usize]
    }

    pub(crate) fn bits(&self, id: TermId) -> u16 {
        match self.get(id) {
            Term::Const { bits, .. }
            | Term::Entry { bits, .. }
            | Term::Leaf { bits, .. }
            | Term::Unknown { bits, .. }
            | Term::Widen { bits, .. }
            | Term::Trunc { bits, .. }
            | Term::Zext { bits, .. }
            | Term::Op { bits, .. }
            | Term::Ev { bits, .. } => *bits,
            Term::Cfa
            | Term::Slot(_)
            | Term::IncomingArg(_)
            | Term::Lin { .. }
            | Term::Sum { .. } => 64,
        }
    }

    pub(crate) fn is_unknown(&self, id: TermId) -> bool {
        matches!(self.get(id), Term::Unknown { .. })
    }

    fn intern(&mut self, term: Term) -> TermId {
        if (self.terms.len() + 1) * 2 > self.slots.len() {
            self.grow();
        }
        let mask = self.slots.len() - 1;
        let mut at = (Self::hash_term(&term) as usize) & mask;
        loop {
            let slot = self.slots[at];
            if slot == u32::MAX {
                break;
            }
            if self.terms[slot as usize] == term {
                return TermId(slot);
            }
            at = (at + 1) & mask;
        }
        let rooted = match &term {
            Term::Const { .. }
            | Term::Entry { .. }
            | Term::Cfa
            | Term::Slot(_)
            | Term::IncomingArg(_) => true,
            Term::Leaf { .. } | Term::Unknown { .. } | Term::Widen { .. } | Term::Ev { .. } => {
                false
            }
            Term::Trunc { arg, .. } | Term::Zext { arg, .. } => self.rooted(*arg),
            Term::Lin { base, .. } => self.rooted(*base),
            Term::Sum { atoms } => atoms.iter().all(|&(a, _)| self.rooted(a)),
            Term::Op { args, .. } => args.iter().all(|&a| self.rooted(a)),
        };
        let id =
            TermId(u32::try_from(self.terms.len()).expect("term arena exceeds u32::MAX entries"));
        self.slots[at] = id.0;
        self.terms.push(term);
        self.rooted.push(rooted);
        id
    }

    pub(crate) fn op_id(&mut self, key: OpKey) -> OpId {
        if let Some(&id) = self.op_index.get(&key) {
            return id;
        }
        let id = OpId(u32::try_from(self.ops.len()).expect("op table exceeds u32::MAX entries"));
        self.ops.push(key.clone());
        self.op_index.insert(key, id);
        id
    }

    pub(crate) fn constant(&mut self, bits: u16, value: u128) -> TermId {
        self.intern(Term::Const {
            bits,
            value: value & mask(bits),
        })
    }

    pub(crate) fn const_value(&self, id: TermId) -> Option<u128> {
        match self.get(id) {
            Term::Const { value, .. } => Some(*value),
            _ => None,
        }
    }

    pub(crate) fn entry(&mut self, loc: u16, bits: u16) -> TermId {
        self.intern(Term::Entry { loc, bits })
    }

    pub(crate) fn cfa(&mut self) -> TermId {
        self.intern(Term::Cfa)
    }

    pub(crate) fn slot(&mut self, slot: u32) -> TermId {
        self.intern(Term::Slot(slot))
    }

    pub(crate) fn incoming_arg(&mut self, offset: i64) -> TermId {
        self.intern(Term::IncomingArg(offset))
    }

    pub(crate) fn leaf(&mut self, block: u32, index: u32, bits: u16) -> TermId {
        self.intern(Term::Leaf { block, index, bits })
    }

    /// The unknown produced at `(side, block, site, slot)`.
    pub(crate) fn unknown(
        &mut self,
        side: u8,
        block: u32,
        site: u32,
        slot: u64,
        bits: u16,
    ) -> TermId {
        self.intern(Term::Unknown {
            side,
            block,
            site,
            slot,
            bits,
        })
    }

    /// A `bits`-wide value whose low bits are `low` and whose upper bits are
    /// the unknown produced at `(side, block, site, slot)`. Identity when
    /// `low` is already `bits` wide.
    pub(crate) fn widen_keyed(
        &mut self,
        low: TermId,
        bits: u16,
        side: u8,
        block: u32,
        site: u32,
        slot: u64,
    ) -> TermId {
        if self.bits(low) >= bits {
            return low;
        }
        self.intern(Term::Widen {
            low,
            side,
            block,
            site,
            slot,
            bits,
        })
    }

    /// The low `bits` bits of `arg`.
    pub(crate) fn trunc(&mut self, bits: u16, arg: TermId) -> TermId {
        let width = self.bits(arg);
        if bits >= width {
            return arg;
        }
        match self.get(arg).clone() {
            // Constants fold.
            Term::Const { value, .. } => self.constant(bits, value),
            // trunc(w, trunc(W, u)) = trunc(w, u) for w < W.
            Term::Trunc { arg: inner, .. } => self.trunc(bits, inner),
            // trunc(w, zext(W, u)): the low w bits of u when u has at least
            // w bits, else u zero-extended to w.
            Term::Zext { arg: inner, .. } => {
                let inner_bits = self.bits(inner);
                if inner_bits >= bits {
                    self.trunc(bits, inner)
                } else {
                    self.zext(bits, inner)
                }
            }
            // trunc(w, widen(low)) keeps the known low part.
            Term::Widen { low, .. } => {
                let low_bits = self.bits(low);
                if low_bits >= bits {
                    self.trunc(bits, low)
                } else {
                    self.intern(Term::Trunc { bits, arg })
                }
            }
            _ => self.intern(Term::Trunc { bits, arg }),
        }
    }

    /// `arg` zero-extended to `bits` bits.
    pub(crate) fn zext(&mut self, bits: u16, arg: TermId) -> TermId {
        let width = self.bits(arg);
        if bits <= width {
            return arg;
        }
        match self.get(arg).clone() {
            Term::Const { value, .. } => self.constant(bits, value),
            // zext(W, zext(w, u)) = zext(W, u).
            Term::Zext { arg: inner, .. } => self.zext(bits, inner),
            // zext(W, trunc(w, u)) = u when u is W bits wide and its bits
            // above w are known zero.
            Term::Trunc { arg: inner, .. }
                if self.bits(inner) == bits && self.significant_bits(inner) <= width =>
            {
                inner
            }
            _ => self.intern(Term::Zext { bits, arg }),
        }
    }

    /// Record that `t`'s bits at and above `bits` are zero.
    pub(crate) fn note_significant(&mut self, t: TermId, bits: u16) {
        if bits < self.bits(t) {
            self.significant.insert(t, bits);
        }
    }

    /// The number of low bits of `t` that may be nonzero.
    pub(crate) fn significant_bits(&self, t: TermId) -> u16 {
        match self.get(t) {
            Term::Const { value, .. } => (128 - value.leading_zeros()) as u16,
            Term::Zext { arg, .. } => self.significant_bits(*arg),
            Term::Trunc { bits, arg } => (*bits).min(self.significant_bits(*arg)),
            _ => self
                .significant
                .get(&t)
                .copied()
                .unwrap_or_else(|| self.bits(t)),
        }
    }

    /// Read `arg` as a `bits`-wide value whose bits above `arg`'s width are
    /// zero: truncate a wider term, zero-extend a narrower one.
    pub(crate) fn resize(&mut self, bits: u16, arg: TermId) -> TermId {
        let width = self.bits(arg);
        if bits < width {
            self.trunc(bits, arg)
        } else {
            self.zext(bits, arg)
        }
    }

    /// The 64-bit sum `base + offset`.
    pub(crate) fn lin(&mut self, base: TermId, offset: i64) -> TermId {
        let base = if self.bits(base) == 64 {
            base
        } else {
            self.resize(64, base)
        };
        if offset == 0 {
            return base;
        }
        match self.get(base).clone() {
            Term::Const { value, .. } => {
                let sum = (value as u64).wrapping_add(offset as u64);
                self.constant(64, u128::from(sum))
            }
            Term::Lin {
                base: inner,
                offset: first,
            } => {
                let total = first.wrapping_add(offset);
                self.lin(inner, total)
            }
            _ => self.intern(Term::Lin { base, offset }),
        }
    }

    /// The affine form of the 64-bit term `term`: a constant, a
    /// [`Term::Lin`] or [`Term::Sum`] decomposed, any other term one atom.
    pub(crate) fn affine(&self, term: TermId) -> Affine {
        match self.get(term) {
            Term::Const { value, .. } => Affine {
                constant: *value as u64,
                atoms: Vec::new(),
            },
            Term::Lin { base, offset } => {
                let mut form = self.affine(*base);
                form.constant = form.constant.wrapping_add(*offset as u64);
                form
            }
            Term::Sum { atoms } => Affine {
                constant: 0,
                atoms: atoms.to_vec(),
            },
            _ => Affine {
                constant: 0,
                atoms: vec![(term, 1)],
            },
        }
    }

    /// The term of an affine form (the inverse of [`Self::affine`]).
    pub(crate) fn affine_term(&mut self, form: Affine) -> TermId {
        if form.atoms.is_empty() {
            return self.constant(64, u128::from(form.constant));
        }
        let base = match form.atoms.as_slice() {
            [(atom, 1)] => *atom,
            _ => self.intern(Term::Sum {
                atoms: form.atoms.into_boxed_slice(),
            }),
        };
        self.lin(base, form.constant as i64)
    }

    /// The 64-bit wrapping sum `a + k·b` of two 64-bit terms, or `None`
    /// when the form would exceed [`MAX_AFFINE_ATOMS`] atoms (the caller
    /// keeps the operation uninterpreted, so a long chain of adds stays
    /// linear in size).
    pub(crate) fn add_scaled64(&mut self, a: TermId, b: TermId, k: u64) -> Option<TermId> {
        let mut form = self.affine(a);
        form.add_scaled(&self.affine(b), k);
        (form.atoms.len() <= MAX_AFFINE_ATOMS).then(|| self.affine_term(form))
    }

    /// The 64-bit wrapping product `k·a` of a 64-bit term (`None` as for
    /// [`Self::add_scaled64`]).
    pub(crate) fn scale64(&mut self, a: TermId, k: u64) -> Option<TermId> {
        let mut form = Affine::default();
        form.add_scaled(&self.affine(a), k);
        (form.atoms.len() <= MAX_AFFINE_ATOMS).then(|| self.affine_term(form))
    }

    /// `(base, offset)` with `term = base + offset`, splitting a [`Term::Lin`].
    pub(crate) fn split_lin(&self, term: TermId) -> (TermId, i64) {
        match self.get(term) {
            Term::Lin { base, offset } => (*base, *offset),
            _ => (term, 0),
        }
    }

    pub(crate) fn op_term(&mut self, op: OpId, args: &[TermId], slot: u16, bits: u16) -> TermId {
        if (self.terms.len() + 1) * 2 > self.slots.len() {
            self.grow();
        }
        let mask = self.slots.len() - 1;
        let mut at = (Self::hash_op(op, args, slot, bits) as usize) & mask;
        loop {
            let found = self.slots[at];
            if found == u32::MAX {
                break;
            }
            if let Term::Op {
                op: o,
                args: a,
                slot: s,
                bits: b,
            } = &self.terms[found as usize]
                && *o == op
                && *s == slot
                && *b == bits
                && a[..] == *args
            {
                return TermId(found);
            }
            at = (at + 1) & mask;
        }
        self.intern(Term::Op {
            op,
            args: args.into(),
            slot,
            bits,
        })
    }

    pub(crate) fn ev(&mut self, block: u32, ordinal: u32, slot: u16, bits: u16) -> TermId {
        self.intern(Term::Ev {
            block,
            ordinal,
            slot,
            bits,
        })
    }

    /// The first pair of differing subterms of `a` and `b` (descending
    /// through operations of the same key and shape), for diagnostics.
    pub(crate) fn first_difference(&self, a: TermId, b: TermId) -> (TermId, TermId) {
        let (mut a, mut b) = (a, b);
        for _ in 0..256 {
            if a == b {
                break;
            }
            let next = match (self.get(a), self.get(b)) {
                (
                    Term::Op {
                        op: oa,
                        args: xa,
                        slot: sa,
                        ..
                    },
                    Term::Op {
                        op: ob,
                        args: xb,
                        slot: sb,
                        ..
                    },
                ) if oa == ob && sa == sb && xa.len() == xb.len() => xa
                    .iter()
                    .zip(xb.iter())
                    .find(|(x, y)| x != y)
                    .map(|(x, y)| (*x, *y)),
                (Term::Trunc { bits: ba, arg: xa }, Term::Trunc { bits: bb, arg: xb })
                | (Term::Zext { bits: ba, arg: xa }, Term::Zext { bits: bb, arg: xb })
                    if ba == bb =>
                {
                    Some((*xa, *xb))
                }
                (
                    Term::Lin {
                        base: xa,
                        offset: oa,
                    },
                    Term::Lin {
                        base: xb,
                        offset: ob,
                    },
                ) if oa == ob => Some((*xa, *xb)),
                _ => None,
            };
            match next {
                Some((x, y)) => {
                    a = x;
                    b = y;
                }
                None => break,
            }
        }
        (a, b)
    }

    /// A bounded, human-readable rendering of a term for diagnostics.
    pub(crate) fn render(&self, id: TermId) -> String {
        let mut out = String::new();
        self.render_into(id, 3, &mut out);
        out
    }

    fn render_into(&self, id: TermId, depth: u32, out: &mut String) {
        use std::fmt::Write;
        if depth == 0 {
            let _ = write!(out, "t{}", id.0);
            return;
        }
        match self.get(id) {
            Term::Const { bits, value } => {
                let _ = write!(out, "{value:#x}:{bits}");
            }
            Term::Entry { loc, bits } => {
                let _ = write!(out, "entry({}):{bits}", super::model::loc_name(*loc));
            }
            Term::Cfa => out.push_str("cfa"),
            Term::Slot(slot) => {
                let _ = write!(out, "slot{slot}");
            }
            Term::IncomingArg(offset) => {
                let _ = write!(out, "incoming_arg{offset}");
            }
            Term::Leaf { block, index, bits } => {
                let _ = write!(out, "in(bb{block}#{index}):{bits}");
            }
            Term::Unknown {
                side,
                block,
                site,
                slot,
                bits,
            } => {
                let who = if *side == 0 { "spec" } else { "impl" };
                let _ = write!(out, "unknown({who},bb{block},@{site},{slot:#x}):{bits}");
            }
            Term::Widen { low, bits, .. } => {
                let _ = write!(out, "widen{bits}(");
                self.render_into(*low, depth - 1, out);
                out.push(')');
            }
            Term::Trunc { bits, arg } => {
                let _ = write!(out, "trunc{bits}(");
                self.render_into(*arg, depth - 1, out);
                out.push(')');
            }
            Term::Zext { bits, arg } => {
                let _ = write!(out, "zext{bits}(");
                self.render_into(*arg, depth - 1, out);
                out.push(')');
            }
            Term::Lin { base, offset } => {
                out.push('(');
                self.render_into(*base, depth - 1, out);
                let _ = write!(out, "{offset:+})");
            }
            Term::Sum { atoms } => {
                out.push('(');
                for (i, (atom, coef)) in atoms.iter().enumerate() {
                    if i > 0 {
                        out.push_str(" + ");
                    }
                    let _ = write!(out, "{}*", *coef as i64);
                    self.render_into(*atom, depth - 1, out);
                }
                out.push(')');
            }
            Term::Op {
                op,
                args,
                slot,
                bits,
            } => {
                let key = self.op(*op);
                let _ = write!(out, "{:?}", key.tag);
                if !key.aux.is_empty() {
                    let _ = write!(out, "{:?}", key.aux);
                }
                out.push('(');
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    self.render_into(*arg, depth - 1, out);
                }
                let _ = write!(out, ")#{slot}:{bits}");
            }
            Term::Ev {
                block,
                ordinal,
                slot,
                bits,
            } => {
                let _ = write!(out, "effect(bb{block}#{ordinal}).{slot}:{bits}");
            }
        }
    }
}
