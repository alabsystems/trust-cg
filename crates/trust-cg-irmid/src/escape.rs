// trust-cg-irmid/escape.rs - which pointers outlive a bound, and how far
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The offset and escape analysis of a pointer through a wasm32 function,
//! shared by the wasm32 lane and the mid-end. The lane
//! (`trust-cg-codegen` `wasm/lower/captures.rs`) asks it whether an `Alloca`
//! that executes more than once per activation may keep one fixed frame
//! slot, and which fixed slots may share bytes; the mid-end's constant-table
//! promotion (`passes/ctp.rs`) asks it which accesses reach an allocation and
//! at which displacements. The facts are the same; each caller decides what
//! it needs of them. Addresses are 32 bits wide here (`usize`/`isize` are
//! wasm32 addresses): the analysis serves the wasm32 profile only.
//!
//! trust-ir gives every EXECUTION of an `Alloca` a fresh allocation that stays
//! valid until the function returns (the reference interpreter's
//! `eval_alloca`). A fixed slot is exact for an `Alloca` that runs at most once
//! per activation. For one inside a loop it is exact only when no pointer from
//! an earlier execution can be observed after a later one: then the reuse is
//! unobservable. A pointer from an earlier execution survives a later
//! execution only through
//!
//! * a block parameter of a block the `Alloca` does not strictly dominate (in
//!   strict SSA every other value derived from it is dead by then — a value
//!   whose definition the `Alloca` dominates cannot be live at the `Alloca`),
//! * memory: stored as a value, or handed to a callee that may store it, or
//! * its address BITS: the interpreter turns any integer back into a pointer
//!   to the live allocation containing that address (`inttoptr`), so an
//!   integer equal to the address, rebuilt with no data dependence on the
//!   pointer — by branching on its bits, by reading a table indexed by them,
//!   or by an instruction that lets execution continue only for some of them
//!   (a failing `assert` panics, and a false `assume`, a division by zero
//!   or an out-of-range shift is UB, so past it the address is known) —
//!   reaches the allocation again.
//!
//! So [`derive`] follows the address through integers too, and tells two
//! kinds of derived value apart. An OFFSET value is the address plus an
//! amount that does not depend on it: the pointer, a `GEP` of it by indices
//! that do not depend on it, its `ptrtoint` to an integer of at least 32 bits,
//! that integer plus or minus an independent one, and `inttoptr` of such an
//! integer. Every other value computed from the address carries its BITS
//! (`and`, a shift, a comparison, a narrowing cast, `inttoptr` of a bits
//! integer). Data flow keeps both kinds derived — they
//! root the allocation's liveness wherever they are live — and the address
//! escapes that data flow, a capture, exactly when a derived value steers
//! control flow (a branch or `switch` operand, a `select` condition), when
//! whether execution continues depends on one (an `assert` or `assume`
//! condition; a divisor, either operand of a signed division or remainder,
//! whose overflow is UB, or a shift amount; a float-to-integer conversion or
//! element index, which are UB out of range; an `inttoptr` from an integer
//! wider than an address, which is UB above the address space; a `GEP` of a
//! bits pointer or by a derived index, which is UB past it), when memory is
//! read or written at a bits-dependent location (any access through a bits
//! pointer, which is UB unless it lands in a live allocation, a bulk length
//! or fill from the address), when a bits value is handed to a callee (whose
//! own facts assume an offset), and in every case that already captured a
//! plain pointer. So a bits value never reaches memory, and only data flow,
//! comparisons and returns consume one.
//!
//! An access through an offset pointer reads or writes the allocation's own
//! bytes only while the pointer's PROVENANCE is the allocation. A `GEP` keeps
//! its operand's provenance (an access past the allocation is UB whatever the
//! layout), but `inttoptr` gives its result the provenance of whichever live
//! allocation contains the address (the interpreter's
//! `try_pointer_from_address`): the address plus a displacement outside
//! `[0, size)` may land in a NEIGHBOUR, whose bytes at a location that depends
//! on the address are then read or written. So the walk tracks each offset
//! value's displacement from the seed ([`Disp`]: a constant, or an index
//! times a scale plus a constant, the index bounded by its own definition or
//! by a dominating unsigned check `index < limit` of its current value), and
//! an `inttoptr` of an offset integer resolves to the seed's allocation only
//! when its displacement provably lies in `[0, size)`. A scaled displacement
//! that crosses an edge into a block parameter is kept only when its index
//! cannot have been rebound since (`FuncFacts::carried`). Any other such
//! pointer is STRAY: it may still be compared,
//! converted back to an integer, or moved, but an access, a `GEP` or bulk
//! operation through it, handing it to a callee, returning it, or putting it
//! in an aggregate is a capture. A seed whose size is unknown — an entry
//! parameter of a callee — records each displacement it needs inside its
//! allocation ([`Sym`]), and a caller checks the callee's needs against its
//! own argument (`ParamFate::needs`). A need may be relative to another entry
//! parameter (a checked length) only in a function whose entry block no
//! branch re-enters, where every entry parameter holds the caller's argument
//! for the whole activation.
//!
//! [`ParamCaptures`] answers the second question for callees defined in this
//! compilation, and whether a callee may hand an argument back in its result
//! (so the call's result carries the pointer on), optimistically over
//! recursion (a least fixpoint of both facts); a callee that is imported,
//! overridable at link time, or called indirectly is assumed to capture and
//! return every argument — except the C library's `memset`, `memcpy` and
//! `memmove`, whose contracts (ISO C 7.24.2.1, 7.24.2.2, 7.24.6.1) keep no
//! pointer argument, return only the destination, and reach memory only
//! through their pointer arguments' own allocations.

use std::collections::{HashMap, HashSet};

use trust_ir::{
    BinOp, BlockId, CastOp, Constant, FuncId, Function, ICmpOp, Inst, Linkage, Module, Ty, ValueId,
};

/// The most displacement bounds one entry parameter may ask of its callers
/// ([`ParamFate::needs`]); a parameter needing more counts as captured.
const MAX_NEEDS: usize = 8;

/// Rounds of the [`param_captures`] fixpoint that merge facts exactly; past
/// them any fact that still changes widens to "captures and returns", so a
/// displacement that grows around a recursion cannot keep the fixpoint going.
const EXACT_ROUNDS: usize = 32;

/// An upper bound on a displacement in bytes: `add`, plus `(P - 1) * scale`
/// when `len` names entry parameter `P`, an unsigned limit the displacement's
/// index was checked to lie below.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Sym {
    len: Option<usize>,
    scale: u64,
    add: i128,
}

impl Sym {
    const fn constant(add: i128) -> Self {
        Self {
            len: None,
            scale: 0,
            add,
        }
    }

    /// `(limit - 1) * scale + add` for a known `limit`.
    fn below(limit: u128, scale: u64, add: i128) -> Option<Self> {
        let top = i128::try_from(limit).ok()?.checked_sub(1)?;
        Some(Self::constant(
            top.checked_mul(i128::from(scale))?.checked_add(add)?,
        ))
    }

    /// The sum of two bounds, when at most one of them names a parameter.
    fn plus(self, other: Self) -> Option<Self> {
        let add = self.add.checked_add(other.add)?;
        match (self.len, other.len) {
            (_, None) => Some(Self { add, ..self }),
            (None, Some(_)) => Some(Self { add, ..other }),
            (Some(_), Some(_)) => None,
        }
    }
}

/// Keep, per parameter-and-scale, only the largest bound (it implies the
/// others), in a canonical order.
fn normalize(needs: &mut Vec<Sym>) {
    needs.sort();
    let mut kept: Vec<Sym> = Vec::with_capacity(needs.len());
    for n in needs.drain(..) {
        match kept.last_mut() {
            Some(k) if k.len == n.len && k.scale == n.scale => k.add = k.add.max(n.add),
            _ => kept.push(n),
        }
    }
    *needs = kept;
}

/// What a function defined here may do with an entry parameter's value
/// (an offset value, module docs).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ParamFate {
    /// Outlive the call: stored to memory, passed on to a capturing callee, or
    /// its address escaping the data flow ([`derive`]).
    captured: bool,
    /// Flow into a returned value.
    returned: bool,
    /// Flow into a returned value that carries the address's bits.
    returned_bits: bool,
    /// The call's result IS the argument (the C library's destination).
    identity: bool,
    /// Displacements from the argument that the callee turns back into
    /// pointers (`inttoptr`) and uses: each must lie below the argument's
    /// allocation's extent from the argument, or a caller counts the
    /// argument as captured. Empty when `captured`.
    needs: Vec<Sym>,
}

impl ParamFate {
    /// Everything a callee could do.
    fn unknown() -> Self {
        Self {
            captured: true,
            returned: true,
            returned_bits: true,
            identity: false,
            needs: Vec::new(),
        }
    }
}

/// [`ParamFate`] of every entry parameter of every function defined here,
/// and of the C library's bulk-memory functions.
#[derive(Debug, Clone, Default)]
pub struct ParamCaptures {
    by_func: HashMap<FuncId, Vec<ParamFate>>,
}

impl ParamCaptures {
    fn fate(&self, callee: FuncId, index: usize) -> ParamFate {
        self.by_func
            .get(&callee)
            .and_then(|v| v.get(index))
            .cloned()
            .unwrap_or_else(ParamFate::unknown)
    }
}

/// The fates of a C library bulk-memory function's parameters, when `func`
/// is declared (its body is linked from elsewhere) under its C name and
/// shape: the destination is returned
/// (as an offset) and kept by nobody, a source is only read, and a fill byte
/// or length derived from an address writes or reaches memory by it.
fn libc_fates(module: &Module, func: &Function) -> Option<Vec<ParamFate>> {
    let ft = module.func_type(func.ty)?;
    let pointer = |t: &Ty| is_address_ty(t) && !matches!(t, Ty::FatPtr(_));
    let integer = |t: &Ty| t.is_integer() || matches!(t, Ty::Isize | Ty::Usize);
    let fill_or_len = ParamFate::unknown();
    let dst = ParamFate {
        returned: true,
        identity: true,
        ..ParamFate::default()
    };
    let returns_ok = match ft.returns.as_slice() {
        [] => true,
        [r] => pointer(r),
        _ => false,
    };
    if ft.is_vararg || !returns_ok || ft.params.len() != 3 {
        return None;
    }
    let (a, b, c) = (&ft.params[0], &ft.params[1], &ft.params[2]);
    match func.name.as_str() {
        "memset" if pointer(a) && integer(b) && integer(c) => {
            Some(vec![dst, fill_or_len.clone(), fill_or_len])
        }
        "memcpy" | "memmove" if pointer(a) && pointer(b) && integer(c) => {
            Some(vec![dst, ParamFate::default(), fill_or_len])
        }
        _ => None,
    }
}

/// Uses of each value: `(block index, node index)`.
type UseIndex = HashMap<ValueId, Vec<(usize, usize)>>;

fn use_index(func: &Function) -> UseIndex {
    let mut uses: UseIndex = HashMap::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (ni, node) in block.body.iter().enumerate() {
            node.inst
                .visit_value_operands(|v| uses.entry(v).or_default().push((bi, ni)));
        }
    }
    for list in uses.values_mut() {
        list.dedup();
    }
    uses
}

/// The width of an integer type in bits (`usize`/`isize`: a wasm32 address).
fn int_width(ty: &Ty) -> Option<u32> {
    match ty {
        Ty::Usize | Ty::Isize => Some(32),
        t if t.is_integer() => t.bit_width(),
        _ => None,
    }
}

/// The largest unsigned value of `w` bits.
fn ones(w: u32) -> u128 {
    u128::MAX.checked_shr(128u32.saturating_sub(w)).unwrap_or(0)
}

/// A bounds check a branch establishes: in every block `block` dominates,
/// `index < limit` held, unsigned, when the branch was taken.
#[derive(Debug, Clone, Copy)]
struct Guard {
    block: usize,
    index: ValueId,
    limit: ValueId,
}

/// The per-function facts the walk consults: uses, definitions, entry
/// parameters, dominators and the bounds checks branches establish.
pub struct FuncFacts<'f> {
    func: &'f Function,
    uses: UseIndex,
    block_index: HashMap<BlockId, usize>,
    types: HashMap<ValueId, Ty>,
    defs: HashMap<ValueId, (usize, usize)>,
    /// The block each block parameter belongs to.
    block_params: HashMap<ValueId, usize>,
    /// The entry parameters, by position, when no branch re-enters the entry
    /// block (so each holds the caller's argument for the whole activation);
    /// empty otherwise, since a branch back would rebind them.
    params: HashMap<ValueId, usize>,
    /// Block parameters every edge binds to one entry parameter (or to
    /// themselves): a loop-invariant copy of it.
    same: HashMap<ValueId, ValueId>,
    guards: Vec<Guard>,
    idom: Vec<usize>,
    entry: usize,
}

impl<'f> FuncFacts<'f> {
    /// Index `func` (`types` types its values where known; an untyped field
    /// operand reads as a pointer carrier) and find its bounds checks.
    pub fn new(
        func: &'f Function,
        block_index: HashMap<BlockId, usize>,
        types: HashMap<ValueId, Ty>,
    ) -> Self {
        let n = func.blocks.len();
        let mut defs = HashMap::new();
        let mut block_params = HashMap::new();
        for (bi, block) in func.blocks.iter().enumerate() {
            for (v, _) in &block.params {
                block_params.insert(*v, bi);
            }
            for (ni, node) in block.body.iter().enumerate() {
                for &r in &node.results {
                    defs.insert(r, (bi, ni));
                }
            }
        }
        let entry = block_index.get(&func.entry).copied().unwrap_or(usize::MAX);
        let params = if entry_reentered(func) {
            HashMap::new()
        } else {
            func.blocks
                .get(entry)
                .map(|b| {
                    b.params
                        .iter()
                        .enumerate()
                        .map(|(i, (v, _))| (*v, i))
                        .collect()
                })
                .unwrap_or_default()
        };
        let mut facts = Self {
            func,
            uses: use_index(func),
            block_index,
            types,
            defs,
            block_params,
            params,
            guards: Vec::new(),
            same: HashMap::new(),
            idom: vec![usize::MAX; n],
            entry,
        };
        if entry < n {
            facts.find_same();
            facts.find_guards();
        }
        facts
    }

    /// The block parameters (outside the entry block) whose every incoming
    /// argument is the parameter itself or one entry parameter: they hold
    /// that parameter's value, which no execution rebinds.
    fn find_same(&mut self) {
        let mut incoming: HashMap<ValueId, Vec<ValueId>> = HashMap::new();
        for block in &self.func.blocks {
            let Some(term) = block.body.last() else {
                continue;
            };
            let mut edge = |target: &BlockId, args: &[ValueId]| {
                let Some(&ti) = self.block_index.get(target) else {
                    return;
                };
                for (k, a) in args.iter().enumerate() {
                    if let Some((p, _)) = self.func.blocks[ti].params.get(k) {
                        incoming.entry(*p).or_default().push(*a);
                    }
                }
            };
            match &term.inst {
                Inst::Br { target, args } => edge(target, args),
                Inst::CondBr {
                    then_target,
                    then_args,
                    else_target,
                    else_args,
                    ..
                } => {
                    edge(then_target, then_args);
                    edge(else_target, else_args);
                }
                Inst::Switch {
                    default,
                    default_args,
                    cases,
                    ..
                } => {
                    edge(default, default_args);
                    for c in cases {
                        edge(&c.target, &c.args);
                    }
                }
                _ => {}
            }
        }
        let mut incoming: Vec<(ValueId, Vec<ValueId>)> = incoming
            .into_iter()
            .filter(|(p, _)| !self.params.contains_key(p))
            .collect();
        incoming.sort_unstable_by_key(|(p, _)| *p);
        loop {
            let mut changed = false;
            for (p, args) in &incoming {
                if self.same.contains_key(p) {
                    continue;
                }
                let mut one: Option<ValueId> = None;
                let all = args.iter().all(|a| {
                    let c = self.canon(*a);
                    c == *p || (self.params.contains_key(&c) && *one.get_or_insert(c) == c)
                });
                if all && let Some(v) = one {
                    self.same.insert(*p, v);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }

    /// Dominators over every edge, then the checks of every two-way branch
    /// whose taken edge is the only way into its target.
    fn find_guards(&mut self) {
        let n = self.func.blocks.len();
        let mut succs: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (bi, block) in self.func.blocks.iter().enumerate() {
            let Some(term) = block.body.last() else {
                continue;
            };
            let mut push = |t: &BlockId| {
                if let Some(&ti) = self.block_index.get(t) {
                    succs[bi].push(ti);
                }
            };
            match &term.inst {
                Inst::Br { target, .. } => push(target),
                Inst::CondBr {
                    then_target,
                    else_target,
                    ..
                } => {
                    push(then_target);
                    push(else_target);
                }
                Inst::Switch { default, cases, .. } => {
                    push(default);
                    for c in cases {
                        push(&c.target);
                    }
                }
                _ => {}
            }
        }
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (p, ss) in succs.iter().enumerate() {
            for &b in ss {
                preds[b].push(p);
            }
        }
        let (rpo, _) = reverse_postorder(&succs, self.entry, n);
        self.idom = compute_idom(&preds, &rpo, self.entry, n);
        for (c, block) in self.func.blocks.iter().enumerate() {
            let Some(Inst::CondBr {
                cond,
                then_target,
                else_target,
                ..
            }) = block.body.last().map(|t| &t.inst)
            else {
                continue;
            };
            if then_target == else_target || rpo[c] == usize::MAX {
                continue;
            }
            let Some(Inst::ICmp { op, lhs, rhs, .. }) = self.def(self.canon(*cond)) else {
                continue;
            };
            let (target, index, limit) = match op {
                ICmpOp::Ult => (then_target, *lhs, *rhs),
                ICmpOp::Ugt => (then_target, *rhs, *lhs),
                ICmpOp::Uge => (else_target, *lhs, *rhs),
                ICmpOp::Ule => (else_target, *rhs, *lhs),
                _ => continue,
            };
            let Some(&t) = self.block_index.get(target) else {
                continue;
            };
            // The taken edge must be the only way into `t` (and `t` not the
            // entry, whose parameters a branch back would rebind): then every
            // execution of a block `t` dominates follows the check of the
            // latest `index` and `limit` (both dominate the check).
            if t == self.entry || preds[t] != [c] {
                continue;
            }
            self.guards.push(Guard {
                block: t,
                index: self.canon(index),
                limit: self.canon(limit),
            });
        }
    }

    /// The `(block index, node index)` of every instruction that uses `v`.
    pub fn uses_of(&self, v: ValueId) -> &[(usize, usize)] {
        self.uses.get(&v).map_or(&[], Vec::as_slice)
    }

    /// The instruction defining `v`.
    pub fn def(&self, v: ValueId) -> Option<&'f Inst> {
        let &(bi, ni) = self.defs.get(&v)?;
        Some(&self.func.blocks[bi].body[ni].inst)
    }

    /// `v` through copies, value-preserving integer casts (a truncation of a
    /// zero extension to no more bits than it extended from included) and
    /// block parameters that only ever hold an entry parameter.
    fn canon(&self, mut v: ValueId) -> ValueId {
        for _ in 0..64 {
            match self.def(v) {
                Some(Inst::Copy { operand, .. }) => v = *operand,
                Some(Inst::Cast {
                    op: CastOp::Trunc,
                    dst_ty,
                    operand,
                    ..
                }) if int_width(dst_ty).is_some_and(|w| w >= 32)
                    && matches!(self.def(*operand), Some(Inst::Cast {
                        op: CastOp::ZExt,
                        src_ty,
                        ..
                    }) if int_width(src_ty).is_some_and(|s| int_width(dst_ty) >= Some(s))) =>
                {
                    v = *operand;
                }
                Some(Inst::Cast {
                    op: CastOp::Bitcast | CastOp::Transmute | CastOp::ZExt,
                    src_ty,
                    dst_ty,
                    operand,
                }) if int_width(src_ty).is_some_and(|w| w >= 32)
                    && int_width(dst_ty).is_some_and(|w| w >= 32) =>
                {
                    v = *operand;
                }
                None => match self.same.get(&v) {
                    Some(&w) => v = w,
                    None => break,
                },
                _ => break,
            }
        }
        v
    }

    /// The value of `v` when it is an integer constant (or a sum, difference
    /// or product of them), as an unsigned number of its type's width.
    pub fn const_of(&self, v: ValueId) -> Option<u128> {
        self.const_at(v, 8)
    }

    fn const_at(&self, v: ValueId, depth: u32) -> Option<u128> {
        let depth = depth.checked_sub(1)?;
        let wrap = |ty: &Ty, x: i128| -> Option<u128> { Some((x as u128) & ones(int_width(ty)?)) };
        match self.def(self.canon(v))? {
            Inst::Const {
                ty,
                value: Constant::Int(c),
            } => wrap(ty, *c),
            Inst::BinOp { op, ty, lhs, rhs } if int_width(ty).is_some_and(|w| w <= 64) => {
                let a = i128::try_from(self.const_at(*lhs, depth)?).ok()?;
                let b = i128::try_from(self.const_at(*rhs, depth)?).ok()?;
                let x = match op {
                    BinOp::Add => a.checked_add(b)?,
                    BinOp::Sub => a.checked_sub(b)?,
                    BinOp::Mul => a.checked_mul(b)?,
                    _ => return None,
                };
                wrap(ty, x)
            }
            _ => None,
        }
    }

    /// The independent amount `v` adds to a displacement.
    fn term(&self, v: ValueId) -> Disp {
        if let Some(c) = self.const_of(v).and_then(|c| i128::try_from(c).ok()) {
            return Disp::Const(c);
        }
        let v = self.canon(v);
        let scaled = |x: ValueId, s: u128| -> Disp {
            u64::try_from(s).map_or(Disp::Unknown, |scale| Disp::Scaled {
                index: self.canon(x),
                scale,
                add: 0,
            })
        };
        match self.def(v) {
            Some(Inst::BinOp {
                op: BinOp::Mul,
                lhs,
                rhs,
                ..
            }) => match (self.const_of(*lhs), self.const_of(*rhs)) {
                (_, Some(s)) => scaled(*lhs, s),
                (Some(s), _) => scaled(*rhs, s),
                _ => scaled(v, 1),
            },
            Some(Inst::BinOp {
                op: BinOp::Shl,
                lhs,
                rhs,
                ..
            }) => match self.const_of(*rhs) {
                Some(k) if k < 32 => scaled(*lhs, 1 << k),
                _ => scaled(v, 1),
            },
            _ => scaled(v, 1),
        }
    }

    /// The largest unsigned value `v` can take on any execution, from its
    /// definition alone: a constant, a remainder by or a mask with one, a
    /// zero extension from a narrower type, a truncation of a bounded value
    /// or a selection between two.
    fn max_of(&self, v: ValueId) -> Option<u128> {
        self.max_at(v, 8)
    }

    fn max_at(&self, v: ValueId, depth: u32) -> Option<u128> {
        let depth = depth.checked_sub(1)?;
        if let Some(c) = self.const_of(v) {
            return Some(c);
        }
        let tighter = |a: Option<u128>, b: Option<u128>| match (a, b) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        };
        match self.def(self.canon(v))? {
            Inst::BinOp {
                op: BinOp::URem,
                lhs,
                rhs,
                ..
            } => {
                let by = self.const_of(*rhs).filter(|&c| c > 0).map(|c| c - 1);
                tighter(by, self.max_at(*lhs, depth))
            }
            Inst::BinOp {
                op: BinOp::And,
                lhs,
                rhs,
                ..
            } => tighter(self.max_at(*lhs, depth), self.max_at(*rhs, depth)),
            Inst::BinOp {
                op: BinOp::LShr,
                ty,
                lhs,
                rhs,
            } => {
                let k = u32::try_from(self.const_of(*rhs)?).ok()?;
                let top = self
                    .max_at(*lhs, depth)
                    .or_else(|| int_width(ty).map(ones))?;
                Some(top.checked_shr(k).unwrap_or(0))
            }
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty,
                operand,
                ..
            } => tighter(int_width(src_ty).map(ones), self.max_at(*operand, depth)),
            Inst::Cast {
                op: CastOp::Trunc,
                dst_ty,
                operand,
                ..
            } => {
                let all = int_width(dst_ty).map(ones)?;
                Some(
                    self.max_at(*operand, depth)
                        .filter(|&m| m <= all)
                        .unwrap_or(all),
                )
            }
            Inst::Select {
                then_val, else_val, ..
            } => Some(
                self.max_at(*then_val, depth)?
                    .max(self.max_at(*else_val, depth)?),
            ),
            _ => None,
        }
    }

    /// Does block `a` dominate block `b`?
    fn dominates(&self, a: usize, b: usize) -> bool {
        b < self.idom.len()
            && self.idom[b] != usize::MAX
            && dominates_in(&self.idom, a, b, self.entry)
    }

    /// `disp` of a value an edge binds to a parameter of block `target`.
    ///
    /// A scaled displacement names its index by value, and a value's
    /// displacement holds of the index's CURRENT value wherever the value is
    /// used: for an instruction result, because the index's definition
    /// dominates the result's, so in strict SSA a later execution of the index's
    /// definition reaches a use only through the result's definition again.
    /// A block parameter keeps that only when the index's definition strictly
    /// dominates `target`, so that redefining the index reaches a use only
    /// through a new binding of the parameter; otherwise (an index rebound
    /// around a loop, or one defined in `target` itself) the parameter may hold
    /// a displacement built from an earlier index, and it is unknown.
    fn carried(&self, disp: Disp, target: usize) -> Disp {
        let Disp::Scaled { index, .. } = disp else {
            return disp;
        };
        let defined = self
            .defs
            .get(&index)
            .map(|&(b, _)| b)
            .or_else(|| self.block_params.get(&index).copied());
        match defined {
            Some(b) if b != target && self.dominates(b, target) => disp,
            _ => Disp::Unknown,
        }
    }

    /// Upper bounds on `disp` that hold in block `at` (constants first), or
    /// none when it may be negative or has no bound there: an index is
    /// bounded by its own definition ([`Self::max_of`]) or by a check that
    /// dominates `at`.
    fn bounds(&self, disp: Disp, at: usize) -> Vec<Sym> {
        match disp {
            Disp::Const(c) if c >= 0 => vec![Sym::constant(c)],
            Disp::Scaled { index, scale, add } if add >= 0 => {
                let mut out: Vec<Sym> = Vec::new();
                if let Some(m) = self.max_of(index) {
                    out.extend(m.checked_add(1).and_then(|l| Sym::below(l, scale, add)));
                }
                for g in &self.guards {
                    if g.index != index || !self.dominates(g.block, at) {
                        continue;
                    }
                    if let Some(l) = self.const_of(g.limit) {
                        out.extend(Sym::below(l, scale, add));
                    } else if let Some(&j) = self.params.get(&g.limit) {
                        out.push(Sym {
                            len: Some(j),
                            scale,
                            add,
                        });
                    }
                }
                out.sort_by_key(|s| s.len.is_some());
                out
            }
            _ => Vec::new(),
        }
    }
}

/// An offset value's displacement from the seed's address, modulo 2^32: an
/// exact constant, `index * scale + add` for an unsigned `index`, or
/// unknown.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Disp {
    Const(i128),
    Scaled {
        index: ValueId,
        scale: u64,
        add: i128,
    },
    Unknown,
}

impl Disp {
    /// `self + term`.
    fn plus(self, term: Disp) -> Disp {
        match (self, term) {
            (Disp::Const(a), Disp::Const(b)) => a.checked_add(b).map_or(Disp::Unknown, Disp::Const),
            (Disp::Const(a), Disp::Scaled { index, scale, add })
            | (Disp::Scaled { index, scale, add }, Disp::Const(a)) => a
                .checked_add(add)
                .map_or(Disp::Unknown, |add| Disp::Scaled { index, scale, add }),
            _ => Disp::Unknown,
        }
    }

    /// `self - c`.
    fn minus(self, c: i128) -> Disp {
        match c.checked_neg() {
            Some(n) => self.plus(Disp::Const(n)),
            None => Disp::Unknown,
        }
    }
}

/// What the walk knows of one derived value (module docs).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fact {
    /// It carries the address's bits; otherwise it is an offset value.
    pub bits: bool,
    /// An offset value's displacement.
    pub disp: Disp,
    /// A pointer `inttoptr` may have resolved to another allocation.
    pub stray: bool,
}

impl Fact {
    const BITS: Fact = Fact {
        bits: true,
        disp: Disp::Unknown,
        stray: false,
    };

    const fn offset(disp: Disp) -> Fact {
        Fact {
            bits: false,
            disp,
            stray: false,
        }
    }

    /// What holds of a value that may be either.
    fn join(self, other: Fact) -> Fact {
        if self.bits || other.bits {
            return Fact::BITS;
        }
        Fact {
            bits: false,
            disp: if self.disp == other.disp {
                self.disp
            } else {
                Disp::Unknown
            },
            stray: self.stray || other.stray,
        }
    }

    /// Whether an access, `GEP`, call or return through the value observes
    /// more than the seed allocation's own bytes.
    fn escapes(self) -> bool {
        self.bits || self.stray
    }
}

/// How far the seed's allocation extends from the seed.
#[derive(Debug, Clone, Copy)]
pub enum Extent {
    /// Exactly this many bytes.
    Bytes(u64),
    /// The seed is an entry parameter: record what it needs.
    Param,
    /// Not known: no displacement is provably inside.
    Unknown,
}

/// The values derived from `seeds` (module docs): whether the address they
/// carry is captured or returned (and returned as bits), and the blocks whose
/// parameters received one.
pub struct Derived {
    pub captured: bool,
    pub returned: bool,
    pub returned_bits: bool,
    pub param_blocks: Vec<usize>,
    /// Every derived value found (the seeds included). Complete unless
    /// `captured`, where the walk stops.
    pub values: Vec<ValueId>,
    /// Each derived value's final fact (the join of every fact the walk
    /// gave it). Complete unless `captured`.
    pub facts: HashMap<ValueId, Fact>,
    /// With [`Extent::Param`]: the displacements the seed needs inside its
    /// allocation.
    needs: Vec<Sym>,
}

/// The walk's view of the seed's extent, collecting needs.
struct Bounds<'a, 'f> {
    facts: &'a FuncFacts<'f>,
    extent: Extent,
    needs: Vec<Sym>,
}

impl Bounds<'_, '_> {
    /// Whether some bound in `candidates` keeps every displacement inside
    /// the allocation. Against an unknown extent (an entry parameter), the
    /// bound recorded as a need is one relative to another parameter (a
    /// checked length) when there is one, else the smallest.
    fn accept(&mut self, candidates: &[Sym]) -> bool {
        match self.extent {
            Extent::Bytes(size) => candidates
                .iter()
                .any(|b| b.len.is_none() && b.add < i128::from(size)),
            Extent::Param => {
                let best = candidates
                    .iter()
                    .find(|b| b.len.is_some())
                    .or_else(|| candidates.iter().min_by_key(|b| b.add));
                best.is_some_and(|b| {
                    self.needs.push(*b);
                    true
                })
            }
            Extent::Unknown => false,
        }
    }

    /// Whether `inttoptr` of an integer at `disp` from the seed, in block
    /// `at`, resolves to the seed's allocation.
    fn resolves(&mut self, disp: Disp, at: usize) -> bool {
        let candidates = self.facts.bounds(disp, at);
        self.accept(&candidates)
    }

    /// Whether a callee's `need` of an argument at `disp` from the seed, in
    /// block `at` with arguments `args`, lies inside the allocation.
    fn passes(&mut self, disp: Disp, need: Sym, args: &[ValueId], at: usize) -> bool {
        let need = match need.len {
            None => need,
            Some(j) => {
                let Some(&arg) = args.get(j) else {
                    return false;
                };
                if let Some(l) = self.facts.const_of(arg) {
                    match Sym::below(l, need.scale, need.add) {
                        Some(s) => s,
                        None => return false,
                    }
                } else if let Some(&k) = self.facts.params.get(&self.facts.canon(arg)) {
                    Sym {
                        len: Some(k),
                        ..need
                    }
                } else {
                    return false;
                }
            }
        };
        let candidates: Vec<Sym> = self
            .facts
            .bounds(disp, at)
            .into_iter()
            .filter_map(|b| b.plus(need))
            .collect();
        self.accept(&candidates)
    }
}

/// Follow `seeds` (offset values of one address, displacement 0) through
/// `facts.func`. A value's fact only ever weakens ([`Fact::join`]), and a
/// value whose fact weakens is walked again, so the walk reaches a fixpoint.
pub fn derive(
    facts: &FuncFacts<'_>,
    table: &ParamCaptures,
    extent: Extent,
    seeds: &[ValueId],
) -> Derived {
    let func = facts.func;
    let mut known: HashMap<ValueId, Fact> = seeds
        .iter()
        .map(|&s| (s, Fact::offset(Disp::Const(0))))
        .collect();
    let mut work: Vec<ValueId> = seeds.to_vec();
    let mut bounds = Bounds {
        facts,
        extent,
        needs: Vec::new(),
    };
    let mut out = Derived {
        captured: false,
        returned: false,
        returned_bits: false,
        param_blocks: Vec::new(),
        values: seeds.to_vec(),
        facts: HashMap::new(),
        needs: Vec::new(),
    };
    let edge =
        |target: &BlockId, args: &[ValueId], d: ValueId, found: &mut Vec<(usize, ValueId)>| {
            let Some(&ti) = facts.block_index.get(target) else {
                return;
            };
            for (k, a) in args.iter().enumerate() {
                if *a == d
                    && let Some((p, _)) = func.blocks[ti].params.get(k)
                {
                    found.push((ti, *p));
                }
            }
        };
    while let Some(d) = work.pop() {
        let Some(sites) = facts.uses.get(&d) else {
            continue;
        };
        let fact = known.get(&d).copied().unwrap_or(Fact::BITS);
        let db = fact.bits;
        let derived = |v: &ValueId, known: &HashMap<ValueId, Fact>| known.contains_key(v);
        // A field access whose aggregate operand is a pointer reads or
        // writes through it (the rustc bridge's pointer-carried aggregates).
        let through = |v: &ValueId| facts.types.get(v).is_none_or(is_pointer_carrier);
        for &(bi, ni) in sites {
            let node = &func.blocks[bi].body[ni];
            // The fact of the node's results when they are derived; `None`
            // when they are not.
            let mut results: Option<Fact> = Some(fact);
            let mut params: Vec<(usize, ValueId)> = Vec::new();
            match &node.inst {
                // Control flow that depends on the address.
                Inst::CondBr { cond, .. } if *cond == d => out.captured = true,
                Inst::Switch { value, .. } if *value == d => out.captured = true,
                Inst::Select { cond, .. } if *cond == d => out.captured = true,
                // A check that stops execution unless it holds (a panic, or
                // UB when an `assume` is false): past it the address is
                // known. A derived condition is always bits.
                Inst::Assume { cond } if *cond == d => out.captured = true,
                // A source assert's failure-only payload (`index`/`len`,
                // `required`/`found`) is formatted into the panic message,
                // which observes the operand's bits like the condition does.
                // A v54 sited check passes its run-time location to its panic
                // entry, which reads it: the address is observed there too.
                Inst::Assert { cond, kind, site }
                    if *cond == d
                        || kind.operands().is_some_and(|ops| ops.contains(&d))
                        || site.as_ref().and_then(trust_ir::PanicSite::location_value)
                            == Some(d) =>
                {
                    out.captured = true;
                }
                // A read through a pointer of the seed's provenance sees the
                // allocation's bytes, which hold the address only if it was
                // stored (a capture). A read through a bits or stray pointer
                // is UB unless it lands in a live allocation, and may see a
                // neighbour (or a table) at a location the address decides.
                Inst::Load { .. } | Inst::AtomicLoad { .. } => {
                    out.captured |= fact.escapes();
                    results = None;
                }
                Inst::Store { ptr, value, .. } | Inst::AtomicStore { ptr, value, .. } => {
                    out.captured |= *value == d || (*ptr == d && fact.escapes());
                }
                // A read-modify-write also returns what it read.
                Inst::AtomicRMW { ptr, value, .. } => {
                    out.captured |= *value == d || (*ptr == d && fact.escapes());
                    results = db.then_some(Fact::BITS);
                }
                Inst::CmpXchg {
                    ptr,
                    expected,
                    desired,
                    ..
                } => {
                    out.captured |=
                        *expected == d || *desired == d || (*ptr == d && fact.escapes());
                    results = db.then_some(Fact::BITS);
                }
                Inst::MemCopy {
                    dst, src, bytes, ..
                } => {
                    out.captured |= *bytes == d || ((*dst == d || *src == d) && fact.escapes());
                }
                Inst::MemSet {
                    dst, byte, bytes, ..
                } => {
                    out.captured |= *byte == d || *bytes == d || (*dst == d && fact.escapes());
                }
                // The write-through form stores `value` through the pointer
                // `aggregate`.
                Inst::InsertField {
                    aggregate, value, ..
                } if through(aggregate) => {
                    out.captured |= *value == d || (*aggregate == d && fact.escapes());
                }
                // A fat pointer's data part is the pointer itself.
                Inst::PtrFromParts { data, metadata, .. } if *data == d && *metadata != d => {}
                // A by-value aggregate holds the value; what is extracted
                // from it has no displacement the walk knows. A stray
                // pointer may not hide in one.
                Inst::InsertField { .. }
                | Inst::MakeAggregate { .. }
                | Inst::MakeClosure { .. }
                | Inst::ArraySplat { .. }
                | Inst::PtrFromParts { .. } => {
                    out.captured |= fact.stray;
                    results = Some(if db {
                        Fact::BITS
                    } else {
                        Fact::offset(Disp::Unknown)
                    });
                }
                Inst::Call { callee, args } => {
                    let at: Vec<usize> = (0..args.len()).filter(|&k| args[k] == d).collect();
                    // A callee's facts assume an offset value of the seed's
                    // provenance, and its needs a displacement it can bound.
                    out.captured |= fact.escapes();
                    let mut returned = false;
                    let mut returned_bits = false;
                    let mut identity = true;
                    for &k in &at {
                        let fate = table.fate(*callee, k);
                        out.captured |= fate.captured;
                        for &need in &fate.needs {
                            out.captured |= !bounds.passes(fact.disp, need, args, bi);
                        }
                        returned |= fate.returned;
                        returned_bits |= fate.returned_bits;
                        identity &= fate.identity;
                    }
                    results = returned.then_some(if returned_bits {
                        Fact::BITS
                    } else if identity {
                        fact
                    } else {
                        Fact::offset(Disp::Unknown)
                    });
                }
                Inst::CallIndirect { .. } => out.captured = true,
                Inst::Br { target, args } => edge(target, args, d, &mut params),
                Inst::CondBr {
                    then_target,
                    then_args,
                    else_target,
                    else_args,
                    ..
                } => {
                    edge(then_target, then_args, d, &mut params);
                    edge(else_target, else_args, d, &mut params);
                }
                Inst::Switch {
                    default,
                    default_args,
                    cases,
                    ..
                } => {
                    edge(default, default_args, d, &mut params);
                    for c in cases {
                        edge(&c.target, &c.args, d, &mut params);
                    }
                }
                Inst::Return { values } => {
                    let r = values.contains(&d);
                    // A caller takes a returned pointer for one of the
                    // argument's provenance.
                    out.captured |= r && fact.stray;
                    out.returned |= r;
                    out.returned_bits |= r && db;
                }
                // A `GEP` is UB when its result leaves the address space or
                // an index is negative: of a bits pointer, or by an index
                // derived from the address, that depends on the bits; of a
                // stray pointer, on which allocation it resolved to. An
                // offset pointer moved by an independent amount stays one,
                // of the same provenance.
                Inst::GEP { indices, .. } => {
                    out.captured |= fact.escapes() || indices.contains(&d);
                    results = Some(Fact::offset(Disp::Unknown));
                }
                Inst::Cast {
                    op, src_ty, dst_ty, ..
                } => {
                    out.captured |= cast_is_partial(*op, src_ty);
                    results = Some(if db || !keeps_offset(*op, src_ty, dst_ty) {
                        Fact::BITS
                    } else if is_address_ty(dst_ty) && !is_address_ty(src_ty) {
                        // `inttoptr`: the provenance of the allocation
                        // containing the address.
                        Fact {
                            bits: false,
                            disp: fact.disp,
                            stray: !bounds.resolves(fact.disp, bi),
                        }
                    } else if is_address_ty(src_ty) && !is_address_ty(dst_ty) {
                        Fact::offset(fact.disp)
                    } else {
                        fact
                    });
                }
                Inst::BinOp { op, lhs, rhs, .. } => {
                    // Division by zero, signed overflow of a division and an
                    // out-of-range shift amount are UB.
                    out.captured |= match op {
                        BinOp::UDiv | BinOp::URem => *rhs == d,
                        BinOp::SDiv | BinOp::SRem => true,
                        BinOp::Shl | BinOp::LShr | BinOp::AShr => *rhs == d,
                        _ => false,
                    };
                    let disp = match op {
                        BinOp::Add if *lhs == d && !derived(rhs, &known) => {
                            Some(fact.disp.plus(facts.term(*rhs)))
                        }
                        BinOp::Add if *rhs == d && !derived(lhs, &known) => {
                            Some(fact.disp.plus(facts.term(*lhs)))
                        }
                        BinOp::Sub if *lhs == d && !derived(rhs, &known) => Some(
                            facts
                                .const_of(*rhs)
                                .and_then(|c| i128::try_from(c).ok())
                                .map_or(Disp::Unknown, |c| fact.disp.minus(c)),
                        ),
                        _ => None,
                    };
                    results = Some(match disp {
                        Some(disp) if !db => Fact::offset(disp),
                        _ => Fact::BITS,
                    });
                }
                Inst::ICmp { .. }
                | Inst::FCmp { .. }
                | Inst::UnOp { .. }
                | Inst::Overflow { .. } => {
                    results = Some(Fact::BITS);
                }
                // An `Alloca` whose count depends on the address lays memory
                // out by it.
                Inst::Alloca { .. } => out.captured = true,
                // The read-through forms load a field or element through the
                // pointer, as `Load` does. An element index out of range is
                // UB, so a derived index captures in either form.
                Inst::ExtractField { aggregate, .. } => {
                    if through(aggregate) {
                        out.captured |= fact.escapes();
                        results = None;
                    } else {
                        results = Some(if db {
                            Fact::BITS
                        } else {
                            Fact::offset(Disp::Unknown)
                        });
                    }
                }
                Inst::ExtractElement { array, index, .. } => {
                    out.captured |= *index == d || (through(array) && fact.escapes());
                    results = if through(array) {
                        None
                    } else if db {
                        Some(Fact::BITS)
                    } else {
                        Some(Fact::offset(Disp::Unknown))
                    };
                }
                Inst::InsertElement { index, .. } => {
                    out.captured |= *index == d || fact.stray;
                    results = Some(if db {
                        Fact::BITS
                    } else {
                        Fact::offset(Disp::Unknown)
                    });
                }
                // The metadata of a pointer is not its address.
                Inst::PtrMetadata { .. } => {
                    results = Some(if db {
                        Fact::BITS
                    } else {
                        Fact::offset(Disp::Unknown)
                    });
                }
                Inst::Unreachable
                | Inst::Copy { .. }
                | Inst::Select { .. }
                | Inst::PtrData { .. }
                | Inst::Borrow { .. }
                | Inst::BorrowMut { .. }
                | Inst::EndBorrow { .. }
                | Inst::Fence { .. } => {}
                _ => out.captured = true,
            }
            if out.captured {
                return out;
            }
            if let Some(f) = results {
                for &r in &node.results {
                    add_derived(&mut known, &mut work, &mut out.values, r, f);
                }
            }
            for (ti, p) in params {
                out.param_blocks.push(ti);
                let fact = Fact {
                    disp: facts.carried(fact.disp, ti),
                    ..fact
                };
                add_derived(&mut known, &mut work, &mut out.values, p, fact);
            }
        }
    }
    out.needs = bounds.needs;
    normalize(&mut out.needs);
    out.facts = known;
    out
}

/// Record `v` as derived with fact `f` (joined with what was known), and
/// queue it for a walk when it is new or its fact weakens.
fn add_derived(
    known: &mut HashMap<ValueId, Fact>,
    work: &mut Vec<ValueId>,
    values: &mut Vec<ValueId>,
    v: ValueId,
    f: Fact,
) {
    match known.get(&v).copied() {
        None => {
            known.insert(v, f);
            work.push(v);
            values.push(v);
        }
        Some(old) => {
            let new = old.join(f);
            if new != old {
                known.insert(v, new);
                work.push(v);
            }
        }
    }
}

/// Whether a cast keeps an offset value an offset (module docs): to an
/// address type, or between an address and an integer of at least 32 bits
/// (wasm32 addresses are 32 bits), by a value-preserving cast. A narrowing, a
/// sign extension, a float conversion or a cast to anything else yields bits.
fn keeps_offset(op: CastOp, src_ty: &Ty, dst_ty: &Ty) -> bool {
    let wide = |t: &Ty| {
        is_address_ty(t)
            || matches!(t, Ty::Isize | Ty::Usize)
            || (t.is_integer() && t.bit_width().is_some_and(|w| w >= 32))
    };
    match op {
        CastOp::PtrToInt
        | CastOp::IntToPtr
        | CastOp::PtrToPtr
        | CastOp::Bitcast
        | CastOp::Transmute
        | CastOp::ZExt
        | CastOp::Trunc => wide(src_ty) && wide(dst_ty),
        _ => false,
    }
}

/// Whether a cast of a derived value may be UB for some of its values: a
/// float-to-integer conversion out of range, or an `inttoptr` from an integer
/// wider than a wasm32 address above the address space. Every other cast the
/// lane lowers is total.
fn cast_is_partial(op: CastOp, src_ty: &Ty) -> bool {
    match op {
        CastOp::FPToUI | CastOp::FPToSI => true,
        CastOp::IntToPtr => {
            !matches!(src_ty, Ty::Isize | Ty::Usize) && src_ty.bit_width().is_none_or(|w| w > 32)
        }
        _ => false,
    }
}

/// Whether a value of `ty` is an address (or carries one as its data part).
fn is_address_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr
            | Ty::FatPtr(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::Rc(_)
    )
}

/// A callee whose definition here is the one every call reaches: a body,
/// and a linkage no other definition can replace at link time
/// (`interposable_linkage`, the `_odr` forms included: an equivalent
/// replacement may still keep a pointer argument).
fn analyzable(func: &Function, foreign: &HashSet<FuncId>) -> bool {
    !foreign.contains(&func.id)
        && !is_declaration(func)
        && !interposable_linkage(func.linkage)
        && func.linkage != Linkage::ExternalWeak
}

fn block_index(func: &Function) -> HashMap<BlockId, usize> {
    func.blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.id, i))
        .collect()
}

/// Compute [`ParamCaptures`] for every function defined in `module`, except
/// the `foreign` ones (callees a link may replace). `types_of` types a
/// function's values (`None`: the function derives no facts, so a call to it
/// is a call to an unknown callee).
pub fn param_captures(
    module: &Module,
    foreign: &HashSet<FuncId>,
    types_of: impl Fn(&Function) -> Option<HashMap<ValueId, Ty>>,
) -> ParamCaptures {
    let mut table = ParamCaptures::default();
    for func in &module.functions {
        if is_declaration(func)
            && let Some(fates) = libc_fates(module, func)
        {
            table.by_func.insert(func.id, fates);
        }
    }
    let mut facts: Vec<(FuncFacts<'_>, Vec<ValueId>)> = Vec::new();
    for func in module.functions.iter().filter(|f| analyzable(f, foreign)) {
        let Some(entry) = func.blocks.iter().find(|b| b.id == func.entry) else {
            continue;
        };
        let Some(types) = types_of(func) else {
            continue;
        };
        let params: Vec<ValueId> = entry.params.iter().map(|(v, _)| *v).collect();
        table
            .by_func
            .insert(func.id, vec![ParamFate::default(); params.len()]);
        facts.push((FuncFacts::new(func, block_index(func), types), params));
    }
    let mut round = 0;
    loop {
        round += 1;
        let mut changed = false;
        for (f, params) in &facts {
            for (i, p) in params.iter().enumerate() {
                let known = table.fate(f.func.id, i);
                if known.captured {
                    continue;
                }
                let d = derive(f, &table, Extent::Param, &[*p]);
                let mut needs = known.needs.clone();
                needs.extend(d.needs);
                normalize(&mut needs);
                // The walk stops at the first capture, before it may see a
                // return; a captured argument is treated as returned too.
                let captured = d.captured || needs.len() > MAX_NEEDS;
                let mut fate = if captured {
                    ParamFate::unknown()
                } else {
                    ParamFate {
                        captured: false,
                        returned: known.returned || d.returned,
                        returned_bits: known.returned_bits || d.returned_bits,
                        identity: false,
                        needs,
                    }
                };
                if fate != known {
                    if round > EXACT_ROUNDS {
                        fate = ParamFate::unknown();
                    }
                    if let Some(v) = table.by_func.get_mut(&f.func.id) {
                        v[i] = fate;
                    }
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    table
}

// ---------------------------------------------------------------------------
// Function-shape predicates and dominance, shared with the wasm32 lane
// ---------------------------------------------------------------------------

/// Whether a branch targets the entry block of `func`: only then are the
/// entry's parameters written by this function rather than bound once by the
/// caller.
pub fn entry_reentered(func: &Function) -> bool {
    func.blocks.iter().any(|b| {
        b.body.last().is_some_and(|t| match &t.inst {
            Inst::Br { target, .. } => *target == func.entry,
            Inst::CondBr {
                then_target,
                else_target,
                ..
            } => *then_target == func.entry || *else_target == func.entry,
            Inst::Switch { default, cases, .. } => {
                *default == func.entry || cases.iter().any(|c| c.target == func.entry)
            }
            _ => false,
        })
    })
}

/// A declaration: no body, or an `available_externally` body (one for
/// inlining whose definition is emitted elsewhere; a consumer without an
/// inliner must not emit it as a second definition of the symbol). The
/// native adapter's `is_bodyless_external_declaration` gives the same verdict.
pub fn is_declaration(func: &Function) -> bool {
    func.blocks.is_empty() || func.linkage == Linkage::AvailableExternally
}

/// Whether a definition with this linkage may be replaced at link time by
/// another one (the `_odr` forms included: an equivalent replacement may
/// still keep a pointer argument, or write the C ABI's caller-made copy).
pub fn interposable_linkage(linkage: Linkage) -> bool {
    matches!(
        linkage,
        Linkage::Weak | Linkage::LinkOnce | Linkage::WeakOdr | Linkage::LinkOnceOdr
    )
}

/// The rustc bridge's POINTER-CARRIED aggregate convention, honored exactly
/// as the native adapter honors it (`trust_cg_lower::adapter`,
/// `insert_field_writes_through` / `field_extract_types`): where an aggregate
/// is expected but the operand's actual type is a pointer (or a raw 64-bit
/// address), the operand IS the address of the aggregate's bytes.
pub fn is_pointer_carrier(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::I64 | Ty::U64
    )
}

/// Iterative DFS from `entry` over `succs`: records back-edges (retreating
/// edges whose target is on the current path) and returns a reverse-postorder
/// index (`usize::MAX` for unreachable blocks).
pub fn reverse_postorder(
    succs: &[Vec<usize>],
    entry: usize,
    n: usize,
) -> (Vec<usize>, HashSet<(usize, usize)>) {
    let mut visited = vec![false; n];
    let mut on_path = vec![false; n];
    let mut postorder: Vec<usize> = Vec::new();
    let mut back_edges: HashSet<(usize, usize)> = HashSet::new();

    enum Step {
        Enter(usize),
        Exit(usize),
    }
    let mut stack = vec![Step::Enter(entry)];
    while let Some(step) = stack.pop() {
        match step {
            Step::Enter(u) => {
                if visited[u] {
                    continue;
                }
                visited[u] = true;
                on_path[u] = true;
                stack.push(Step::Exit(u));
                for &v in succs[u].iter().rev() {
                    if on_path[v] {
                        back_edges.insert((u, v));
                    } else if !visited[v] {
                        stack.push(Step::Enter(v));
                    }
                }
            }
            Step::Exit(u) => {
                on_path[u] = false;
                postorder.push(u);
            }
        }
    }

    let mut rpo_index = vec![usize::MAX; n];
    for (pos, &block) in postorder.iter().rev().enumerate() {
        rpo_index[block] = pos;
    }
    (rpo_index, back_edges)
}

/// Cooper-Harvey-Kennedy iterative dominance over reverse-postorder: each
/// reachable block's immediate dominator (`usize::MAX` for unreachable ones;
/// the entry is its own).
pub fn compute_idom(
    preds: &[Vec<usize>],
    rpo_index: &[usize],
    entry: usize,
    n: usize,
) -> Vec<usize> {
    // Reachable blocks in RPO order (excluding entry).
    let mut order: Vec<usize> = (0..n)
        .filter(|&b| b != entry && rpo_index[b] != usize::MAX)
        .collect();
    order.sort_by_key(|&b| rpo_index[b]);

    let undefined = usize::MAX;
    let mut idom = vec![undefined; n];
    idom[entry] = entry;

    let intersect = |mut a: usize, mut b: usize, idom: &[usize]| -> usize {
        while a != b {
            while rpo_index[a] > rpo_index[b] {
                a = idom[a];
            }
            while rpo_index[b] > rpo_index[a] {
                b = idom[b];
            }
        }
        a
    };

    let mut changed = true;
    while changed {
        changed = false;
        for &b in &order {
            let mut new_idom = undefined;
            for &p in &preds[b] {
                if idom[p] == undefined {
                    continue; // not yet processed
                }
                new_idom = if new_idom == undefined {
                    p
                } else {
                    intersect(p, new_idom, &idom)
                };
            }
            if new_idom != undefined && idom[b] != new_idom {
                idom[b] = new_idom;
                changed = true;
            }
        }
    }
    idom
}

/// Does `a` dominate `b` under `idom`? Walk `b`'s idom chain to the entry.
pub fn dominates_in(idom: &[usize], a: usize, b: usize, entry: usize) -> bool {
    let mut cur = b;
    loop {
        if cur == a {
            return true;
        }
        if cur == entry {
            return false;
        }
        let next = idom[cur];
        if next == cur || next == usize::MAX {
            return false;
        }
        cur = next;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(body: &str) -> Module {
        trust_ir::parser::parse_module(&format!(
            "module \"t\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n{body}"
        ))
        .expect("test module parses")
    }

    fn fates(module: &Module, name: &str) -> Vec<ParamFate> {
        let table = param_captures(module, &HashSet::new(), |f| {
            Some(crate::passes::value_types(f))
        });
        let f = module.function_by_name(name).expect("function");
        table.by_func[&f.id].clone()
    }

    /// `p[i]` for `i < len` and `p[len - 1]`, the rustc bridge's checked
    /// indexing: `p` needs `len` bytes, and nothing else happens to it.
    const SLICE: &str = "functy.0 = (ptr, i32, i32) -> (i32)\n\n\
        fn @touch(functy.0) {\n\
        bb0(%0: ptr, %1: i32, %2: i32):\n\
            %3 = icmp ult i32 %2, %1\n\
            condbr %3, bb1, bb3\n\
        bb1:\n\
            %4 = ptrtoint ptr %0 to i32\n\
            %5 = add i32 %4, %2\n\
            %6 = inttoptr i32 %5 to ptr\n\
            %7 = load u8, ptr %6\n\
            %8 = const i32 1\n\
            %9 = sub i32 %1, %8\n\
            %10 = icmp ult i32 %9, %1\n\
            condbr %10, bb2, bb3\n\
        bb2:\n\
            %11 = ptrtoint ptr %0 to i32\n\
            %12 = bitcast i32 %9 to u32\n\
            %13 = zext u32 %12 to u64\n\
            %14 = trunc u64 %13 to i32\n\
            %15 = add i32 %11, %14\n\
            %16 = inttoptr i32 %15 to ptr\n\
            %17 = load u8, ptr %16\n\
            %18 = zext u8 %17 to i32\n\
            ret %18\n\
        bb3:\n\
            unreachable\n\
        }\n";

    #[test]
    fn a_checked_index_asks_the_caller_for_the_length() {
        let fates = fates(&parse(SLICE), "touch");
        assert_eq!(
            fates[0],
            ParamFate {
                needs: vec![Sym {
                    len: Some(1),
                    scale: 1,
                    add: 0
                }],
                ..ParamFate::default()
            }
        );
    }

    /// The same access at `p[len]` (the check bounds another index), with
    /// no check, and before the argument: each may land outside the
    /// argument's allocation.
    #[test]
    fn an_unchecked_or_negative_displacement_captures() {
        for (from, to) in [
            ("%5 = add i32 %4, %2", "%5 = add i32 %4, %1"),
            ("condbr %3, bb1, bb3", "br bb1"),
            ("%5 = add i32 %4, %2", "%5 = sub i32 %4, %8"),
        ] {
            let text = SLICE.replace(from, to);
            assert_ne!(text, SLICE);
            // `%8` must be defined before a use moved ahead of it.
            let text = text.replace(
                "%4 = ptrtoint ptr %0 to i32\n",
                "%4 = ptrtoint ptr %0 to i32\n%80 = const i32 1\n",
            );
            let text = text.replace("i32 %4, %8", "i32 %4, %80");
            assert!(
                fates(&parse(&text), "touch")[0].captured,
                "{to}: the parameter is not captured"
            );
        }
    }

    /// The same check in a function a branch re-enters: the length it checks
    /// may be one the branch rebound, so the check asks no length of the
    /// caller and the access through the rebuilt pointer captures.
    #[test]
    fn a_reentered_entry_block_asks_no_length_of_the_caller() {
        let text = SLICE
            .replace("condbr %3, bb1, bb3", "condbr %3, bb1, bb4")
            .replace(
                "bb3:\n",
                "bb4:\n%40 = const i32 -1\nbr bb0(%0, %40, %2)\nbb3:\n",
            );
        assert_ne!(text, SLICE);
        assert!(fates(&parse(&text), "touch")[0].captured);
    }

    #[test]
    fn needs_keep_the_largest_bound_per_parameter() {
        let mut needs = vec![
            Sym::constant(3),
            Sym {
                len: Some(1),
                scale: 4,
                add: 0,
            },
            Sym::constant(9),
            Sym {
                len: Some(1),
                scale: 4,
                add: 2,
            },
        ];
        normalize(&mut needs);
        assert_eq!(
            needs,
            vec![
                Sym::constant(9),
                Sym {
                    len: Some(1),
                    scale: 4,
                    add: 2
                }
            ]
        );
        // Two parameter terms do not add up to one bound.
        assert!(needs[1].plus(needs[1]).is_none());
        assert_eq!(needs[0].plus(needs[1]).map(|s| s.add), Some(11));
    }

    #[test]
    fn only_the_c_shapes_of_the_bulk_memory_functions_are_trusted() {
        let m = parse(
            "functy.0 = (ptr, i32, usize) -> (ptr)\n\
             functy.1 = (ptr, ptr, usize) -> (ptr)\n\
             functy.2 = (ptr, ptr) -> ()\n\n\
             fn @memset(functy.0) {\n}\n\n\
             fn @memmove(functy.1) {\n}\n\n\
             fn @memcpy(functy.2) {\n}\n",
        );
        let table = param_captures(&m, &HashSet::new(), |f| Some(crate::passes::value_types(f)));
        let id = |n: &str| m.function_by_name(n).expect("function").id;
        assert!(table.fate(id("memset"), 0).identity);
        assert!(!table.fate(id("memset"), 0).captured);
        assert!(table.fate(id("memset"), 1).captured);
        assert!(!table.fate(id("memmove"), 1).captured);
        assert!(!table.fate(id("memmove"), 1).returned);
        // Not memcpy's C shape: an unknown callee.
        assert_eq!(table.fate(id("memcpy"), 0), ParamFate::unknown());
    }
}
