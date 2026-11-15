// trust-cg-codegen/wasm/opt/rewrite.rs - segment-local rewrites of the emission pass
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The rewrites the emission pass makes inside straight-line segments, before
//! its colouring, on the lowering's own local index space:
//!
//! 1. **single-use stackify** — a definition `T; local.set t` whose value is
//!    read once, by the next access of `t` in the same segment, is moved to
//!    that read: `T` replaces the `local.get t` and the `local.set` goes.
//!    When the value is read again later (or is live out of the segment) the
//!    read becomes `T; local.tee t`. `T` moves only when it is one contiguous,
//!    self-contained expression tree with no local write in it, and only past
//!    instructions it commutes with: none that writes a local `T` reads, none
//!    of unknown effect, and — when `T` itself has an effect (a load, a call,
//!    a trapping operation, `global.get`) — no effect at all. So a load never
//!    moves past a store, call, trap, `global.set` or `memory.copy`/`fill`,
//!    and the order of effects is unchanged. With the pressure condition on,
//!    a move is also refused when it would raise the pressure at a local
//!    write between the definition and the read above the input's peak for
//!    that type: the pressure at a write is the number of locals of its type
//!    live just after it, a local `T` reads for the last time stays live
//!    from its latest read to the read of `t`, and `t` itself no longer
//!    lives across those writes. The peak is the largest pressure at any
//!    write of that type in the input, a lower bound on the slots of that
//!    type the colouring needs, which the moves therefore do not raise
//!    (V8's Liftoff zero-fills the frame slot of every declared local on each
//!    call once a function declares more than it caches). The pressure is
//!    tracked for the input's own writes; a `local.tee` a move creates is
//!    not counted;
//! 2. **dead definitions** — `T; local.set t` whose value is never read (not
//!    in the segment, not live out of it) loses `T` as well when `T` is pure
//!    (vacuum), and becomes `T; drop` otherwise; `T; drop` of a pure `T` is
//!    deleted, and `local.tee t` of a dead value is deleted;
//! 3. **narrow-canonicalization elimination** — `x; i32.const 2^k-1;
//!    i32.and` with `x` already below `2^k`, and `extend8_s`/`extend16_s`/
//!    `extend32_s` of a value already sign-extended from that width, are
//!    deleted; `x; i32.const 0; i32.add` is `x`;
//! 4. **memarg offset folding** — the address `x + c` of a load or store
//!    (an `i32.add` of a constant) becomes `x` with `c` added to the memarg
//!    offset (while the offset stays a `u32`), when `x`'s fact bounds `x + c`
//!    below `2^32`, or when the addition is the value written to a local
//!    whose single write carries a no-wrap premise (a GEP's address addition,
//!    `trust_cg_verify::wasm_nowrap_premise`; the validator re-checks the
//!    premise's value and order);
//! 5. **small copies inline** — `memory.copy` of a constant `1 <= n <= 32`
//!    bytes between two pure address expressions becomes the run of loads
//!    and stores `trust_cg_verify::wasm_local_tv` validates against it: every
//!    chunk (8, 4, 2 or 1 bytes, highest offset first) is loaded before any is
//!    stored, the chunk that ends at `n` is stored first, and the loaded
//!    values wait in fresh scratch locals.
//!
//! Facts (an unsigned bound, a sign-extension width) come from the same
//! rules the validator applies (`wasm_local_tv::pure_op_facts` and its
//! helpers); a fact of a local across segment boundaries is a CLAIM this
//! module computes over the whole body (the join of every value written to
//! the local where it is live out) and hands to the validator, which assumes
//! it where the local is live in and re-checks it where it is live out. The
//! frame-base local's claim, `base <= 2^32 - 1 - size`, is given only for a
//! function whose prologue guards the new stack pointer (a closed module with
//! a stack limit); the validator re-derives it from that guard.
//!
//! Nothing here is trusted: every rewrite is checked by the per-segment
//! validator against the pre body, and a function it does not accept keeps
//! its baseline body.

use std::collections::{HashMap, HashSet};

use trust_cg_verify::wasm_cfg_proofs::ValKind;
use trust_cg_verify::wasm_local_tv::{
    self as tv, LocalFacts, MAX_EXPANDED_COPY, TvTypes, const_facts, load_facts, pure_op_facts, top,
};

use super::super::encode::{Reloc, ValType, write_uleb128};
use super::super::locals::{self, Kind};
use super::{Body, Liveness, SparseSet, block_liveness};

/// Instructions one function's rewrites may visit (moved trees count each
/// instruction they carry) before the rest of the body is copied as it is.
const MAX_REWRITE_WORK: usize = 1 << 24;
/// Longest expression tree (in instructions) that is moved.
const MAX_TREE: usize = 96;
/// Most distinct locals a moved tree may read.
const MAX_TREE_READS: usize = 8;
/// Longest address expression a small-copy expansion re-evaluates.
const MAX_COPY_ADDR: usize = 4;
/// Changes of one local's claim after which it is widened to nothing.
const CLAIM_WIDEN_AFTER: usize = 3;
/// Passes of the claim analysis; one that has not reached its fixpoint by
/// then claims nothing.
const CLAIM_MAX_ROUNDS: usize = 8;

/// What the rewrites did.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct RewriteStats {
    /// Definitions moved to their single use (or to a `local.tee` there).
    pub stackified: usize,
    /// Of those, the ones that left a `local.tee`.
    pub tees: usize,
    /// Dead definitions deleted with their pure operand, or turned into
    /// `drop`.
    pub dead_defs: usize,
    /// Narrow masks and sign extensions deleted.
    pub masks_removed: usize,
    /// Additions of a constant folded into a memarg offset, or of zero
    /// deleted.
    pub offsets_folded: usize,
    /// `memory.copy`s expanded into loads and stores.
    pub copies_expanded: usize,
    /// Moves rule 1's pressure condition refused.
    pub pressure_kept: usize,
}

impl RewriteStats {
    /// Both rounds' counts.
    pub(crate) fn plus(self, o: RewriteStats) -> RewriteStats {
        RewriteStats {
            stackified: self.stackified + o.stackified,
            tees: self.tees + o.tees,
            dead_defs: self.dead_defs + o.dead_defs,
            masks_removed: self.masks_removed + o.masks_removed,
            offsets_folded: self.offsets_folded + o.offsets_folded,
            copies_expanded: self.copies_expanded + o.copies_expanded,
            pressure_kept: self.pressure_kept + o.pressure_kept,
        }
    }
}

/// The rewritten body (the pre locals plus any scratch locals, in the same
/// index space) and the claimed fact of every pre local.
pub(crate) struct Rewritten {
    pub body: Body,
    pub facts: Vec<LocalFacts>,
    pub stats: RewriteStats,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Class {
    Pure,
    Effect,
    Get(u32),
    Set(u32),
    Tee(u32),
    Drop,
    /// Unknown stack effect or semantics: a barrier.
    Opaque,
    Control,
}

/// One instruction's stack behaviour.
#[derive(Clone, Copy)]
struct Shape {
    class: Class,
    pops: usize,
    pushes: usize,
    result: Option<ValType>,
}

fn kind_of(v: ValType) -> u32 {
    match v {
        ValType::I32 => 32,
        ValType::I64 => 64,
        _ => 0,
    }
}

/// The index of a value type in per-type tables.
fn type_slot(v: ValType) -> usize {
    match v {
        ValType::I32 => 0,
        ValType::I64 => 1,
        ValType::F32 => 2,
        ValType::F64 => 3,
    }
}

fn uleb_at(code: &[u8], mut pos: usize) -> Option<(u64, usize)> {
    let mut v = 0u64;
    let mut shift = 0u32;
    loop {
        let b = *code.get(pos)?;
        pos += 1;
        if shift < 64 {
            v |= u64::from(b & 0x7f) << shift;
        }
        if b & 0x80 == 0 {
            return Some((v, pos));
        }
        shift += 7;
        if shift > 70 {
            return None;
        }
    }
}

fn sleb_at(code: &[u8], mut pos: usize) -> Option<i64> {
    let mut v = 0i64;
    let mut shift = 0u32;
    loop {
        let b = *code.get(pos)?;
        pos += 1;
        if shift < 64 {
            v |= i64::from(b & 0x7f) << shift;
        }
        shift += 7;
        if b & 0x80 == 0 {
            if shift < 64 && b & 0x40 != 0 {
                v |= -1i64 << shift;
            }
            return Some(v);
        }
        if shift > 70 {
            return None;
        }
    }
}

/// The result type and operand count of a numeric opcode, and whether it
/// may trap.
fn numeric(op: u8) -> Option<(usize, ValType, bool)> {
    use ValType::*;
    Some(match op {
        0x45 | 0x50 => (1, I32, false),
        0x46..=0x4f | 0x51..=0x66 => (2, I32, false),
        0x67..=0x69 => (1, I32, false),
        0x6d..=0x70 => (2, I32, true),
        0x6a..=0x78 => (2, I32, false),
        0x79..=0x7b => (1, I64, false),
        0x7f..=0x82 => (2, I64, true),
        0x7c..=0x8a => (2, I64, false),
        0x8b..=0x91 => (1, F32, false),
        0x92..=0x98 => (2, F32, false),
        0x99..=0x9f => (1, F64, false),
        0xa0..=0xa6 => (2, F64, false),
        0xa7 => (1, I32, false),
        0xa8..=0xab => (1, I32, true),
        0xac | 0xad => (1, I64, false),
        0xae..=0xb1 => (1, I64, true),
        0xb2..=0xb6 => (1, F32, false),
        0xb7..=0xbb => (1, F64, false),
        0xbc => (1, I32, false),
        0xbd => (1, I64, false),
        0xbe => (1, F32, false),
        0xbf => (1, F64, false),
        0xc0 | 0xc1 => (1, I32, false),
        0xc2..=0xc4 => (1, I64, false),
        _ => return None,
    })
}

/// A float operation whose NaN result is nondeterministic (as the validator
/// counts them): vacuuming one could misalign the validator's evaluation
/// count of a later identical one, so such trees are dropped, not deleted.
fn nan_nondeterministic(op: u8) -> bool {
    matches!(op, 0x8d..=0x97 | 0x9b..=0xa5 | 0xb6 | 0xbb)
}

fn load_result(op: u8) -> Option<ValType> {
    use ValType::*;
    Some(match op {
        0x28 | 0x2c..=0x2f => I32,
        0x29 | 0x30..=0x35 => I64,
        0x2a => F32,
        0x2b => F64,
        _ => return None,
    })
}

fn val_of(k: ValKind) -> ValType {
    match k {
        ValKind::I32 => ValType::I32,
        ValKind::I64 => ValType::I64,
        ValKind::F32 => ValType::F32,
        ValKind::F64 => ValType::F64,
    }
}

/// The stack behaviour of the instruction at `code[x.start..x.end]`.
fn shape(
    code: &[u8],
    x: &locals::Ins,
    ty: &dyn Fn(u32) -> Option<ValType>,
    types: &dyn TvTypes,
) -> Shape {
    let op = code[x.start];
    let s = |class, pops, pushes, result| Shape {
        class,
        pops,
        pushes,
        result,
    };
    let opaque = s(Class::Opaque, 0, 0, None);
    match x.kind {
        Kind::Get(l) => return s(Class::Get(l), 0, 1, ty(l)),
        Kind::Set(l) => return s(Class::Set(l), 1, 0, None),
        Kind::Tee(l) => return s(Class::Tee(l), 1, 1, ty(l)),
        Kind::Plain => {}
        _ => return s(Class::Control, 0, 0, None),
    }
    match op {
        0x01 => s(Class::Pure, 0, 0, None),
        0x1a => s(Class::Drop, 1, 0, None),
        0x1b => s(Class::Pure, 3, 1, None),
        0x10 => {
            let Some((f, _)) = uleb_at(code, x.start + 1) else {
                return opaque;
            };
            match u32::try_from(f).ok().and_then(|f| types.func(f)) {
                Some(sig) => s(
                    Class::Effect,
                    sig.params.len(),
                    sig.results.len(),
                    (sig.results.len() == 1).then(|| val_of(sig.results[0])),
                ),
                None => opaque,
            }
        }
        0x11 => {
            let Some((t, _)) = uleb_at(code, x.start + 1) else {
                return opaque;
            };
            match u32::try_from(t).ok().and_then(|t| types.type_at(t)) {
                Some(sig) => s(
                    Class::Effect,
                    sig.params.len() + 1,
                    sig.results.len(),
                    (sig.results.len() == 1).then(|| val_of(sig.results[0])),
                ),
                None => opaque,
            }
        }
        0x23 => s(Class::Effect, 0, 1, None),
        0x24 => s(Class::Effect, 1, 0, None),
        0x28..=0x35 => s(Class::Effect, 1, 1, load_result(op)),
        0x36..=0x3e => s(Class::Effect, 2, 0, None),
        0x3f => s(Class::Effect, 0, 1, Some(ValType::I32)),
        0x40 => s(Class::Effect, 1, 1, Some(ValType::I32)),
        0x41 => s(Class::Pure, 0, 1, Some(ValType::I32)),
        0x42 => s(Class::Pure, 0, 1, Some(ValType::I64)),
        0x43 => s(Class::Pure, 0, 1, Some(ValType::F32)),
        0x44 => s(Class::Pure, 0, 1, Some(ValType::F64)),
        0xfc => match uleb_at(code, x.start + 1).map(|(v, _)| v) {
            Some(0..=3) => s(Class::Pure, 1, 1, Some(ValType::I32)),
            Some(4..=7) => s(Class::Pure, 1, 1, Some(ValType::I64)),
            Some(10 | 11) => s(Class::Effect, 3, 0, None),
            _ => opaque,
        },
        _ => match numeric(op) {
            Some((n, r, traps)) => s(
                if traps { Class::Effect } else { Class::Pure },
                n,
                1,
                Some(r),
            ),
            None => opaque,
        },
    }
}

/// One instruction of the output: its bytes in the arena, and the
/// relocations against them (offsets relative to its first byte).
#[derive(Clone)]
struct Out {
    start: usize,
    end: usize,
    relocs: Vec<(u32, Reloc)>,
    alive: bool,
}

/// `x + c` on the stack: the output index of the constant and of the add,
/// the constant, and `x`; `nowrap` once the sum was written to a local whose
/// write carries a no-wrap premise.
#[derive(Clone)]
struct AddConst {
    konst: usize,
    add: usize,
    c: u64,
    x: Box<Val>,
    nowrap: bool,
}

/// A value on the simulated operand stack.
#[derive(Clone)]
struct Val {
    /// First output index of the expression tree that computes it, when that
    /// tree is contiguous, self-contained and writes no local.
    tree: Option<usize>,
    /// Output index just after the instruction that produced it.
    end: usize,
    effects: bool,
    /// The tree evaluates a float operation with a nondeterministic NaN.
    nan: bool,
    reloc: bool,
    reads: Vec<u32>,
    ty: Option<ValType>,
    facts: LocalFacts,
    add: Option<AddConst>,
    /// The value of a single constant instruction without a relocation.
    konst: Option<u64>,
    /// A local that holds this value while it is on the stack (it was read
    /// from or tee'd into that local in this segment, and the instructions
    /// that may still follow it before it is consumed write no local).
    local: Option<u32>,
}

impl Val {
    fn outside() -> Val {
        Val {
            tree: None,
            end: 0,
            effects: true,
            nan: false,
            reloc: false,
            reads: Vec::new(),
            ty: None,
            facts: LocalFacts::NONE,
            add: None,
            konst: None,
            local: None,
        }
    }

    fn remap(&mut self, map: &HashMap<usize, usize>, after: usize) {
        if let Some(t) = self.tree {
            self.tree = map.get(&t).copied();
        }
        self.end = after;
        if let Some(a) = &mut self.add {
            match (map.get(&a.konst), map.get(&a.add)) {
                (Some(&k), Some(&d)) => {
                    a.konst = k;
                    a.add = d;
                    let x_after = a.konst;
                    a.x.remap(map, x_after);
                }
                _ => self.add = None,
            }
        }
    }
}

/// A definition that may still move to its use.
struct Pending {
    start: usize,
    set_at: usize,
    effect_epoch: u64,
    clock: u64,
    val: Val,
}

struct Rewriter<'a> {
    arena: Vec<u8>,
    /// Per local: the clock at its latest read (where a moved tree reads it,
    /// the clock where the tree moved to).
    read_clock: Vec<u64>,
    /// Per input local: its accesses (input index, whether a read), in order.
    accesses: &'a [Vec<(usize, bool)>],
    cfg: &'a locals::Cfg,
    live: &'a Liveness,
    /// The current segment and input instruction.
    block: usize,
    cur: usize,
    /// Per input write: the locals of its type live just after it (itself
    /// included), as moves have changed it so far.
    press: Vec<u32>,
    /// Per value type: the largest `press` of a write of that type in the
    /// input, the pressure no move may exceed.
    peak: [u32; 4],
    /// The input writes kept in the current segment: clock, input index, type.
    seg_writes: Vec<(u64, usize, usize)>,
    /// Whether rule 1's pressure condition applies.
    pressure: bool,
    out: Vec<Out>,
    stack: Vec<Val>,
    pending: HashMap<u32, Pending>,
    effect_epoch: u64,
    clock: u64,
    write_epoch: Vec<u64>,
    /// Facts of the locals written so far in the current segment.
    seg_value: HashMap<u32, LocalFacts>,
    claims: &'a [LocalFacts],
    /// Locals whose single write carries a no-wrap premise.
    nowrap: HashSet<u32>,
    entry: bool,
    params: usize,
    types: Vec<ValType>,
    extra: Vec<ValType>,
    work: usize,
    frozen: bool,
    stats: RewriteStats,
}

impl Rewriter<'_> {
    fn ty(&self, l: u32) -> Option<ValType> {
        self.types.get(l as usize).copied()
    }

    fn local_facts(&self, l: u32) -> LocalFacts {
        if let Some(f) = self.seg_value.get(&l) {
            return *f;
        }
        let w = self.ty(l).map_or(0, kind_of);
        if w == 0 {
            return LocalFacts::NONE;
        }
        if self.entry {
            if (l as usize) < self.params {
                top(w)
            } else {
                const_facts(0, w)
            }
        } else {
            self.claims
                .get(l as usize)
                .copied()
                .unwrap_or(LocalFacts::NONE)
                .meet(top(w))
        }
    }

    /// Whether local `l` is read after the current input instruction before
    /// it is next written (or is live out of the segment unwritten). A local
    /// the input does not have (a scratch local) counts as live.
    fn live_after(&self, l: u32) -> bool {
        let Some(acc) = self.accesses.get(l as usize) else {
            return true;
        };
        let k = acc.partition_point(|&(i, _)| i <= self.cur);
        match acc.get(k) {
            Some(&(i, read)) if self.cfg.block_of[i] == self.block => read,
            _ => self.live.live_out(self.cfg, self.block, l),
        }
    }

    /// The pressure condition of rule 1 (module docs): the change moving
    /// `pd`'s tree to the current read makes to the pressure at every input
    /// write between its definition and that read (`None` when one of them
    /// would exceed its type's peak). A read local `r` the tree reads for
    /// the last time stays live from its latest read up to here; `t` itself
    /// is no longer live across them.
    fn pressure_moves(&self, pd: &Pending) -> Option<Vec<(usize, i64)>> {
        let set_clock = pd.clock + 1;
        let extended: Vec<(u64, usize)> = pd
            .val
            .reads
            .iter()
            .filter(|&&r| !self.live_after(r))
            .filter_map(|&r| {
                let c = *self.read_clock.get(r as usize)?;
                Some((c.max(set_clock), type_slot(self.ty(r)?)))
            })
            .collect();
        let t_ty = pd.val.ty.map(type_slot);
        let mut moves = Vec::new();
        let from = self.seg_writes.partition_point(|&(c, _, _)| c <= set_clock);
        for &(c, i, ty) in &self.seg_writes[from..] {
            let grown = extended
                .iter()
                .filter(|&&(rc, rt)| rt == ty && rc < c)
                .count() as i64;
            let delta = grown - i64::from(t_ty == Some(ty));
            if delta > 0 && i64::from(self.press[i]) + delta > i64::from(self.peak[ty]) {
                return None;
            }
            if delta != 0 {
                moves.push((i, delta));
            }
        }
        Some(moves)
    }

    fn push_out(&mut self, o: Out) -> usize {
        self.out.push(o);
        self.out.len() - 1
    }

    fn synth(&mut self, bytes: &[u8]) -> usize {
        let start = self.arena.len();
        self.arena.extend_from_slice(bytes);
        let end = self.arena.len();
        self.push_out(Out {
            start,
            end,
            relocs: Vec::new(),
            alive: true,
        })
    }

    fn local_op(&mut self, op: u8, l: u32) -> usize {
        let mut b = vec![op];
        write_uleb128(&mut b, u64::from(l));
        self.synth(&b)
    }

    fn kill(&mut self, from: usize, to: usize) {
        for o in &mut self.out[from..to] {
            o.alive = false;
        }
    }

    /// Whether every output instruction in `[a, b)` is deleted.
    fn gap_dead(&self, a: usize, b: usize) -> bool {
        a <= b && b - a <= 32 && self.out[a..b].iter().all(|o| !o.alive)
    }

    fn pop(&mut self) -> Val {
        self.stack.pop().unwrap_or_else(Val::outside)
    }

    fn spend(&mut self, n: usize) {
        self.work = self.work.saturating_add(n);
        if self.work > MAX_REWRITE_WORK {
            self.frozen = true;
            self.pending.clear();
        }
    }

    /// Push the result of the instruction just emitted at `p`, which popped
    /// `args` (bottom first).
    fn push_result(&mut self, p: usize, op: u8, sh: Shape, args: Vec<Val>) {
        if sh.pushes == 0 {
            return;
        }
        if sh.pushes > 1 {
            for _ in 0..sh.pushes {
                self.stack.push(Val::outside());
            }
            return;
        }
        let mut contiguous = args.iter().all(|a| a.tree.is_some());
        let mut start = p;
        if contiguous && !args.is_empty() {
            for w in args.windows(2) {
                contiguous &= self.gap_dead(w[0].end, w[1].tree.unwrap_or(usize::MAX));
            }
            contiguous &= self.gap_dead(args[args.len() - 1].end, p);
            start = args[0].tree.unwrap_or(p);
        }
        let mut reads: Vec<u32> = Vec::new();
        for a in &args {
            for &r in &a.reads {
                if !reads.contains(&r) {
                    reads.push(r);
                }
            }
        }
        if let Class::Get(l) = sh.class
            && !reads.contains(&l)
        {
            reads.push(l);
        }
        let reloc = !self.out[p].relocs.is_empty() || args.iter().any(|a| a.reloc);
        let movable = contiguous
            && matches!(sh.class, Class::Pure | Class::Effect | Class::Get(_))
            && reads.len() <= MAX_TREE_READS
            && p + 1 - start <= MAX_TREE;
        let ty = match op {
            0x1b => args.first().and_then(|a| a.ty),
            _ => sh.result,
        };
        let w = ty.map_or(0, kind_of);
        let facts = if w == 0 {
            LocalFacts::NONE
        } else {
            match sh.class {
                Class::Get(l) => self.local_facts(l),
                _ => self.facts_of(op, &args, w, p),
            }
        };
        let konst = match op {
            0x41 if self.out[p].relocs.is_empty() => {
                sleb_at(&self.arena, self.out[p].start + 1).map(|v| u64::from(v as i32 as u32))
            }
            0x42 if self.out[p].relocs.is_empty() => {
                sleb_at(&self.arena, self.out[p].start + 1).map(|v| v as u64)
            }
            _ => None,
        };
        let add = match (op, args.as_slice()) {
            (0x6a, [x, c]) if c.konst.is_some() && c.tree.is_some() && contiguous => {
                Some(AddConst {
                    konst: c.tree.unwrap_or(p),
                    add: p,
                    c: c.konst.unwrap_or(0),
                    x: Box::new(x.clone()),
                    nowrap: false,
                })
            }
            _ => None,
        };
        self.stack.push(Val {
            tree: movable.then_some(start),
            end: p + 1,
            effects: sh.class == Class::Effect || args.iter().any(|a| a.effects),
            nan: nan_nondeterministic(op) || args.iter().any(|a| a.nan),
            reloc,
            reads,
            ty,
            facts,
            add,
            konst,
            local: match sh.class {
                Class::Get(l) => Some(l),
                _ => None,
            },
        });
    }

    fn facts_of(&self, op: u8, args: &[Val], w: u32, p: usize) -> LocalFacts {
        match op {
            0x41 | 0x42 => {
                if !self.out[p].relocs.is_empty() {
                    return top(w);
                }
                match sleb_at(&self.arena, self.out[p].start + 1) {
                    Some(v) => const_facts(v as u64, w),
                    None => top(w),
                }
            }
            0x28..=0x35 => load_facts(op).map_or(top(w), |f| tv::tighten(f, w)),
            0x45..=0xc4 | 0x1b => {
                let facts: Vec<LocalFacts> = args.iter().map(|a| a.facts).collect();
                let consts: Vec<Option<u64>> = args.iter().map(|a| a.konst).collect();
                pure_op_facts(op, &facts, &consts, w)
            }
            _ => top(w),
        }
    }

    /// Copy instruction `x` of the input as it is.
    fn copy_in(&mut self, x: &locals::Ins, relocs: Vec<(u32, Reloc)>) -> usize {
        self.push_out(Out {
            start: x.start,
            end: x.end,
            relocs,
            alive: true,
        })
    }

    /// The memarg `(align, offset)` of the load or store whose opcode is at
    /// arena byte `start`; `None` for a multi-memory memarg.
    fn memarg(&self, start: usize) -> Option<(u64, u64)> {
        let (align, at) = uleb_at(&self.arena, start + 1)?;
        if align & 0x40 != 0 {
            return None;
        }
        let (offset, _) = uleb_at(&self.arena, at)?;
        Some((align, offset))
    }

    fn mem_op(&mut self, op: u8, align: u64, offset: u64) -> usize {
        let mut b = vec![op];
        write_uleb128(&mut b, align);
        write_uleb128(&mut b, offset);
        self.synth(&b)
    }

    /// Fold `x + c` addresses into `offset` (module docs, rule 4); the
    /// address value is replaced by `x` on success.
    fn fold_address(&mut self, addr: &mut Val, offset: &mut u64) -> bool {
        let mut folded = false;
        while let Some(a) = addr.add.clone() {
            let ok = self.out[a.konst].alive
                && self.out[a.add].alive
                && a.x.ty == Some(ValType::I32)
                && (a.nowrap || a.x.facts.max.saturating_add(a.c) <= u64::from(u32::MAX))
                && offset.saturating_add(a.c) <= u64::from(u32::MAX);
            if !ok {
                break;
            }
            self.out[a.konst].alive = false;
            self.out[a.add].alive = false;
            *offset += a.c;
            let end = addr.end;
            *addr = (*a.x).clone();
            addr.end = end;
            self.stats.offsets_folded += 1;
            folded = true;
        }
        folded
    }

    fn on_get(&mut self, l: u32, more_reads: bool, x: &locals::Ins) {
        if !self.frozen
            && let Some(pd) = self.pending.remove(&l)
        {
            let legal = (!pd.val.effects || self.effect_epoch == pd.effect_epoch)
                && pd
                    .val
                    .reads
                    .iter()
                    .all(|&r| self.write_epoch[r as usize] <= pd.clock)
                && !pd.val.reads.contains(&l);
            let moves = if legal && self.pressure {
                let from = self
                    .seg_writes
                    .partition_point(|&(c, _, _)| c <= pd.clock + 1);
                self.spend(self.seg_writes.len() - from);
                self.pressure_moves(&pd)
            } else {
                Some(Vec::new())
            };
            if legal && moves.is_none() {
                self.stats.pressure_kept += 1;
            }
            if legal && let Some(moves) = moves {
                for (i, d) in moves {
                    self.press[i] = (i64::from(self.press[i]) + d).max(0) as u32;
                }
                let mut map: HashMap<usize, usize> = HashMap::new();
                let moved: Vec<(usize, Out)> = (pd.start..pd.set_at)
                    .filter(|&k| self.out[k].alive)
                    .map(|k| (k, self.out[k].clone()))
                    .collect();
                self.spend(moved.len() + 1);
                self.kill(pd.start, pd.set_at + 1);
                let start = self.out.len();
                for (k, o) in moved {
                    let to = self.push_out(o);
                    map.insert(k, to);
                }
                if pd.val.effects {
                    self.effect_epoch += 1;
                }
                for &r in &pd.val.reads {
                    if let Some(c) = self.read_clock.get_mut(r as usize) {
                        *c = self.clock;
                    }
                }
                let after = self.out.len();
                let mut val = pd.val;
                val.remap(&map, after);
                val.tree = Some(start);
                self.stats.stackified += 1;
                if more_reads {
                    self.local_op(0x22, l);
                    self.clock += 1;
                    self.write_epoch[l as usize] = self.clock;
                    self.seg_value.insert(l, val.facts);
                    self.stats.tees += 1;
                    val.tree = None;
                    val.add = None;
                    val.konst = None;
                    val.local = Some(l);
                    val.end = self.out.len();
                }
                self.stack.push(val);
                return;
            }
        }
        if let Some(c) = self.read_clock.get_mut(l as usize) {
            *c = self.clock;
        }
        let p = self.copy_in(x, Vec::new());
        let sh = Shape {
            class: Class::Get(l),
            pops: 0,
            pushes: 1,
            result: self.ty(l),
        };
        self.push_result(p, 0x20, sh, Vec::new());
    }

    fn on_set(&mut self, l: u32, dead: bool, x: &locals::Ins) {
        let mut v = self.pop();
        if self.nowrap.contains(&l)
            && let Some(a) = &mut v.add
        {
            a.nowrap = true;
        }
        self.pending.remove(&l);
        if dead && !self.frozen {
            let p = self.out.len();
            match v.tree {
                Some(t) if !v.effects && !v.nan && self.gap_dead(v.end, p) => {
                    self.kill(t, p);
                }
                _ => {
                    self.synth(&[0x1a]);
                }
            }
            self.stats.dead_defs += 1;
            return;
        }
        let p = self.copy_in(x, Vec::new());
        let before = self.clock;
        self.clock += 1;
        self.write_epoch[l as usize] = self.clock;
        if let Some(ty) = self.ty(l) {
            self.seg_writes.push((self.clock, self.cur, type_slot(ty)));
        }
        self.seg_value.insert(l, v.facts);
        if !self.frozen
            && let Some(t) = v.tree
            && self.gap_dead(v.end, p)
        {
            self.pending.insert(
                l,
                Pending {
                    start: t,
                    set_at: p,
                    effect_epoch: self.effect_epoch,
                    clock: before,
                    val: v,
                },
            );
        }
    }

    fn on_tee(&mut self, l: u32, dead: bool, x: &locals::Ins) {
        let v = self.pop();
        self.pending.remove(&l);
        if dead && !self.frozen {
            self.stats.dead_defs += 1;
            self.stack.push(v);
            return;
        }
        let p = self.copy_in(x, Vec::new());
        self.clock += 1;
        self.write_epoch[l as usize] = self.clock;
        if let Some(ty) = self.ty(l) {
            self.seg_writes.push((self.clock, self.cur, type_slot(ty)));
        }
        self.seg_value.insert(l, v.facts);
        self.stack.push(Val {
            tree: None,
            end: p + 1,
            effects: true,
            add: None,
            konst: None,
            local: Some(l),
            ..v
        });
    }

    fn on_drop(&mut self, x: &locals::Ins) {
        let v = self.pop();
        let p = self.out.len();
        if !self.frozen
            && let Some(t) = v.tree
            && !v.effects
            && !v.nan
            && self.gap_dead(v.end, p)
        {
            self.kill(t, p);
            self.stats.dead_defs += 1;
            return;
        }
        self.copy_in(x, Vec::new());
    }

    /// Rules 3-5 for the instruction `op`; `true` when it was handled.
    fn peephole(
        &mut self,
        op: u8,
        sub: Option<u64>,
        x: &locals::Ins,
        relocs: &[(u32, Reloc)],
    ) -> bool {
        if self.frozen || !relocs.is_empty() {
            return false;
        }
        let n = self.stack.len();
        match op {
            // x & (2^k - 1) with x already below 2^k; x + 0.
            0x71 | 0x83 | 0x6a | 0x7c if n >= 2 => {
                let (x_val, c) = (&self.stack[n - 2], &self.stack[n - 1]);
                let (Some(m), Some(t)) = (c.konst, c.tree) else {
                    return false;
                };
                if c.end != t + 1 {
                    return false;
                }
                let removable = if matches!(op, 0x71 | 0x83) {
                    m & m.wrapping_add(1) == 0 && x_val.facts.max <= m
                } else {
                    m == 0
                };
                if !removable {
                    return false;
                }
                self.out[t].alive = false;
                self.stack.pop();
                if matches!(op, 0x71 | 0x83) {
                    self.stats.masks_removed += 1;
                } else {
                    self.stats.offsets_folded += 1;
                }
                true
            }
            0xc0..=0xc4 if n >= 1 => {
                let bits = match op {
                    0xc0 | 0xc2 => 8,
                    0xc1 | 0xc3 => 16,
                    _ => 32,
                };
                if self.stack[n - 1].facts.sext > bits {
                    return false;
                }
                self.stats.masks_removed += 1;
                true
            }
            0x28..=0x3e => {
                let at = if op <= 0x35 { 1 } else { 2 };
                if n < at {
                    return false;
                }
                let Some((align, mut offset)) = self.memarg(x.start) else {
                    return false;
                };
                let mut addr = self.stack[n - at].clone();
                if !self.fold_address(&mut addr, &mut offset) {
                    return false;
                }
                self.stack[n - at] = addr;
                let sh = Shape {
                    class: Class::Effect,
                    pops: at,
                    pushes: usize::from(op <= 0x35),
                    result: load_result(op),
                };
                let args: Vec<Val> = self.stack.split_off(n - at);
                let p = self.mem_op(op, align, offset);
                self.effect_epoch += 1;
                self.push_result(p, op, sh, args);
                true
            }
            0xfc if sub == Some(10) && n >= 3 => self.expand_copy(),
            _ => false,
        }
    }

    /// Rule 5 on `[d, s, n]` at the top of the stack. Each address is
    /// re-evaluated by copying its pure expression tree (after folding a
    /// constant addition into the offsets) or by reading the local that holds
    /// it; nothing between the address and the copy writes a local.
    fn expand_copy(&mut self) -> bool {
        let k = self.stack.len();
        let (d, s, len) = (&self.stack[k - 3], &self.stack[k - 2], &self.stack[k - 1]);
        let (Some(n), Some(nt)) = (len.konst, len.tree) else {
            return false;
        };
        let p = self.out.len();
        let start = |v: &Val| v.tree.unwrap_or(v.end - 1);
        let usable = |v: &Val| {
            v.ty == Some(ValType::I32)
                && match v.tree {
                    Some(t) => !v.effects && !v.reloc && v.end - t <= MAX_COPY_ADDR,
                    None => v.local.is_some(),
                }
        };
        if !(1..=MAX_EXPANDED_COPY).contains(&n)
            || len.end != nt + 1
            || !usable(d)
            || !usable(s)
            || !self.gap_dead(d.end, start(s))
            || !self.gap_dead(s.end, nt)
            || !self.gap_dead(len.end, p)
        {
            return false;
        }
        let mut d = d.clone();
        let mut s = s.clone();
        self.out[nt].alive = false;
        let (mut kd, mut ks) = (0u64, 0u64);
        if d.tree.is_some() {
            self.fold_address(&mut d, &mut kd);
        }
        if s.tree.is_some() {
            self.fold_address(&mut s, &mut ks);
        }
        let reeval = |r: &mut Self, v: &Val| -> Vec<Out> {
            match (v.tree, v.local) {
                (Some(t), _) => (t..v.end)
                    .filter(|&i| r.out[i].alive)
                    .map(|i| r.out[i].clone())
                    .collect(),
                (None, Some(l)) => {
                    r.local_op(0x20, l);
                    r.out.pop().into_iter().collect()
                }
                (None, None) => Vec::new(),
            }
        };
        // Never empty: a tree keeps the instruction that produced its value
        // (folding deletes only the constant and the add above it).
        let d_tree = reeval(self, &d);
        let s_tree = reeval(self, &s);
        debug_assert!(!d_tree.is_empty() && !s_tree.is_empty());
        // Chunks, highest offset first.
        let mut chunks: Vec<(u64, u64)> = Vec::new();
        let mut at = 0u64;
        for w in [8u64, 4, 2, 1] {
            while n - at >= w {
                chunks.push((at, w));
                at += w;
            }
        }
        chunks.reverse();
        let load_op = |w: u64| match w {
            8 => 0x29,
            4 => 0x28,
            2 => 0x2f,
            _ => 0x2d,
        };
        let store_op = |w: u64| match w {
            8 => 0x37,
            4 => 0x36,
            2 => 0x3b,
            _ => 0x3a,
        };
        self.stack.truncate(k - 3);
        let first = chunks[0];
        // [d, s] are on the stack, in place: load the end chunk.
        self.mem_op(load_op(first.1), 0, ks + first.0);
        let base = self.types.len() as u32;
        let mut temps = Vec::new();
        for &(o, w) in &chunks[1..] {
            for t in &s_tree {
                self.push_out(t.clone());
            }
            self.mem_op(load_op(w), 0, ks + o);
            let ty = if w == 8 { ValType::I64 } else { ValType::I32 };
            let l = base + self.extra.len() as u32;
            self.extra.push(ty);
            self.local_op(0x21, l);
            temps.push(l);
        }
        self.mem_op(store_op(first.1), 0, kd + first.0);
        for (&(o, w), &l) in chunks[1..].iter().zip(&temps) {
            for t in &d_tree {
                self.push_out(t.clone());
            }
            self.local_op(0x20, l);
            self.mem_op(store_op(w), 0, kd + o);
        }
        self.write_epoch
            .resize(self.types.len() + self.extra.len(), 0);
        self.read_clock
            .resize(self.types.len() + self.extra.len(), 0);
        self.effect_epoch += 1;
        self.stats.copies_expanded += 1;
        self.spend(chunks.len() * (d_tree.len() + s_tree.len() + 4));
        true
    }
}

/// The claimed fact of every pre local (module docs): over the pre body, the
/// join of the facts of the value each segment leaves in a local it is live
/// out of, to a fixpoint (a local whose claim changed [`CLAIM_WIDEN_AFTER`]
/// times claims nothing). `pinned` fixes one local's claim (the guarded
/// frame base); `relocated` marks instructions a relocation patches (a
/// relocated constant is not its encoded value). A local that claims
/// nothing is [`LocalFacts::NONE`].
#[allow(clippy::too_many_arguments)]
fn claims(
    code: &[u8],
    ins: &[locals::Ins],
    relocated: &[bool],
    cfg: &locals::Cfg,
    live: &Liveness,
    types: &[ValType],
    params: usize,
    sigs: &dyn TvTypes,
    pinned: Option<(u32, LocalFacts)>,
) -> Vec<LocalFacts> {
    let n = types.len();
    let width = |l: usize| kind_of(types[l]);
    // Bottom: no value reaches a boundary yet (0 satisfies it).
    let mut claim: Vec<LocalFacts> = (0..n)
        .map(|l| {
            let w = width(l);
            if w == 0 {
                LocalFacts::NONE
            } else {
                const_facts(0, w)
            }
        })
        .collect();
    let mut changes = vec![0usize; n];
    let nb = cfg.first.len();
    // A parameter whose entry value survives the entry segment has no claim.
    let mut written0 = vec![false; n];
    if nb > 0 && !is_control(ins[cfg.first[0]].kind) {
        for x in &ins[cfg.first[0]..=cfg.last[0]] {
            if let Kind::Set(l) | Kind::Tee(l) = x.kind {
                written0[l as usize] = true;
            }
        }
    }
    for p in 0..params.min(n) {
        if !written0[p] && width(p) != 0 && live.live_in(0, p as u32) {
            claim[p] = top(width(p));
        }
    }
    if let Some((l, f)) = pinned
        && (l as usize) < n
    {
        claim[l as usize] = f;
    }
    let ty = |l: u32| types.get(l as usize).copied();
    let mut converged = false;
    for _ in 0..CLAIM_MAX_ROUNDS {
        let mut changed = false;
        for b in 0..nb {
            if is_control(ins[cfg.first[b]].kind) {
                continue;
            }
            let entry = b == 0;
            let mut stack: Vec<(Option<ValType>, LocalFacts, Option<u64>)> = Vec::new();
            let mut cur: HashMap<u32, LocalFacts> = HashMap::new();
            let pop = |s: &mut Vec<(Option<ValType>, LocalFacts, Option<u64>)>| {
                s.pop().unwrap_or((None, LocalFacts::NONE, None))
            };
            for i in cfg.first[b]..=cfg.last[b] {
                let x = &ins[i];
                let sh = shape(code, x, &ty, sigs);
                let op = code[x.start];
                match sh.class {
                    Class::Get(l) => {
                        let w = width(l as usize);
                        let f = if w == 0 {
                            LocalFacts::NONE
                        } else if let Some(f) = cur.get(&l) {
                            *f
                        } else if entry {
                            if (l as usize) < params {
                                top(w)
                            } else {
                                const_facts(0, w)
                            }
                        } else {
                            claim[l as usize].meet(top(w))
                        };
                        stack.push((ty(l), f, None));
                    }
                    Class::Set(l) | Class::Tee(l) => {
                        let v = pop(&mut stack);
                        cur.insert(l, v.1);
                        if matches!(sh.class, Class::Tee(_)) {
                            stack.push(v);
                        }
                    }
                    Class::Drop => {
                        pop(&mut stack);
                    }
                    Class::Opaque => stack.clear(),
                    Class::Control => {}
                    Class::Pure | Class::Effect => {
                        let k = sh.pops.min(stack.len());
                        let mut args: Vec<_> = stack.split_off(stack.len() - k);
                        while args.len() < sh.pops {
                            args.insert(0, (None, LocalFacts::NONE, None));
                        }
                        if sh.pushes != 1 {
                            for _ in 0..sh.pushes {
                                stack.push((None, LocalFacts::NONE, None));
                            }
                            continue;
                        }
                        let rty = if op == 0x1b {
                            args.first().and_then(|a| a.0)
                        } else {
                            sh.result
                        };
                        let w = rty.map_or(0, kind_of);
                        let konst = match op {
                            _ if relocated[i] => None,
                            0x41 => sleb_at(code, x.start + 1).map(|v| u64::from(v as i32 as u32)),
                            0x42 => sleb_at(code, x.start + 1).map(|v| v as u64),
                            _ => None,
                        };
                        let f = if w == 0 {
                            LocalFacts::NONE
                        } else {
                            match op {
                                0x41 | 0x42 => konst.map_or(top(w), |v| const_facts(v, w)),
                                0x28..=0x35 => load_facts(op).map_or(top(w), |f| tv::tighten(f, w)),
                                0x45..=0xc4 | 0x1b => {
                                    let fs: Vec<LocalFacts> = args.iter().map(|a| a.1).collect();
                                    let cs: Vec<Option<u64>> = args.iter().map(|a| a.2).collect();
                                    pure_op_facts(op, &fs, &cs, w)
                                }
                                _ => top(w),
                            }
                        };
                        stack.push((rty, f, konst));
                    }
                }
            }
            for (&l, &f) in &cur {
                let li = l as usize;
                if !live.live_out(cfg, b, l) || pinned.is_some_and(|(p, _)| p == l) {
                    continue;
                }
                let w = width(li);
                if w == 0 {
                    continue;
                }
                let joined = claim[li].join(f);
                if joined != claim[li] {
                    changes[li] += 1;
                    claim[li] = if changes[li] > CLAIM_WIDEN_AFTER {
                        top(w)
                    } else {
                        joined
                    };
                    changed = true;
                }
            }
        }
        if !changed {
            converged = true;
            break;
        }
    }
    for (l, c) in claim.iter_mut().enumerate() {
        let w = width(l);
        if !converged || w == 0 || *c == top(w) {
            *c = LocalFacts::NONE;
        }
    }
    if let Some((l, f)) = pinned
        && (l as usize) < n
    {
        claim[l as usize] = f;
    }
    claim
}

fn is_control(k: Kind) -> bool {
    !matches!(k, Kind::Plain | Kind::Get(_) | Kind::Set(_) | Kind::Tee(_))
}

/// Run rules 1-5 (module docs) over `pre`. `params` are the parameter types;
/// `frame_base` the guarded frame-base local and its bound. `None` when the
/// body cannot be read (the caller then colours `pre` as it is).
pub(crate) fn rewrite(
    params: &[ValType],
    pre: &Body,
    frame_base: Option<(u32, u64)>,
    nowrap: &[u32],
    sigs: &dyn TvTypes,
    pressure: bool,
) -> Option<Rewritten> {
    let (ins, tables) = locals::decode(&pre.code)?;
    if ins.is_empty() {
        return None;
    }
    let cfg = locals::cfg(&ins, &tables)?;
    let mut types: Vec<ValType> = params.to_vec();
    types.extend_from_slice(&pre.declared);
    let n = types.len();
    for x in &ins {
        if let Kind::Get(l) | Kind::Set(l) | Kind::Tee(l) = x.kind
            && l as usize >= n
        {
            return None;
        }
    }
    let mut work = 0usize;
    let live = block_liveness(&ins, &cfg, n, &mut work).ok()?;
    // Relocations by instruction.
    let mut relocs_of: HashMap<usize, Vec<(u32, Reloc)>> = HashMap::new();
    for r in &pre.relocs {
        let at = r.offset as usize;
        let k = ins.partition_point(|x| x.start <= at).checked_sub(1)?;
        if at >= ins[k].end {
            return None;
        }
        relocs_of
            .entry(k)
            .or_default()
            .push(((at - ins[k].start) as u32, *r));
    }
    let pinned = frame_base.map(|(l, max)| (l, LocalFacts { max, sext: 32 }));
    let mut relocated = vec![false; ins.len()];
    for &k in relocs_of.keys() {
        relocated[k] = true;
    }
    let facts = claims(
        &pre.code,
        &ins,
        &relocated,
        &cfg,
        &live,
        &types,
        params.len(),
        sigs,
        pinned,
    );

    // Per instruction: is a `local.get`'s value read again (or live out)
    // before the local is next written; is a write's value never read.
    let m = ins.len();
    let mut more = vec![false; m];
    let mut dead = vec![false; m];
    {
        let mut later: Vec<(u32, bool)> = vec![(u32::MAX, false); n];
        for b in 0..cfg.first.len() {
            let stamp = b as u32;
            for i in (cfg.first[b]..=cfg.last[b]).rev() {
                let read_later = |later: &mut Vec<(u32, bool)>, l: u32| -> bool {
                    let e = later[l as usize];
                    if e.0 == stamp {
                        e.1
                    } else {
                        live.live_out(&cfg, b, l)
                    }
                };
                match ins[i].kind {
                    Kind::Get(l) => {
                        more[i] = read_later(&mut later, l);
                        later[l as usize] = (stamp, true);
                    }
                    Kind::Set(l) | Kind::Tee(l) => {
                        dead[i] = !read_later(&mut later, l);
                        later[l as usize] = (stamp, false);
                    }
                    _ => {}
                }
            }
        }
    }

    let mut accesses: Vec<Vec<(usize, bool)>> = vec![Vec::new(); n];
    for (i, x) in ins.iter().enumerate() {
        match x.kind {
            Kind::Get(l) => accesses[l as usize].push((i, true)),
            Kind::Set(l) | Kind::Tee(l) => accesses[l as usize].push((i, false)),
            _ => {}
        }
    }

    // Pressure at every write: the locals of its type live just after it.
    let mut press = vec![0u32; m];
    let mut peak = [0u32; 4];
    {
        let mut live_now = SparseSet::new(n);
        for b in 0..cfg.first.len() {
            live_now.clear();
            let mut count = [0u32; 4];
            for l in live.live_out_set(&cfg, b) {
                live_now.insert(l);
                count[type_slot(types[l as usize])] += 1;
            }
            for i in (cfg.first[b]..=cfg.last[b]).rev() {
                match ins[i].kind {
                    Kind::Get(l) if !live_now.contains(l) => {
                        live_now.insert(l);
                        count[type_slot(types[l as usize])] += 1;
                    }
                    Kind::Set(l) | Kind::Tee(l) => {
                        let t = type_slot(types[l as usize]);
                        let live_after = live_now.contains(l);
                        let p = count[t] + u32::from(!live_after);
                        press[i] = p;
                        peak[t] = peak[t].max(p);
                        if live_after {
                            live_now.remove(l);
                            count[t] -= 1;
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    let mut r = Rewriter {
        arena: pre.code.clone(),
        press,
        peak,
        seg_writes: Vec::new(),
        pressure,
        read_clock: vec![0; n],
        accesses: &accesses,
        cfg: &cfg,
        live: &live,
        block: 0,
        cur: 0,
        out: Vec::with_capacity(m),
        stack: Vec::new(),
        pending: HashMap::new(),
        effect_epoch: 0,
        clock: 0,
        write_epoch: vec![0; n],
        seg_value: HashMap::new(),
        claims: &facts,
        nowrap: nowrap.iter().copied().collect(),
        entry: true,
        params: params.len(),
        types: types.clone(),
        extra: Vec::new(),
        work: 0,
        frozen: false,
        stats: RewriteStats::default(),
    };
    let ty = |l: u32| types.get(l as usize).copied();
    for b in 0..cfg.first.len() {
        r.stack.clear();
        r.pending.clear();
        r.seg_value.clear();
        r.entry = b == 0;
        r.block = b;
        r.seg_writes.clear();
        for i in cfg.first[b]..=cfg.last[b] {
            let x = &ins[i];
            r.cur = i;
            r.spend(1);
            let relocs = relocs_of.remove(&i).unwrap_or_default();
            let sh = shape(&pre.code, x, &ty, sigs);
            if !relocs.is_empty()
                && !matches!(
                    sh.class,
                    Class::Pure | Class::Effect | Class::Control | Class::Opaque
                )
            {
                return None;
            }
            let op = pre.code[x.start];
            match sh.class {
                Class::Get(l) => r.on_get(l, more[i], x),
                Class::Set(l) => r.on_set(l, dead[i], x),
                Class::Tee(l) => r.on_tee(l, dead[i], x),
                Class::Drop => r.on_drop(x),
                Class::Control => {
                    r.copy_in(x, relocs);
                }
                Class::Opaque => {
                    r.copy_in(x, relocs);
                    r.stack.clear();
                    r.pending.clear();
                    r.effect_epoch += 1;
                }
                Class::Pure | Class::Effect => {
                    let sub = (op == 0xfc)
                        .then(|| uleb_at(&pre.code, x.start + 1).map(|v| v.0))
                        .flatten();
                    if r.peephole(op, sub, x, &relocs) {
                        continue;
                    }
                    let k = sh.pops.min(r.stack.len());
                    let mut args = r.stack.split_off(r.stack.len() - k);
                    while args.len() < sh.pops {
                        args.insert(0, Val::outside());
                    }
                    let p = r.copy_in(x, relocs);
                    if sh.class == Class::Effect {
                        r.effect_epoch += 1;
                    }
                    r.push_result(p, op, sh, args);
                }
            }
        }
    }

    let mut code = Vec::with_capacity(pre.code.len());
    let mut relocs = Vec::with_capacity(pre.relocs.len());
    for o in r.out.iter().filter(|o| o.alive) {
        let at = code.len();
        code.extend_from_slice(&r.arena[o.start..o.end]);
        for (rel, rel_r) in &o.relocs {
            relocs.push(Reloc {
                offset: u32::try_from(at).ok()? + rel,
                ..*rel_r
            });
        }
    }
    let mut declared = pre.declared.clone();
    declared.extend_from_slice(&r.extra);
    Some(Rewritten {
        body: Body {
            declared,
            code,
            relocs,
        },
        facts: facts[..n].to_vec(),
        stats: r.stats,
    })
}
