// Reconstructed `clean_expr_slice.rs` — the real kernel `Expr` CONSTRUCTION slice.
//
// This is the VERBATIM clean-kernel construction core (from_kind -> compute_meta ->
// mk_*_meta -> mix_hash + pack), modeling clean's cfg(kani) verification config
// (KaniHasher pure-arithmetic hasher). It already contains the verified READ
// (has_loose_bvar_in_range-style guard via the cached meta `loose_bvar_range`) +
// WRITE (lift_at, the de-Bruijn lift rebuilding App/Lam/Pi via from_kind).
//
// THIS rung ADDS `instantiate_at` — the beta-reduction substitution primitive
// (substitute BVar(depth) with a value, lifting the value's loose BVars under
// inner binders via the verified `lift_at`, decrementing higher BVars). It is the
// direct-recursion CONSTRUCTION form (the analog the production memoized
// `Instantiator`/`ExprFolderOpt` path implements; the caching plumbing is deferred,
// same as `lift_at` defers the production `Lifter` memo). Both `instantiate` (depth
// 0) and `instantiate_at` are the heart of `whnf`'s beta step on `App(Lam(body),arg)`.

#![allow(dead_code)]

use std::hash::Hash;
use std::hash::Hasher;
use std::sync::Arc;

// ── Leaf payload models (never constructed by lift_at / instantiate_at). ──

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Name(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct FVarId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Level {
    Zero,
    Succ(Box<Level>),
    Param(Name),
}

impl Level {
    fn has_params(&self) -> bool {
        match self {
            Level::Zero => false,
            Level::Succ(l) => l.has_params(),
            Level::Param(_) => true,
        }
    }
}

type LevelVec = Vec<Level>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Literal {
    Nat(u64),
    Str(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct BinderData {
    pub info: u8,
    pub mult: u8,
}

// ── mix_hash (MurmurHash2-64A mixing step) — VERBATIM. ──
#[inline]
fn mix_hash(h: u64, k: u64) -> u64 {
    const M: u64 = 0xc6a4_a793_5bd1_e995;
    const R: u32 = 47;
    let mut k = k.wrapping_mul(M);
    k ^= k >> R;
    k ^= M;
    let mut h = h ^ k;
    h = h.wrapping_mul(M);
    h
}

// ── KaniHasher (clean's cfg(kani) FxHash-style pure-arithmetic hasher) — VERBATIM.
//    Only reachable from the (unconstructed) Sort/Const/Lit/Proj leaf arms. ──
struct KaniHasher {
    state: u64,
}
impl KaniHasher {
    fn new() -> Self {
        KaniHasher { state: 0 }
    }
}
impl Hasher for KaniHasher {
    fn finish(&self) -> u64 {
        self.state
    }
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.state = self.state.wrapping_mul(31).wrapping_add(b as u64);
        }
    }
    fn write_u8(&mut self, i: u8) {
        self.state ^= i as u64;
        self.state = self.state.wrapping_mul(0x517cc1b727220a95);
    }
    fn write_u16(&mut self, i: u16) {
        self.state ^= i as u64;
        self.state = self.state.wrapping_mul(0x517cc1b727220a95);
    }
    fn write_u32(&mut self, i: u32) {
        self.state ^= i as u64;
        self.state = self.state.wrapping_mul(0x517cc1b727220a95);
    }
    fn write_u64(&mut self, i: u64) {
        self.state ^= i;
        self.state = self.state.wrapping_mul(0x517cc1b727220a95);
    }
    fn write_u128(&mut self, i: u128) {
        self.write_u64(i as u64);
        self.write_u64((i >> 64) as u64);
    }
    fn write_usize(&mut self, i: usize) {
        self.write_u64(i as u64);
    }
}

// Three monomorphic hash helpers (NOT a generic `hash_to_u64<T>`): each demangles
// to a DISTINCT in-tree name (hash_name/hash_lit/hash_level) so the emitted closure
// module has no duplicate symbol. Only reachable from the unconstructed leaf arms.
#[inline]
fn hash_name(value: &Name) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}
#[inline]
fn hash_lit(value: &Literal) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}
#[inline]
fn hash_level(value: &Level) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[inline]
fn level_has_mvar(_l: &Level) -> bool {
    false
}

// ── ExprMeta (bit-packed u64 @ offset 32 of Expr) — VERBATIM. ──
#[derive(Clone, Copy, Debug)]
struct ExprMeta(u64);

impl ExprMeta {
    const HASH_MASK: u64 = 0xFFFF_FFFF;
    const DEPTH_SHIFT: u32 = 32;
    const DEPTH_MASK: u64 = 0xFF;
    const HAS_FVAR_BIT: u32 = 40;
    const HAS_EXPR_MVAR_BIT: u32 = 41;
    const HAS_LEVEL_MVAR_BIT: u32 = 42;
    const HAS_LEVEL_PARAM_BIT: u32 = 43;
    const BVAR_RANGE_SHIFT: u32 = 44;
    const MAX_DEPTH: u32 = 255;
    const MAX_BVAR_RANGE: u32 = 1_048_575;

    fn pack(
        hash: u32,
        loose_bvar_range: u32,
        approx_depth: u32,
        has_fvar: bool,
        has_expr_mvar: bool,
        has_level_mvar: bool,
        has_level_param: bool,
    ) -> Self {
        let depth = approx_depth.min(Self::MAX_DEPTH);
        let range = loose_bvar_range;
        let bits = (hash as u64)
            | ((depth as u64) << Self::DEPTH_SHIFT)
            | ((has_fvar as u64) << Self::HAS_FVAR_BIT)
            | ((has_expr_mvar as u64) << Self::HAS_EXPR_MVAR_BIT)
            | ((has_level_mvar as u64) << Self::HAS_LEVEL_MVAR_BIT)
            | ((has_level_param as u64) << Self::HAS_LEVEL_PARAM_BIT)
            | ((range as u64) << Self::BVAR_RANGE_SHIFT);
        ExprMeta(bits)
    }
    fn raw(self) -> u64 {
        self.0
    }
    fn hash(self) -> u32 {
        (self.0 & Self::HASH_MASK) as u32
    }
    fn approx_depth(self) -> u8 {
        ((self.0 >> Self::DEPTH_SHIFT) & Self::DEPTH_MASK) as u8
    }
    fn has_fvar(self) -> bool {
        (self.0 >> Self::HAS_FVAR_BIT) & 1 == 1
    }
    fn has_expr_mvar(self) -> bool {
        (self.0 >> Self::HAS_EXPR_MVAR_BIT) & 1 == 1
    }
    fn has_level_mvar(self) -> bool {
        (self.0 >> Self::HAS_LEVEL_MVAR_BIT) & 1 == 1
    }
    fn has_level_param(self) -> bool {
        (self.0 >> Self::HAS_LEVEL_PARAM_BIT) & 1 == 1
    }
    fn loose_bvar_range(self) -> u32 {
        (self.0 >> Self::BVAR_RANGE_SHIFT) as u32
    }

    fn mk_app_meta(f: ExprMeta, a: ExprMeta) -> ExprMeta {
        let depth = (f.approx_depth().max(a.approx_depth()) as u32 + 1).min(Self::MAX_DEPTH);
        let range = f.loose_bvar_range().max(a.loose_bvar_range());
        let h = mix_hash(f.0, a.0) as u32;
        let flags = (f.0 | a.0) & (0xF_u64 << Self::HAS_FVAR_BIT);
        let bits = (h as u64)
            | ((depth as u64) << Self::DEPTH_SHIFT)
            | flags
            | ((range as u64) << Self::BVAR_RANGE_SHIFT);
        ExprMeta(bits)
    }
    fn mk_binder_meta(ty: ExprMeta, body: ExprMeta, extra_hash: u64) -> ExprMeta {
        let depth = (ty.approx_depth().max(body.approx_depth()) as u32 + 1).min(Self::MAX_DEPTH);
        let body_range = body.loose_bvar_range().saturating_sub(1);
        let range = ty.loose_bvar_range().max(body_range);
        let h = mix_hash(
            depth as u64,
            mix_hash(ty.hash() as u64, mix_hash(body.hash() as u64, extra_hash)),
        ) as u32;
        ExprMeta::pack(
            h,
            range,
            depth,
            ty.has_fvar() || body.has_fvar(),
            ty.has_expr_mvar() || body.has_expr_mvar(),
            ty.has_level_mvar() || body.has_level_mvar(),
            ty.has_level_param() || body.has_level_param(),
        )
    }
    fn mk_let_meta(ty: ExprMeta, val: ExprMeta, body: ExprMeta) -> ExprMeta {
        let depth = (ty
            .approx_depth()
            .max(val.approx_depth())
            .max(body.approx_depth()) as u32
            + 1)
        .min(Self::MAX_DEPTH);
        let body_range = body.loose_bvar_range().saturating_sub(1);
        let range = ty
            .loose_bvar_range()
            .max(val.loose_bvar_range())
            .max(body_range);
        let h = mix_hash(
            depth as u64,
            mix_hash(ty.hash() as u64, mix_hash(val.hash() as u64, body.hash() as u64)),
        ) as u32;
        ExprMeta::pack(
            h,
            range,
            depth,
            ty.has_fvar() || val.has_fvar() || body.has_fvar(),
            ty.has_expr_mvar() || val.has_expr_mvar() || body.has_expr_mvar(),
            ty.has_level_mvar() || val.has_level_mvar() || body.has_level_mvar(),
            ty.has_level_param() || val.has_level_param() || body.has_level_param(),
        )
    }
}

#[derive(Clone, Debug)]
enum ExprKind {
    BVar(u32),
    FVar(FVarId),
    Sort(Level),
    Const(Name, LevelVec),
    App(Arc<Expr>, Arc<Expr>),
    Lam(BinderData, Arc<Expr>, Arc<Expr>),
    Pi(BinderData, Arc<Expr>, Arc<Expr>),
    Let(Name, Arc<Expr>, Arc<Expr>, Arc<Expr>, bool),
    Lit(Literal),
    Proj(Name, u32, Arc<Expr>),
}

impl ExprKind {
    fn compute_meta(&self) -> ExprMeta {
        match self {
            ExprKind::BVar(idx) => ExprMeta::pack(
                mix_hash(7, *idx as u64) as u32,
                idx.saturating_add(1),
                0,
                false,
                false,
                false,
                false,
            ),
            ExprKind::App(f, a) => ExprMeta::mk_app_meta(f.meta(), a.meta()),
            ExprKind::Lam(_bi, ty, body) => ExprMeta::mk_binder_meta(ty.meta(), body.meta(), 0),
            ExprKind::Pi(_bi, ty, body) => ExprMeta::mk_binder_meta(ty.meta(), body.meta(), 1),
            ExprKind::FVar(id) => {
                ExprMeta::pack(mix_hash(13, id.0) as u32, 0, 0, true, false, false, false)
            }
            ExprKind::Sort(lvl) => ExprMeta::pack(
                mix_hash(11, hash_level(lvl)) as u32,
                0,
                0,
                false,
                false,
                level_has_mvar(lvl),
                lvl.has_params(),
            ),
            ExprKind::Const(name, _levels) => {
                let name_hash = hash_name(name);
                ExprMeta::pack(mix_hash(5, name_hash) as u32, 0, 0, false, false, false, false)
            }
            ExprKind::Let(_, ty, val, body, _) => {
                ExprMeta::mk_let_meta(ty.meta(), val.meta(), body.meta())
            }
            ExprKind::Lit(lit) => ExprMeta::pack(
                mix_hash(3, hash_lit(lit)) as u32,
                0,
                0,
                false,
                false,
                false,
                false,
            ),
            ExprKind::Proj(name, idx, expr) => {
                let inner = expr.meta();
                let depth = (inner.approx_depth() as u32 + 1).min(255);
                let h = mix_hash(
                    depth as u64,
                    mix_hash(hash_name(name), mix_hash(*idx as u64, inner.hash() as u64)),
                ) as u32;
                ExprMeta::pack(
                    h,
                    inner.loose_bvar_range(),
                    depth,
                    inner.has_fvar(),
                    inner.has_expr_mvar(),
                    inner.has_level_mvar(),
                    inner.has_level_param(),
                )
            }
        }
    }
}

#[derive(Clone, Debug)]
struct Expr {
    kind: ExprKind,
    meta: ExprMeta,
}

impl Expr {
    fn from_kind(kind: ExprKind) -> Self {
        let meta = kind.compute_meta();
        Expr { kind, meta }
    }
    fn meta(&self) -> ExprMeta {
        self.meta
    }
    fn kind(&self) -> &ExprKind {
        &self.kind
    }
    fn loose_bvar_range(&self) -> u32 {
        self.meta.loose_bvar_range()
    }
    fn bvar(idx: u32) -> Self {
        Expr::from_kind(ExprKind::BVar(idx))
    }
    fn app(func: Expr, arg: Expr) -> Self {
        Expr::from_kind(ExprKind::App(Arc::new(func), Arc::new(arg)))
    }
    fn lam(bd: BinderData, ty: Expr, body: Expr) -> Self {
        Expr::from_kind(ExprKind::Lam(bd, Arc::new(ty), Arc::new(body)))
    }
    fn pi(bd: BinderData, ty: Expr, body: Expr) -> Self {
        Expr::from_kind(ExprKind::Pi(bd, Arc::new(ty), Arc::new(body)))
    }
    fn lett(name: Name, ty: Expr, val: Expr, body: Expr, nondep: bool) -> Self {
        Expr::from_kind(ExprKind::Let(
            name,
            Arc::new(ty),
            Arc::new(val),
            Arc::new(body),
            nondep,
        ))
    }
    fn proj(name: Name, idx: u32, e: Expr) -> Self {
        Expr::from_kind(ExprKind::Proj(name, idx, Arc::new(e)))
    }

    // ── VERBATIM lift_at (the verified de-Bruijn lift; WRITE primitive). ──
    fn lift_at(&self, start: u32, amount: u32) -> Expr {
        if amount == 0 {
            return self.clone();
        }
        if start >= self.loose_bvar_range() {
            return self.clone();
        }
        match &self.kind {
            ExprKind::BVar(idx) => {
                if *idx >= start {
                    Expr::bvar(idx.saturating_add(amount))
                } else {
                    self.clone()
                }
            }
            ExprKind::App(f, a) => Expr::app(f.lift_at(start, amount), a.lift_at(start, amount)),
            ExprKind::Lam(bd, ty, body) => Expr::lam(
                *bd,
                ty.lift_at(start, amount),
                body.lift_at(start.saturating_add(1), amount),
            ),
            ExprKind::Pi(bd, ty, body) => Expr::pi(
                *bd,
                ty.lift_at(start, amount),
                body.lift_at(start.saturating_add(1), amount),
            ),
            _ => self.clone(),
        }
    }

    // ── instantiate / instantiate_at — THE BETA SUBSTITUTION PRIMITIVE. ──
    //
    // `instantiate(val)` substitutes BVar(0) with `val` (the beta primitive: what
    // whnf does on `App(Lam(body), arg)`); higher BVars decrement, lower BVars are
    // unchanged. `instantiate_at(val, depth)` generalizes to BVar(depth).
    //
    // This is the DIRECT-RECURSION construction form: under each binder the
    // substitution `depth` increases by 1, so a matching `BVar(depth)` is replaced
    // by the value with its loose BVars LIFTED by `depth` (via the verified
    // `lift_at(0, depth)` — the subtle composition that keeps the value's free
    // variables referring to the right binders), a `BVar(idx>depth)` is decremented
    // to `BVar(idx-1)`, and a `BVar(idx<depth)` is left in place. App/Lam/Pi/Let/Proj
    // are rebuilt via the real constructors (from_kind -> compute_meta). The O(1)
    // `loose_bvar_range` guard short-circuits closed subtrees to a structural clone.
    //
    // Mirrors the production `Instantiator` (ExprFolderOpt) semantics with the
    // pointer-identity `FoldMemo` deferred (same as `lift_at` defers the `Lifter`
    // memo); on a tree the memo is a pure no-op, so the result is byte-identical.
    fn instantiate(&self, val: &Expr) -> Expr {
        self.instantiate_at(val, 0)
    }

    fn instantiate_at(&self, val: &Expr, depth: u32) -> Expr {
        // O(1) metadata guard: no loose BVar at or above `depth` -> nothing to
        // substitute, structural clone. (Lean 4 `instantiate.cpp:16`.)
        if depth >= self.loose_bvar_range() {
            return self.clone();
        }
        match &self.kind {
            ExprKind::BVar(idx) => {
                if *idx == depth {
                    // Hit: substitute the value, lifting its loose BVars by `depth`.
                    val.lift_at(0, depth)
                } else if *idx > depth {
                    // Above the substituted binder: decrement.
                    Expr::bvar(idx.saturating_sub(1))
                } else {
                    // Below `depth`: unchanged.
                    self.clone()
                }
            }
            ExprKind::App(f, a) => {
                Expr::app(f.instantiate_at(val, depth), a.instantiate_at(val, depth))
            }
            ExprKind::Lam(bd, ty, body) => Expr::lam(
                *bd,
                ty.instantiate_at(val, depth),
                body.instantiate_at(val, depth.saturating_add(1)),
            ),
            ExprKind::Pi(bd, ty, body) => Expr::pi(
                *bd,
                ty.instantiate_at(val, depth),
                body.instantiate_at(val, depth.saturating_add(1)),
            ),
            ExprKind::Let(name, ty, val_e, body, nondep) => Expr::lett(
                *name,
                ty.instantiate_at(val, depth),
                val_e.instantiate_at(val, depth),
                body.instantiate_at(val, depth.saturating_add(1)),
                *nondep,
            ),
            ExprKind::Proj(name, idx, e) => {
                Expr::proj(*name, *idx, e.instantiate_at(val, depth))
            }
            _ => self.clone(),
        }
    }
}

// Keep all members reachable from the mono-item roots so the emitter walks them.
// `pub` so mono-collection treats them as entry points (drives instantiate_at +
// lift_at into the mono-item graph). The two "type Expr is more private" warnings
// this raises are inherent to the verification slice (not the frontend build).
pub fn _root_instantiate(e: &Expr, v: &Expr, d: u32) -> Expr {
    e.instantiate_at(v, d)
}
pub fn _root_lift(e: &Expr, s: u32, a: u32) -> Expr {
    e.lift_at(s, a)
}
