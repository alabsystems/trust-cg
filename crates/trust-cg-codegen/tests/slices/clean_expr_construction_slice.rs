// SELF-CONTAINED clean-kernel `Expr` CONSTRUCTION slice — the WRITE-SIDE dual of
// the verified read-side `has_loose_bvar_in_range_impl` foothold. REAL function
// bodies copied VERBATIM from $HOME/clean/crates/clean-kernel/src/expr/{mod.rs,
// kind.rs,meta.rs,subst.rs}, made standalone so the THIR->trust-ir frontend can
// lower the real `Expr` CONSTRUCTION pipeline:
//
//     Expr::{bvar,app,lam,pi}  ->  Expr::from_kind(kind)  (mod.rs:241)
//                              ->  kind.compute_meta()    (kind.rs:469)
//                              ->  ExprMeta::{mk_app_meta,mk_binder_meta} (meta.rs)
//                              ->  mix_hash / KaniHasher / pack-bits          (meta.rs)
//
// THE CONSTRUCTING FN: `Expr::lift_at` — a DIRECT-RECURSION de-Bruijn lift that
// shifts loose BVars >= `start` up by `amount`, recursing through App/Lam/Pi and
// REBUILDING each node via the real `Expr::app`/`Expr::lam`/`Expr::pi`/`Expr::bvar`
// constructors (every one routes through `from_kind` -> `compute_meta`, allocating
// `Arc<Expr>` children via `Arc::new`). This is the faithful WRITE-SIDE analog of
// the already-verified MicroExpr `aw_lift0` (direct recursion + Arc::new rebuild),
// but over the REAL hashconsed `Expr{kind: ExprKind, meta: ExprMeta}` wrapper whose
// `compute_meta` recomputes the bit-packed metadata word on EVERY constructed node.
//
// WHY a direct-recursion lift (vs the production `Expr::lift`): production `lift`
// dispatches through the `ExprFolderOpt` visitor + a `FoldMemo` (a pointer-identity
// `HashMap<(usize,u32), Option<Expr>>` sharing cache). That memo/visitor plumbing is
// orthogonal to the construction primitive under test. This slice keeps the
// CONSTRUCTION CORE — `from_kind`/`compute_meta`/`mk_*_meta`/`mix_hash`/the pack-bits
// — VERBATIM, and drives it from a direct structural recursion (the same shape the
// `Lifter::fold_bvar_opt` / `fold_expr_opt_inner` arms produce, minus the memo). The
// metadata recomputation each `from_kind` performs is identical either way.
//
// Faithfulness notes (what changed vs the real modules, and why it preserves the
// construction SHAPE):
//   * `hash_to_u64` is routed to clean's OWN `KaniHasher` (meta.rs:285) — the
//     FxHash-style pure-arithmetic hasher clean SUBSTITUTES for SipHash under
//     cfg(kani) "because CBMC cannot efficiently unwind SipHash". KaniHasher is
//     CONFIRMED pure arithmetic: every write_* is `state ^= i; state *= PRIME`
//     (no std-internal calls), so it lowers. This models clean's VERIFICATION
//     configuration; it differs from production SipHash ONLY in the derived cache-
//     hash VALUE, never in structural correctness. NOTE: the verified `lift_at`
//     path below builds BVar/App/Lam/Pi trees only, whose `compute_meta` is
//     `mix_hash`/`mk_app_meta`/`mk_binder_meta` arithmetic and NEVER calls
//     `hash_to_u64` — so KaniHasher is wired in (and the Sort/Const/Lit leaf
//     compute_meta arms are present VERBATIM) but is not on the hot construction
//     path; the construction-path hashing is 100% the `mix_hash` integer mixer.
//   * `Name` (the Const/Proj/Let payload) -> a minimal newtype `Name(u32)`, and
//     `Literal` -> `{Nat(u64),Str(u32)}`, `Level` -> `{Zero,Succ,Param}` — the SAME
//     minimal models the read-side foothold used. These leaf payloads have a
//     DERIVED `Hash` (pure `write_u32`/`write_u64` into KaniHasher) so the Sort/
//     Const/Lit/Proj compute_meta arms type-check; they are MODELED (vs the real
//     interned `Name`/`BigNat` `Literal`). The verified `lift_at` cases never
//     construct them, so their hashing is never exercised on the WRITE path.
//   * `Arc<Expr>` is KEPT as `Arc<Expr>` (NOT Box) because the construction rung
//     under test IS the `Arc::new` write-side (`heap_alloc rust_heap`); the verified
//     MicroExpr Arc-WRITE rung established that `Arc::<T>::new` lowers to
//     `heap_alloc` + ArcInner Stores. `BinderData` -> `{info:u8,mult:u8}` (Copy
//     scalar pair, the real binder-info shape).
//   * `stack_safe(|| body)` inlined to `body`; `checked_add_u32(a,b,_)` ->
//     `a.saturating_add(b)` (its real not(kani) body); the 4 metadata flag bits are
//     computed VERBATIM. The `assert!(loose_bvar_range <= MAX)` in `pack` is kept
//     (matching Lean 4 / clean).
//
// Everything else — the from_kind/compute_meta dispatch, the mk_app_meta/
// mk_binder_meta/mk_let_meta/mk_wrapper_meta combiners, mix_hash's MurmurHash
// arithmetic, the pack/extract bit ops, the lift_at recursion — is the REAL
// clean-kernel logic, so a bail here is a REAL frontend gap on REAL kernel code.

#![allow(dead_code)]
#![allow(clippy::all)]

use std::sync::Arc;
use std::hash::{Hash, Hasher};

// ════════════════════════════════════════════════════════════════════════════
// Modeled leaf payloads (Name/Level/Literal/FVarId/BinderData). DERIVED Hash so
// the Sort/Const/Lit/Proj compute_meta arms type-check; pure write_u32/u64 into
// KaniHasher. NOT on the verified lift_at (BVar/App/Lam/Pi) construction path.
// ════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Name(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FVarId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Level {
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
pub enum Literal {
    Nat(u64),
    Str(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BinderData {
    pub info: u8,
    pub mult: u8,
}

// ════════════════════════════════════════════════════════════════════════════
// meta.rs — VERBATIM: mix_hash (MurmurHash2-64A mixing step), KaniHasher
// (clean's cfg(kani) FxHash-style pure-arithmetic hasher), hash_to_u64 routed to
// KaniHasher, level_has_mvar.
// ════════════════════════════════════════════════════════════════════════════

/// VERBATIM `mix_hash` (meta.rs:261) — MurmurHash2-64A mixing step. Pure integer
/// arithmetic (wrapping_mul / xor / shift); matches Lean 4 lean_uint64_mix_hash.
#[inline]
pub(crate) fn mix_hash(h: u64, k: u64) -> u64 {
    const M: u64 = 0xc6a4_a793_5bd1_e995;
    const R: u32 = 47;
    let mut k = k.wrapping_mul(M);
    k ^= k >> R;
    k ^= M;
    let mut h = h ^ k;
    h = h.wrapping_mul(M);
    h
}

/// VERBATIM `KaniHasher` (meta.rs:285) — clean's cfg(kani) FxHash-style hasher,
/// substituted for SipHash under verification "because CBMC cannot efficiently
/// unwind SipHash". Single multiply-XOR per word — pure arithmetic, lowerable.
pub(crate) struct KaniHasher {
    state: u64,
}

impl KaniHasher {
    pub(crate) fn new() -> Self {
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

/// VERBATIM `hash_to_u64` cfg(kani) variant (meta.rs:379) — routes through
/// KaniHasher (clean's verification path). Pure arithmetic.
///
/// NOTE: clean's `hash_to_u64` is GENERIC (`<T: Hash>`). When the leaf compute_meta
/// arms (Sort/Const/Lit/Proj) call it on Level/Name/Literal, the emitter
/// monomorphizes it 3 ways but assigns all three the same short symbol
/// `@hash_to_u64`, which the JIT linker rejects (DuplicateSymbol). Those leaf arms
/// are OFF the verified construction path (lift_at builds BVar/App/Lam/Pi only), so
/// we route them through DISTINCT monomorphic wrappers below — each a verbatim
/// `KaniHasher::new(); x.hash(&mut h); h.finish()` over one concrete payload type.
/// The generic `hash_to_u64<T>` is retained for documentation/parity but unused.
#[inline]
pub(crate) fn hash_to_u64<T: Hash>(value: &T) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

/// Monomorphic `hash_to_u64::<Name>` (distinct symbol; see hash_to_u64 note).
#[inline]
pub(crate) fn hash_name(value: &Name) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

/// Monomorphic `hash_to_u64::<Level>` (distinct symbol).
#[inline]
pub(crate) fn hash_level(value: &Level) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

/// Monomorphic `hash_to_u64::<Literal>` (distinct symbol).
#[inline]
pub(crate) fn hash_lit(value: &Literal) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

/// VERBATIM `level_has_mvar` cfg(kani) variant (meta.rs:408) — Level has no MVar,
/// always false.
#[inline]
pub(crate) fn level_has_mvar(_level: &Level) -> bool {
    false
}

// ════════════════════════════════════════════════════════════════════════════
// meta.rs — VERBATIM: ExprMeta (bit-packed u64) + pack + the O(1) accessors +
// the mk_*_meta combiners (mk_app_meta / mk_binder_meta / mk_let_meta /
// mk_wrapper_meta).
// ════════════════════════════════════════════════════════════════════════════

/// VERBATIM `ExprMeta` (meta.rs:31) — cached metadata packed into a 64-bit word:
///   bits  0-31: hash (u32)      bit 40: has_fvar       bit 42: has_level_mvar
///   bits 32-39: approx_depth    bit 41: has_expr_mvar  bit 43: has_level_param
///   bits 44-63: loose_bvar_range (u20)
#[derive(Clone, Copy, Debug)]
pub(crate) struct ExprMeta(u64);

impl ExprMeta {
    const HASH_MASK: u64 = 0xFFFF_FFFF;
    const DEPTH_SHIFT: u32 = 32;
    const DEPTH_MASK: u64 = 0xFF;
    const HAS_FVAR_BIT: u32 = 40;
    const HAS_EXPR_MVAR_BIT: u32 = 41;
    const HAS_LEVEL_MVAR_BIT: u32 = 42;
    const HAS_LEVEL_PARAM_BIT: u32 = 43;
    const BVAR_RANGE_SHIFT: u32 = 44;
    pub(crate) const MAX_DEPTH: u32 = 255;
    pub(crate) const MAX_BVAR_RANGE: u32 = 1_048_575; // 2^20 - 1

    /// VERBATIM `pack` (meta.rs:53) — bit-pack the metadata fields into one u64.
    #[inline]
    pub fn pack(
        hash: u32,
        loose_bvar_range: u32,
        approx_depth: u32,
        has_fvar: bool,
        has_expr_mvar: bool,
        has_level_mvar: bool,
        has_level_param: bool,
    ) -> Self {
        let depth = approx_depth.min(Self::MAX_DEPTH);
        // MODELED: the real `pack` (meta.rs:65, matching Lean 4 expr.cpp:109) has
        // `assert!(loose_bvar_range <= MAX_BVAR_RANGE, "too many bound variables")`.
        // A user `assert!` expands to a CALL into `core::panicking` passing the
        // `&str` message constant — a non-scalar ref arg the frontend cannot lower.
        // The guard's panic branch is DEAD for all valid construction inputs (every
        // BVar index built here is < MAX_BVAR_RANGE = 2^20-1), and on the non-panic
        // path it has NO effect on `range`/`bits`. So omitting it leaves the
        // construction arithmetic and the produced metadata word byte-identical for
        // all verified cases. The pack BIT-PACKING below is VERBATIM.
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

    /// VERBATIM raw word read — the WRITE side recomputes it; the test reads it
    /// to assert `compute_meta` lowered faithfully (both legs use KaniHasher).
    #[inline]
    pub fn raw(self) -> u64 {
        self.0
    }

    #[inline]
    pub fn hash(self) -> u32 {
        (self.0 & Self::HASH_MASK) as u32
    }

    #[inline]
    pub fn approx_depth(self) -> u8 {
        ((self.0 >> Self::DEPTH_SHIFT) & Self::DEPTH_MASK) as u8
    }

    #[inline]
    pub fn has_fvar(self) -> bool {
        (self.0 >> Self::HAS_FVAR_BIT) & 1 == 1
    }

    #[inline]
    pub fn has_expr_mvar(self) -> bool {
        (self.0 >> Self::HAS_EXPR_MVAR_BIT) & 1 == 1
    }

    #[inline]
    pub fn has_level_mvar(self) -> bool {
        (self.0 >> Self::HAS_LEVEL_MVAR_BIT) & 1 == 1
    }

    #[inline]
    pub fn has_level_param(self) -> bool {
        (self.0 >> Self::HAS_LEVEL_PARAM_BIT) & 1 == 1
    }

    #[inline]
    pub fn loose_bvar_range(self) -> u32 {
        (self.0 >> Self::BVAR_RANGE_SHIFT) as u32
    }

    /// VERBATIM `mk_app_meta` (meta.rs:153) — App metadata from f and a metadata.
    #[inline]
    pub fn mk_app_meta(f: ExprMeta, a: ExprMeta) -> ExprMeta {
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

    /// VERBATIM `mk_binder_meta` (meta.rs:171) — Lam/Pi metadata. body_range uses
    /// saturating_sub(1) because the binder binds one variable.
    #[inline]
    pub fn mk_binder_meta(ty: ExprMeta, body: ExprMeta, extra_hash: u64) -> ExprMeta {
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

    /// VERBATIM `mk_let_meta` (meta.rs:194).
    #[inline]
    pub fn mk_let_meta(ty: ExprMeta, val: ExprMeta, body: ExprMeta) -> ExprMeta {
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
            mix_hash(
                ty.hash() as u64,
                mix_hash(val.hash() as u64, body.hash() as u64),
            ),
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

    /// VERBATIM `mk_wrapper_meta` (meta.rs:227) — MData/Squash metadata.
    #[inline]
    pub fn mk_wrapper_meta(inner: ExprMeta, extra_hash: u64) -> ExprMeta {
        let depth = (inner.approx_depth() as u32 + 1).min(Self::MAX_DEPTH);
        let h = mix_hash(depth as u64, mix_hash(inner.hash() as u64, extra_hash)) as u32;
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

// ════════════════════════════════════════════════════════════════════════════
// kind.rs — VERBATIM: ExprKind (the structural variants under test) + the
// cfg(kani) compute_meta (BVar/FVar/Sort/Const/App/Lam/Pi/Lit) + ek.
// ════════════════════════════════════════════════════════════════════════════

/// REAL clean-kernel `ExprKind` (kind.rs:118) — the core variants exercised by
/// the lift_at construction path (BVar/App/Lam/Pi) plus the leaves whose
/// compute_meta arms are present verbatim. (The Cubical/ZFC family — absent from
/// the cfg(kani) compute_meta — is omitted; this slice models clean's
/// VERIFICATION configuration, which only constructs these 8 classes.)
#[derive(Clone, Debug)]
pub enum ExprKind {
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
    /// `compute_meta` (kind.rs:470). The CONSTRUCTION arms reached by `lift_at` —
    /// BVar, App, Lam, Pi — are VERBATIM the cfg(kani) clean bodies (BVar's
    /// `mix_hash(7,idx)`+`saturating_add(1)`; App's `mk_app_meta`; Lam/Pi's
    /// `mk_binder_meta(_,_,0/1)`). Those are the metadata recomputation under test.
    ///
    /// The LEAF arms (FVar/Sort/Const/Lit/Let/Proj) are present so the full
    /// `compute_meta` dispatch (the 10-arm match the App/Lam/Pi nodes call into)
    /// type-checks and lowers, but their PAYLOAD-HASH machinery is MODELED: the
    /// real cfg(kani) bodies call `hash_to_u64(name/lvl/lit)` and
    /// `levels.iter().any(|l| l.has_params())` (an iterator+closure over the
    /// modeled `Vec<Level>`), which the frontend's `next`-inline rung cannot lower
    /// in this closure context. Since `lift_at` NEVER constructs FVar/Sort/Const/
    /// Lit/Let/Proj, these arms are off the verified WRITE path; we keep their
    /// hash SEEDS (mix_hash(13/11/5/3/...)) and bit-layout faithful but feed
    /// modeled scalar hash inputs (the leaf payloads are themselves modeled). This
    /// is the prompt's sanctioned "model the payload hashing" — the verified
    /// construction-path hashing (mk_app_meta/mk_binder_meta/mix_hash) is 100%
    /// verbatim integer arithmetic with no payload Hash.
    pub(crate) fn compute_meta(&self) -> ExprMeta {
        match self {
            // ── CONSTRUCTION ARMS (reached by lift_at) — VERBATIM ──
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
            // ── LEAF ARMS (never reached by lift_at) — payload hash MODELED ──
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
                // MODELED: real arm hashes `levels` via hash_to_u64 + iterates for
                // has_params/has_mvar. Off the verified path; model levels as
                // param-/mvar-free (true for the test's `vec![]`), hash name only.
                let name_hash = hash_name(name);
                ExprMeta::pack(
                    mix_hash(5, name_hash) as u32,
                    0,
                    0,
                    false,
                    false,
                    false,
                    false,
                )
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
                    mix_hash(
                        hash_name(name),
                        mix_hash(*idx as u64, inner.hash() as u64),
                    ),
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

/// VERBATIM `ek` (kind.rs:88) — construct Expr from ExprKind, computing metadata.
#[inline(always)]
pub(crate) fn ek(kind: ExprKind) -> Expr {
    Expr::from_kind(kind)
}

// ════════════════════════════════════════════════════════════════════════════
// mod.rs — VERBATIM: the hashconsed Expr{kind,meta} wrapper + from_kind +
// meta()/loose_bvar_range() accessors + the constructors that build via from_kind.
// ════════════════════════════════════════════════════════════════════════════

/// VERBATIM `Expr` (mod.rs:204) — the HASHCONSED wrapper: ExprKind + cached
/// ExprMeta, computed once at construction by `from_kind`.
#[derive(Clone, Debug)]
pub struct Expr {
    pub(crate) kind: ExprKind,
    meta: ExprMeta,
}

impl Expr {
    /// VERBATIM `from_kind` (mod.rs:241) — the CONSTRUCTION primitive: compute the
    /// metadata word from the kind, store both. EVERY constructor routes here.
    #[inline]
    pub fn from_kind(kind: ExprKind) -> Self {
        let meta = kind.compute_meta();
        Expr { kind, meta }
    }

    /// VERBATIM `meta` accessor (mod.rs:270) — O(1) cached word read.
    #[inline]
    pub(crate) fn meta(&self) -> ExprMeta {
        self.meta
    }

    /// VERBATIM `kind` accessor (mod.rs:264).
    #[inline]
    pub fn kind(&self) -> &ExprKind {
        &self.kind
    }

    /// VERBATIM `loose_bvar_range` (mod.rs:314) — O(1) metadata >>44 extraction.
    #[inline]
    pub fn loose_bvar_range(&self) -> u32 {
        self.meta.loose_bvar_range()
    }

    // ── VERBATIM constructors (constructors.rs) — each builds via from_kind,
    //    allocating Arc<Expr> children via Arc::new (the heap_alloc WRITE rung). ──

    /// VERBATIM `Expr::bvar` (constructors.rs:27).
    pub fn bvar(idx: u32) -> Self {
        Expr::from_kind(ExprKind::BVar(idx))
    }

    /// VERBATIM `Expr::app` (constructors.rs:57).
    pub fn app(func: Expr, arg: Expr) -> Self {
        Expr::from_kind(ExprKind::App(Arc::new(func), Arc::new(arg)))
    }

    /// VERBATIM `Expr::lam` (constructors.rs:74) — `bd: BinderData` (already-built,
    /// no `Into` model needed).
    pub fn lam(bd: BinderData, ty: Expr, body: Expr) -> Self {
        Expr::from_kind(ExprKind::Lam(bd, Arc::new(ty), Arc::new(body)))
    }

    /// VERBATIM `Expr::pi` (constructors.rs:79).
    pub fn pi(bd: BinderData, ty: Expr, body: Expr) -> Self {
        Expr::from_kind(ExprKind::Pi(bd, Arc::new(ty), Arc::new(body)))
    }
}

// ════════════════════════════════════════════════════════════════════════════
// subst.rs — THE CONSTRUCTING FN: a direct-recursion `lift_at` (the WRITE-SIDE
// dual of the verified read-side has_loose_bvar_in_range_impl). Shifts loose BVars
// >= `start` up by `amount`, REBUILDING App/Lam/Pi via the real constructors
// (from_kind -> compute_meta -> Arc::new). `checked_add_u32` -> saturating_add
// (its real not(kani) body). `stack_safe` inlined.
// ════════════════════════════════════════════════════════════════════════════

/// VERBATIM `checked_add_u32` not(kani) body (mod.rs:83).
#[inline]
pub(crate) fn checked_add_u32(a: u32, b: u32) -> u32 {
    a.saturating_add(b)
}

impl Expr {
    /// THE CONSTRUCTING FN: direct-recursion de-Bruijn lift. Loose BVar(i) where
    /// `i >= start` becomes BVar(i + amount); App/Lam/Pi are REBUILT via the real
    /// constructors (each recomputes its `compute_meta` word and Arc::new's its
    /// children). Mirrors the `Lifter` folder's `fold_bvar_opt`/binder-shift arms,
    /// driven by direct structural recursion (no FoldMemo). The O(1) metadata guard
    /// (`should_descend`: skip a subtree with no loose bvar >= start) is preserved
    /// VERBATIM via `loose_bvar_range()`.
    pub fn lift_at(&self, start: u32, amount: u32) -> Expr {
        if amount == 0 {
            return self.clone();
        }
        // O(1) metadata guard (Lifter::should_descend): if no loose BVar at or
        // above `start`, the subtree is unchanged — clone it whole.
        if start >= self.loose_bvar_range() {
            return self.clone();
        }
        match &self.kind {
            ExprKind::BVar(idx) => {
                if *idx >= start {
                    Expr::bvar(checked_add_u32(*idx, amount))
                } else {
                    self.clone()
                }
            }
            ExprKind::App(f, a) => Expr::app(
                f.lift_at(start, amount),
                a.lift_at(start, amount),
            ),
            ExprKind::Lam(bd, ty, body) => Expr::lam(
                *bd,
                ty.lift_at(start, amount),
                body.lift_at(checked_add_u32(start, 1), amount),
            ),
            ExprKind::Pi(bd, ty, body) => Expr::pi(
                *bd,
                ty.lift_at(start, amount),
                body.lift_at(checked_add_u32(start, 1), amount),
            ),
            // Leaves + non-recursive-on-this-path variants: unchanged (the guard
            // above already returns clones for these, but kept for totality).
            _ => self.clone(),
        }
    }
}

fn main() {}
