// SELF-CONTAINED clean-kernel real-`Expr` QUOTIENT AXIOM-TYPE builders — the REAL
// function bodies mirrored VERBATIM from $HOME/clean/crates/clean-kernel/src/quot.rs:
//   quot_type / quot_mk_type / quot_lift_type (+build_lift_proof_type +make_eq_type)
//   / quot_ind_type (+build_ind_hyp_type) / quot_sound_type.
// These construct the *types* of the five built-in quotient primitives that the
// kernel admits as AXIOMS when a development uses `Quot`:
//     Quot.{u}       : {α : Sort u} → (α → α → Prop) → Sort u
//     Quot.mk.{u}    : {α : Sort u} → (r : α → α → Prop) → (a : α) → @Quot α r
//     Quot.lift.{u v}: {α}{r}{β} → (f : α → β) → (∀ a b, r a b → f a = f b) → @Quot α r → β
//     Quot.ind.{u}   : {α}{r}{β : @Quot α r → Prop} → (∀ a, β (Quot.mk α r a)) → ∀ q, β q
//     Quot.sound.{u} : {α}{r}{a b : α} → r a b → @Quot.mk α r a = @Quot.mk α r b
//
// WHY SOUNDNESS-CRITICAL: these axiom types ARE the trusted interface to the
// quotient primitives — the kernel never *proves* them, it *asserts* them. A wrong
// de-Bruijn index or a wrong head in any of these builders installs an axiom with
// the WRONG type into the environment, and the whole proof development then type-
// checks against a lie. The in-source SOUNDNESS comments on quot_lift_type /
// build_lift_proof_type / quot_ind_type record exactly such off-by-one bugs (the
// codomain β vs the lifting function f, and the motive β vs the hypothesis h) that
// were previously latent. These builders are therefore the definitional core of the
// quotient primitive, distinct from the ALREADY-VERIFIED Quot.lift *whnf reduction*
// (try_quot_lift_reduction) — that verified the ι/computation RULE; this verifies
// the TYPE CONSTRUCTION of the axioms themselves.
//
// PILLARS COMPOSED (each already native==JIT in prior mir_real_expr_* milestones):
//   Expr::from_kind → ExprKind::compute_meta → ExprMeta::{pack,mk_app_meta,
//   mk_binder_meta} → mix_hash (the CONSTRUCTION + meta core, verified in
//   mir_real_expr_construction_roundtrip / build_recursor_type), plus the real
//   Expr::{pi,app,bvar,const_,sort,prop} constructors and Arc::new children.
//
// Faithfulness notes (what changed vs the real quot.rs, and why it preserves the
// LOWERED SHAPE the verification measures):
//   * `Arc<Expr>` kept as `std::sync::Arc<Expr>` (the real recursive child).
//   * `Name` -> a `u32` newtype: the real `names::QUOT`/`QUOT_MK`/`"Eq"` are
//     interned `Name`s compared by identity; MODELED as distinct u32 raws passed
//     by the root, so `Name`-equality and the name-hash into compute_meta are the
//     same integer mixing the real fn drives.
//   * `Level` trimmed to Zero/Succ/Param (Max/IMax unused by these builders, which
//     only ever build `Sort(Param u)`, `Sort(Param v)`, `prop()`=`Sort(Zero)`, and
//     `Const(_, [Param u])` / `[Param v]`).
//   * `BinderInfo::Default`/`Implicit` -> the real `BinderData{info,mult}` scalar
//     (Default=>{0,0}, Implicit=>{1,0}) the real `Expr::pi(bi, ..)` stores after the
//     `Into` conversion — the frontend lowers this as a runtime aggregate.
//   * `Name::from_string("Eq")` / `names::QUOT` etc. -> u32 raws (EQ/QUOT/QUOT_MK)
//     threaded in by the root; the real fns call `.clone()` on interned Names, which
//     is a Copy of the same handle.
// Everything else (every Pi/App/BVar/Const/Sort node, every de-Bruijn index, the
// nesting, the helper decomposition) is the REAL clean-kernel logic, so a bail here
// is a REAL frontend gap on the REAL quotient axiom-type builders.

#![allow(dead_code)]
#![allow(clippy::all)]
#![allow(unused_variables)]

use std::sync::Arc;
use std::hash::{Hash, Hasher};

// ════════════════════════════════════════════════════════════════════════════
// Modeled leaf payloads (Name/Level/Literal/FVarId/BinderData). VERBATIM the
// verified construction slice.
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

// BinderInfo::Default / Implicit modeled as the real `bd.info` byte (Default=0,
// Implicit=1). infer_implicit only ever compares against Default and constructs
// Implicit, so the two-variant model is faithful.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BinderData {
    pub info: u8,
    pub mult: u8,
}

impl BinderData {
    // VERBATIM `BinderData::new(info, mult)` (expr/types.rs:131).
    #[inline]
    fn new(info: u8, mult: u8) -> Self {
        BinderData { info, mult }
    }
}

// BinderInfo::Default / Implicit -> the scalar BinderData the real constructor stores.
// Built as RUNTIME locals (NOT `const` items): the real `Expr::pi(BinderInfo::Default,..)`
// passes a freshly-`Into`-converted `BinderData`, and the frontend lowers a struct-adt
// only as a runtime aggregate. These `#[inline]` fns return the same scalar pair as
// `BinderInfo::Default.into()` / `::Implicit.into()`.
#[inline]
fn bi_default() -> BinderData {
    BinderData { info: 0, mult: 0 }
}
#[inline]
fn bi_implicit() -> BinderData {
    BinderData { info: 1, mult: 0 }
}
// `BinderInfo::Default` used as a comparison value in infer_implicit / has_loose_bvars_in_domain.
const INFO_DEFAULT: u8 = 0;

// ════════════════════════════════════════════════════════════════════════════
// meta.rs — VERBATIM mix_hash / KaniHasher / hash_to_u64 / level_has_mvar.
// ════════════════════════════════════════════════════════════════════════════

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

#[inline]
pub(crate) fn hash_to_u64<T: Hash>(value: &T) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[inline]
pub(crate) fn hash_name(value: &Name) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[inline]
pub(crate) fn hash_level(value: &Level) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[inline]
pub(crate) fn hash_lit(value: &Literal) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[inline]
pub(crate) fn level_has_mvar(_level: &Level) -> bool {
    false
}

// ════════════════════════════════════════════════════════════════════════════
// meta.rs — VERBATIM ExprMeta (bit-packed u64) + pack + accessors + mk_*_meta.
// ════════════════════════════════════════════════════════════════════════════

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
    pub(crate) const MAX_BVAR_RANGE: u32 = 1_048_575;

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
// kind.rs — VERBATIM ExprKind + cfg(kani) compute_meta.
// ════════════════════════════════════════════════════════════════════════════

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
    pub(crate) fn compute_meta(&self) -> ExprMeta {
        match self {
            // ── CONSTRUCTION ARMS (reached by build_recursor_type) — VERBATIM ──
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
                // VERBATIM the real `levels.iter().any(|l| l.has_params())` — lowered to
                // the equivalent explicit loop. True iff any level is a Param; keeps the
                // has_level_param meta bit faithful for the Const(I/ctor, [Param(u)..]) nodes.
                let mut has_param = false;
                {
                    let mut _li = 0usize;
                    while _li < _levels.len() {
                        if _levels[_li].has_params() {
                            has_param = true;
                        }
                        _li += 1;
                    }
                }
                ExprMeta::pack(
                    mix_hash(5, name_hash) as u32,
                    0,
                    0,
                    false,
                    false,
                    false,
                    has_param,
                )
            }
            // ── LEAF ARMS (off this fn's construction path) — payload hash MODELED ──
            ExprKind::FVar(id) => {
                ExprMeta::pack(mix_hash(13, id.0) as u32, 0, 0, true, false, false, false)
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

// ════════════════════════════════════════════════════════════════════════════
// mod.rs — VERBATIM Expr{kind,meta} + from_kind + accessors + constructors.
// ════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Debug)]
pub struct Expr {
    pub(crate) kind: ExprKind,
    pub(crate) meta: ExprMeta,
}

impl Expr {
    #[inline]
    pub fn from_kind(kind: ExprKind) -> Self {
        let meta = kind.compute_meta();
        Expr { kind, meta }
    }
    #[inline]
    pub(crate) fn meta(&self) -> ExprMeta {
        self.meta
    }
    #[inline]
    pub fn kind(&self) -> &ExprKind {
        &self.kind
    }
    #[inline]
    pub fn loose_bvar_range(&self) -> u32 {
        self.meta.loose_bvar_range()
    }

    // ── VERBATIM constructors (each builds via from_kind, Arc::new children). ──
    pub fn bvar(idx: u32) -> Self {
        Expr::from_kind(ExprKind::BVar(idx))
    }
    pub fn const_(name: Name, levels: LevelVec) -> Self {
        Expr::from_kind(ExprKind::Const(name, levels))
    }
    pub fn sort(level: Level) -> Self {
        Expr::from_kind(ExprKind::Sort(level))
    }
    pub fn app(func: Expr, arg: Expr) -> Self {
        Expr::from_kind(ExprKind::App(Arc::new(func), Arc::new(arg)))
    }
    pub fn lam(bd: BinderData, ty: Expr, body: Expr) -> Self {
        Expr::from_kind(ExprKind::Lam(bd, Arc::new(ty), Arc::new(body)))
    }
    pub fn pi(bd: BinderData, ty: Expr, body: Expr) -> Self {
        Expr::from_kind(ExprKind::Pi(bd, Arc::new(ty), Arc::new(body)))
    }
}

// ════════════════════════════════════════════════════════════════════════════
// quot.rs helpers the builders need on top of the construction core.
//   * Expr::prop() = from_kind(Sort(Level::zero()))  (constructors.rs:42)  VERBATIM
//   * Level::param(name) = Level::Param(name)         (level/mod.rs:357)   VERBATIM
// BinderInfo::Default / Implicit are the `bi_default()` / `bi_implicit()` scalars
// already defined in the core (the exact `BinderData` the real Expr::pi stores).
// ════════════════════════════════════════════════════════════════════════════

impl Level {
    // VERBATIM `Level::param` (level/mod.rs:357).
    #[inline]
    fn param(name: Name) -> Level {
        Level::Param(name)
    }
    // VERBATIM `Level::zero` (used by Expr::prop).
    #[inline]
    fn zero() -> Level {
        Level::Zero
    }
}

impl Expr {
    // VERBATIM `Expr::prop` (constructors.rs:42): Prop = Sort 0.
    #[inline]
    fn prop() -> Expr {
        Expr::from_kind(ExprKind::Sort(Level::zero()))
    }
}

// The interned quotient / Eq Names, MODELED as distinct u32 raws (threaded by the
// root). The real fns clone `names::QUOT` / `names::QUOT_MK` / `Name::from_string("Eq")`.
#[derive(Clone, Copy)]
struct QuotNames {
    quot: Name,    // names::QUOT
    quot_mk: Name, // names::QUOT_MK
    eq: Name,      // Name::from_string("Eq")
}

// ════════════════════════════════════════════════════════════════════════════
// quot.rs — VERBATIM axiom-type builders. Only the interned-Name literals are
// parameterised (passed via `qn`); the control flow + every de-Bruijn index +
// every node is byte-for-byte the real quot.rs source.
// ════════════════════════════════════════════════════════════════════════════

// VERBATIM `quot_type` (quot.rs:97).
// `Quot.{u} : {α : Sort u} → (r : α → α → Prop) → Sort u`
fn quot_type(u: &Name) -> Expr {
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
    // {α : Sort u}
    let alpha = Expr::bvar(0);
    // r : α → α → Prop
    let r_type = Expr::pi(
        bi_default(),
        alpha.clone(),
        Expr::pi(bi_default(), Expr::bvar(1), Expr::prop()),
    );
    // The result type: Sort u
    let result = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));

    // Build: {α : Sort u} → (r : α → α → Prop) → Sort u
    Expr::pi(
        bi_implicit(),
        sort_u,
        Expr::pi(bi_default(), r_type, result),
    )
}

// VERBATIM `quot_mk_type` (quot.rs:126).
// `Quot.mk.{u} : {α : Sort u} → (r : α → α → Prop) → (a : α) → @Quot.{u} α r`
fn quot_mk_type(u: &Name, qn: &QuotNames) -> Expr {
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));

    // r : α → α → Prop (α is BVar 0 at this point)
    let r_type = Expr::pi(
        bi_default(),
        Expr::bvar(0), // α
        Expr::pi(bi_default(), Expr::bvar(1), Expr::prop()),
    );

    // Build @Quot.{u} α r where α is BVar 2, r is BVar 1
    let quot_app = Expr::app(
        Expr::app(
            Expr::const_(qn.quot.clone(), vec![Level::param(u.clone())]),
            Expr::bvar(2), // α
        ),
        Expr::bvar(1), // r
    );

    // Build: {α : Sort u} → (r : α → α → Prop) → (a : α) → @Quot.{u} α r
    Expr::pi(
        bi_implicit(),
        sort_u,
        Expr::pi(
            bi_default(),
            r_type,
            Expr::pi(
                bi_default(),
                Expr::bvar(1), // a : α (α is now BVar 1)
                quot_app,
            ),
        ),
    )
}

// VERBATIM `quot_lift_type` (quot.rs:174).
// `Quot.lift.{u v} : {α}{r}{β} → (f : α → β) → (∀ a b, r a b → f a = f b) → @Quot α r → β`
fn quot_lift_type(u: &Name, v: &Name, qn: &QuotNames) -> Expr {
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
    let sort_v = Expr::from_kind(ExprKind::Sort(Level::param(v.clone())));

    // r : α → α → Prop (α is BVar 0 at this point)
    let r_type = Expr::pi(
        bi_default(),
        Expr::bvar(0), // α
        Expr::pi(bi_default(), Expr::bvar(1), Expr::prop()),
    );

    // After binding α, r, β: α is BVar 2, r is BVar 1, β is BVar 0
    // f : α → β
    let f_type = Expr::pi(bi_default(), Expr::bvar(2), Expr::bvar(1));

    // Build the proof obligation type: ∀ a b : α, r a b → f a = f b
    let proof_type = build_lift_proof_type(Level::param(v.clone()), qn);

    // @Quot.{u} α r  (after all bindings: α is BVar 4, r is BVar 3)
    let quot_type_app = Expr::app(
        Expr::app(
            Expr::const_(qn.quot.clone(), vec![Level::param(u.clone())]),
            Expr::bvar(4), // α
        ),
        Expr::bvar(3), // r
    );

    // Result type: β (BVar 3 from the inside — see the SOUNDNESS note in quot.rs).
    let result = Expr::bvar(3);

    // Build the full type with all binders
    Expr::pi(
        bi_implicit(),
        sort_u, // α : Sort u
        Expr::pi(
            bi_implicit(),
            r_type, // r : α → α → Prop
            Expr::pi(
                bi_implicit(),
                sort_v, // β : Sort v
                Expr::pi(
                    bi_default(),
                    f_type, // f : α → β
                    Expr::pi(
                        bi_default(),
                        proof_type, // proof : ∀ a b, r a b → f a = f b
                        Expr::pi(
                            bi_default(),
                            quot_type_app, // q : @Quot α r
                            result,        // β
                        ),
                    ),
                ),
            ),
        ),
    )
}

// VERBATIM `build_lift_proof_type` (quot.rs:247).
// `∀ a b : α, r a b → @Eq.{v} β (f a) (f b)`
fn build_lift_proof_type(level_v: Level, qn: &QuotNames) -> Expr {
    // α at BVar 3
    let alpha = Expr::bvar(3);
    // r at BVar 2 (used in the body after binding)
    let _r = Expr::bvar(2);
    // f at BVar 0 (used in the body after binding)
    let _f = Expr::bvar(0);

    // After binding a, b: r a b
    let r_a_b = Expr::app(Expr::app(Expr::bvar(4), Expr::bvar(1)), Expr::bvar(0));

    // f a, f b (f becomes BVar 3 after binding a, b, h)
    let f_a = Expr::app(Expr::bvar(3), Expr::bvar(2));
    let f_b = Expr::app(Expr::bvar(3), Expr::bvar(1));

    // @Eq.{v} β (f a) (f b)   (β is BVar 4 here — see SOUNDNESS note in quot.rs).
    let eq_type = make_eq_type(level_v, Expr::bvar(4), f_a, f_b, qn);

    // Build: ∀ a b : α, r a b → f a = f b
    Expr::pi(
        bi_default(),
        alpha.clone(), // a : α
        Expr::pi(
            bi_default(),
            Expr::bvar(4), // b : α (α shifted by 1)
            Expr::pi(
                bi_default(),
                r_a_b,   // h : r a b
                eq_type, // f a = f b
            ),
        ),
    )
}

// VERBATIM `make_eq_type` (quot.rs:298).
// `@Eq.{v} β a b`
fn make_eq_type(level_v: Level, beta: Expr, a: Expr, b: Expr, qn: &QuotNames) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(qn.eq.clone(), vec![level_v]), beta),
            a,
        ),
        b,
    )
}

// VERBATIM `quot_ind_type` (quot.rs:321).
// `Quot.ind.{u} : {α}{r}{β : @Quot α r → Prop} → (∀ a, β (Quot.mk α r a)) → ∀ q, β q`
fn quot_ind_type(u: &Name, qn: &QuotNames) -> Expr {
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));

    // r : α → α → Prop
    let r_type = Expr::pi(
        bi_default(),
        Expr::bvar(0),
        Expr::pi(bi_default(), Expr::bvar(1), Expr::prop()),
    );

    // @Quot.{u} α r (after binding α, r): α is BVar 1, r is BVar 0
    let quot_alpha_r = Expr::app(
        Expr::app(
            Expr::const_(qn.quot.clone(), vec![Level::param(u.clone())]),
            Expr::bvar(1),
        ),
        Expr::bvar(0),
    );

    // β : @Quot.{u} α r → Prop
    let beta_type = Expr::pi(bi_default(), quot_alpha_r.clone(), Expr::prop());

    // ∀ a : α, β (@Quot.mk.{u} α r a)
    let ih_type = build_ind_hyp_type(u, qn);

    // @Quot.{u} α r for the final argument (α is BVar 3, r is BVar 2)
    let quot_final = Expr::app(
        Expr::app(
            Expr::const_(qn.quot.clone(), vec![Level::param(u.clone())]),
            Expr::bvar(3),
        ),
        Expr::bvar(2),
    );

    // β q (β is BVar 2 from the inside, q is BVar 0 — see SOUNDNESS note in quot.rs).
    let beta_q = Expr::app(Expr::bvar(2), Expr::bvar(0));

    // Build the full type
    Expr::pi(
        bi_implicit(),
        sort_u,
        Expr::pi(
            bi_implicit(),
            r_type,
            Expr::pi(
                bi_implicit(),
                beta_type,
                Expr::pi(
                    bi_default(),
                    ih_type,
                    Expr::pi(bi_default(), quot_final, beta_q),
                ),
            ),
        ),
    )
}

// VERBATIM `build_ind_hyp_type` (quot.rs:394).
// `∀ a : α, β (@Quot.mk.{u} α r a)`
fn build_ind_hyp_type(u: &Name, qn: &QuotNames) -> Expr {
    // α is BVar 2
    let alpha = Expr::bvar(2);

    // @Quot.mk.{u} α r a (after binding a: α BVar 3, r BVar 2, β BVar 1, a BVar 0)
    let mk_a = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(qn.quot_mk.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(3), // α
            ),
            Expr::bvar(2), // r
        ),
        Expr::bvar(0), // a
    );

    // β (@Quot.mk α r a) where β is BVar 1 after binding a
    let beta_mk_a = Expr::app(Expr::bvar(1), mk_a);

    // ∀ a : α, β (@Quot.mk α r a)
    Expr::pi(bi_default(), alpha, beta_mk_a)
}

// VERBATIM `quot_sound_type` (quot.rs:420).
// `Quot.sound.{u} : {α}{r}{a b : α} → r a b → @Quot.mk α r a = @Quot.mk α r b`
fn quot_sound_type(u: &Name, qn: &QuotNames) -> Expr {
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));

    // r : α → α → Prop
    let r_type = Expr::pi(
        bi_default(),
        Expr::bvar(0),
        Expr::pi(bi_default(), Expr::bvar(1), Expr::prop()),
    );

    // a : α
    let a_type = Expr::bvar(1);
    // b : α
    let b_type = Expr::bvar(2);
    // h : r a b
    let h_type = Expr::app(Expr::app(Expr::bvar(2), Expr::bvar(1)), Expr::bvar(0));

    // Eq.{u} (Quot.{u} α r) (Quot.mk.{u} α r a) (Quot.mk.{u} α r b)
    let quot_alpha_r = Expr::app(
        Expr::app(
            Expr::const_(qn.quot.clone(), vec![Level::param(u.clone())]),
            Expr::bvar(4), // α
        ),
        Expr::bvar(3), // r
    );

    let mk_a = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(qn.quot_mk.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(4), // α
            ),
            Expr::bvar(3), // r
        ),
        Expr::bvar(2), // a
    );

    let mk_b = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(qn.quot_mk.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(4), // α
            ),
            Expr::bvar(3), // r
        ),
        Expr::bvar(1), // b
    );

    let eq_app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(qn.eq.clone(), vec![Level::param(u.clone())]),
                quot_alpha_r,
            ),
            mk_a,
        ),
        mk_b,
    );

    Expr::pi(
        bi_implicit(),
        sort_u,
        Expr::pi(
            bi_implicit(),
            r_type,
            Expr::pi(
                bi_implicit(),
                a_type,
                Expr::pi(
                    bi_implicit(),
                    b_type,
                    Expr::pi(bi_default(), h_type, eq_app),
                ),
            ),
        ),
    )
}

// ════════════════════════════════════════════════════════════════════════════
// MONO ROOT (#[no_mangle]) — the single closure-free root the emitter picks with
// `--mir-emit-closure quot_type_root`. It receives the quotient KIND (0=Quot,
// 1=mk, 2=lift, 3=ind, 4=sound), the u/v level-param name raws, and the interned
// Quot/Quot.mk/Eq name raws, dispatches to the matching VERBATIM builder, and
// writes the resulting `Expr` (the full axiom TYPE) through the sret pointer
// (deep-compared native == JIT + top-level meta word).
// ════════════════════════════════════════════════════════════════════════════

#[repr(C)]
pub struct BuildQuotTypeArgs {
    pub kind: u32,        // 0=Quot,1=mk,2=lift,3=ind,4=sound
    pub u_raw: u32,       // the `u` universe param name
    pub v_raw: u32,       // the `v` universe param name (only used by kind==2/lift)
    pub quot_raw: u32,    // names::QUOT
    pub quot_mk_raw: u32, // names::QUOT_MK
    pub eq_raw: u32,      // Name::from_string("Eq")
}

#[no_mangle]
pub extern "C" fn quot_type_root(out: *mut Expr, args: *const BuildQuotTypeArgs) {
    let a: &BuildQuotTypeArgs = unsafe { &*args };
    let u = Name(a.u_raw);
    let v = Name(a.v_raw);
    let qn = QuotNames {
        quot: Name(a.quot_raw),
        quot_mk: Name(a.quot_mk_raw),
        eq: Name(a.eq_raw),
    };

    let result = if a.kind == 0 {
        quot_type(&u)
    } else if a.kind == 1 {
        quot_mk_type(&u, &qn)
    } else if a.kind == 2 {
        quot_lift_type(&u, &v, &qn)
    } else if a.kind == 3 {
        quot_ind_type(&u, &qn)
    } else {
        quot_sound_type(&u, &qn)
    };

    unsafe {
        std::ptr::write(out, result);
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Standalone re-emit validate harness — build all five quotient axiom types
// through quot_type_root and self-check native == via-root (structure + meta word).
// ════════════════════════════════════════════════════════════════════════════

fn deep_eq(a: &Expr, b: &Expr) -> bool {
    if a.meta.raw() != b.meta.raw() {
        return false;
    }
    match (&a.kind, &b.kind) {
        (ExprKind::BVar(x), ExprKind::BVar(y)) => x == y,
        (ExprKind::FVar(x), ExprKind::FVar(y)) => x == y,
        (ExprKind::Sort(x), ExprKind::Sort(y)) => x == y,
        (ExprKind::Const(n1, l1), ExprKind::Const(n2, l2)) => n1 == n2 && l1 == l2,
        (ExprKind::Lit(x), ExprKind::Lit(y)) => x == y,
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => deep_eq(f1, f2) && deep_eq(a1, a2),
        (ExprKind::Lam(b1, t1, y1), ExprKind::Lam(b2, t2, y2)) => {
            b1 == b2 && deep_eq(t1, t2) && deep_eq(y1, y2)
        }
        (ExprKind::Pi(b1, t1, y1), ExprKind::Pi(b2, t2, y2)) => {
            b1 == b2 && deep_eq(t1, t2) && deep_eq(y1, y2)
        }
        _ => false,
    }
}

// Name raws used by the harness (arbitrary distinct interner handles).
const U_RAW: u32 = 7;
const V_RAW: u32 = 8;
const QUOT_RAW: u32 = 1000;
const QUOT_MK_RAW: u32 = 1001;
const EQ_RAW: u32 = 1002;

fn via_root(kind: u32) -> Expr {
    let args = BuildQuotTypeArgs {
        kind,
        u_raw: U_RAW,
        v_raw: V_RAW,
        quot_raw: QUOT_RAW,
        quot_mk_raw: QUOT_MK_RAW,
        eq_raw: EQ_RAW,
    };
    let mut slot = std::mem::MaybeUninit::<Expr>::uninit();
    unsafe {
        quot_type_root(slot.as_mut_ptr(), &args as *const BuildQuotTypeArgs);
        slot.assume_init()
    }
}

fn native(kind: u32) -> Expr {
    let u = Name(U_RAW);
    let v = Name(V_RAW);
    let qn = QuotNames {
        quot: Name(QUOT_RAW),
        quot_mk: Name(QUOT_MK_RAW),
        eq: Name(EQ_RAW),
    };
    match kind {
        0 => quot_type(&u),
        1 => quot_mk_type(&u, &qn),
        2 => quot_lift_type(&u, &v, &qn),
        3 => quot_ind_type(&u, &qn),
        _ => quot_sound_type(&u, &qn),
    }
}

fn main() {
    let labels = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind", "Quot.sound"];
    for kind in 0u32..5 {
        let n = native(kind);
        let r = via_root(kind);
        assert!(
            deep_eq(&n, &r),
            "native != via-root for {}",
            labels[kind as usize]
        );
        assert_eq!(
            n.meta.raw(),
            r.meta.raw(),
            "meta word disagrees for {}",
            labels[kind as usize]
        );
        println!("{}: OK meta={:#018x}", labels[kind as usize], n.meta.raw());
    }
    println!("all five quotient axiom types: native == via-root");
}
