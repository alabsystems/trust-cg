// SELF-CONTAINED clean-kernel FULL RECURSOR-TYPE slice — the SOUNDNESS-CRITICAL
// elimination-principle STATEMENT construction `Environment::build_recursor_type`
// ($HOME/clean/crates/clean-kernel/src/env/inductive_recursor_types.rs:89), the function
// that assembles the COMPLETE type of an inductive's recursor `I.rec`.
//
// WHY A BUG HERE = UNSOUNDNESS. The recursor's TYPE **is** the elimination
// principle's statement:
//   I.rec : (params) -> {motive_0 .. motive_{m-1}} ->
//           (minor_0) -> .. -> (minor_{k-1}) ->
//           (indices) -> (major : I params indices) -> motive_j indices major
// If this Pi-telescope is WRONG — a motive over the wrong shape, a minor premise in
// the wrong slot / at the wrong de-Bruijn depth, a mis-lifted index domain, or a
// conclusion `motive_j indices major` that references the wrong motive / indices /
// major — then `I.rec` is TYPED at a principle STRONGER than justified: the user
// gets an eliminator whose conclusion does not follow from the discharged obligations,
// a direct route to a proof of `False`. So `build_recursor_type` IS the recursor
// soundness gate for the elimination-rule STATEMENT — the companion of the already
// native==JIT-verified `build_minor_premise_type` (the per-ctor minor premise) and
// `build_recursor_rule_rhs` (the iota computation rule).
//
// Transcribed VERBATIM from $HOME/clean/crates/clean-kernel/src/env/:
//   * build_recursor_type                 (inductive_recursor_types.rs:89)  — THE FN
//   * build_minor_premise_type            (inductive_recursor_minor.rs:33)  — VERIFIED pillar (per-ctor minor)
//   * ctor_motive_index                   (inductive_recursor_types.rs:28)  — pillar
//   * field_motive_index                  (inductive_recursor_types.rs:45)  — VERIFIED pillar
//   * collect_pi_binders                  (inductive_recursor.rs:988)       — pillar (Pi-telescope collect, w/ consume_type_annotations)
//   * collect_pi_binders_after_skip       (inductive_recursor_types.rs:510) — pillar
//   * count_pi_args                       (inductive/mod.rs:608)            — pillar
//   * consume_type_annotations            (inductive/mod.rs:676)            — pillar (optParam/autoParam/outParam strip)
//   * get_constructor_return_indices      (inductive_recursor.rs:951)       — VERIFIED pillar
//   * count_pi_binders                    (inductive_recursor_rules.rs:24)  — VERIFIED pillar
//   * collect_pi_domains                  (inductive_recursor_rules.rs:39)  — VERIFIED pillar
//   * remap_residual_index_bvars_for_minor(inductive_recursor_rules.rs:94)  — VERIFIED pillar
//   * infer_implicit / infer_implicit_n   (expr/subst.rs:560)               — pillar (the strict-mode implicit-binder inference)
//   * has_loose_bvars_in_domain           (expr/mod.rs:140)                 — pillar
//   * has_loose_bvar / _in_range(_impl)   (expr/subst.rs:547 / mod.rs)      — VERIFIED read pillar (meta guard + tree walk)
//   * bvar_in_range / shift_bvar_range    (expr/mod.rs:94 / 114)            — pillar
//   * get_return_type                     (inductive/mod.rs:650)            — VERIFIED pillar (Pi-telescope)
//   * get_app_fn                          (expr/constructors.rs:256)        — VERIFIED pillar (App-spine head walk)
//   * ind_const_with_levels               (inductive_fixed_indices.rs:266)  — Const ctor helper
//   * usize_to_u32                        (env/mod.rs:3054)                 — helper
//
// COMPOSED VERIFIED CONSTRUCTION PILLARS (over the REAL hashconsed Expr/ExprMeta):
//   - Expr::{bvar,app,lam,pi,const_,sort} -> from_kind -> compute_meta -> mk_app_meta /
//     mk_binder_meta / pack / mix_hash / KaniHasher  (the VERBATIM construction core;
//     Arc::new children lower to heap_alloc).
//   - Expr::lift / lift_from -> lift_at  (the VERIFIED de-Bruijn lift).
//   - get_app_fn (the VERIFIED App-spine head walk, reused by field_motive_index).
//   - has_loose_bvar_in_range (the VERIFIED loose-bvar read, driving infer_implicit).
//
// FAITHFULNESS / control flow is VERBATIM the real `build_recursor_type`:
//   collect param/index binders from ind_type's Pi telescope; build one motive type
//   per type in the mutual block (Π indices Π major → Sort u); build one minor premise
//   per ctor via the VERIFIED build_minor_premise_type; assemble inside-out
//   params → motives → minors → indices → major → (motive_j indices major); each with
//   the real per-binder lift arithmetic; then infer_implicit(strict=true). Every BVar
//   depth, every lift/lift_from, every Pi/App/Sort is byte-for-byte the real arithmetic.
//
// MODELING boundary:
//   * `InductiveType` -> `{name: Name, type_: Expr, constructors: Vec<Ctor>}` where
//     `Ctor{name,type_}` — exactly the fields the fn reads: `.name` (ctor_motive_index /
//     this_motive_idx), `.type_` (count_pi_args / collect_pi_binders_after_skip for the
//     motive-type builder), and `.constructors` (ctor_path_data — see below). The fn
//     NEVER reads anything else off these structs.
//   * BinderInfo -> a 2-variant model {Default=0, Implicit=1}; Multiplicity -> u8; the
//     real `BinderData{info,mult}` -> `{info: u8, mult: u8}`. `infer_implicit`'s
//     `bd.info != BinderInfo::Default` -> `bd.info != 0`; `BinderData::new(Implicit,
//     bd.mult)` -> `{info:1, mult: bd.mult}`. The BinderData bytes are compared
//     field-for-field in deep_eq but do NOT enter the meta hash (mk_binder_meta hashes
//     only ty/body/depth/extra_hash, not the binder tag), so the exact numeric encoding
//     is internally consistent between native & JIT (both run this identical modeled code).
//   * HIT / path constructors: `ctor_path_data` returns `Some` ONLY when a ctor's
//     return type is `ExprKind::CubicalPath{..}` (a Higher-Inductive path ctor). The
//     modeled `ExprKind` has NO CubicalPath variant and the test inductives (Nat, List,
//     And, an indexed family) are ALL non-HIT, so `ctor_path_data` is MODELED to always
//     return `None` — the `is_path` branch and `build_path_minor_premise_type` are
//     provably dead on every verified case (documented; not on the JIT path).
//   * `consume_type_annotations` reads `name.to_string()` and compares to the literal
//     wrapper names optParam/autoParam/outParam/semiOutParam. Real `Name::to_string`
//     interns; MODELED as "no synthetic ctor uses those reserved wrapper Names" so the
//     scan is a fast no-op that returns its input unchanged — faithful for every
//     non-annotated domain the construction here builds (none use the wrappers).
//   * Leaf-payload Hash (Name/Level/Literal) MODELED exactly as the verified
//     construction slice (KaniHasher seeds verbatim); off the App/Pi/BVar/Const/Sort
//     construction-path hashing this fn drives, which is 100% mix_hash integer mixing.
//
// Crate name is load-bearing (appears in the mangled extern symbols the JIT binds):
// it MUST stay `clean_recursor_type_slice`.

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
// subst.rs / expr::mod.rs — VERBATIM de-Bruijn READS: lift_at (WRITE lift) +
// has_loose_bvar_in_range (the meta-guarded loose-bvar READ driving infer_implicit).
// ════════════════════════════════════════════════════════════════════════════

#[inline]
pub(crate) fn checked_add_u32(a: u32, b: u32) -> u32 {
    a.saturating_add(b)
}

// VERBATIM `bvar_in_range` (expr/mod.rs:94).
pub(crate) fn bvar_in_range(idx: u32, start: u32, end: u32) -> bool {
    if end == u32::MAX {
        idx >= start
    } else {
        idx >= start && idx < end
    }
}

// VERBATIM `shift_bvar_range` (expr/mod.rs:114). `checked_add_u32` -> saturating_add.
pub(crate) fn shift_bvar_range(start: u32, end: u32) -> Option<(u32, u32)> {
    if end != u32::MAX && start >= end {
        return None;
    }
    if start == u32::MAX {
        return None;
    }
    let next_start = checked_add_u32(start, 1);
    let next_end = if end == u32::MAX {
        u32::MAX
    } else {
        checked_add_u32(end, 1)
    };
    Some((next_start, next_end))
}

impl Expr {
    pub fn lift_at(&self, start: u32, amount: u32) -> Expr {
        if amount == 0 {
            return self.clone();
        }
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
            ExprKind::App(f, a) => Expr::app(f.lift_at(start, amount), a.lift_at(start, amount)),
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
            _ => self.clone(),
        }
    }

    // VERBATIM `Expr::lift` (subst.rs:495).
    pub fn lift(&self, amount: u32) -> Expr {
        self.lift_at(0, amount)
    }
    // VERBATIM `Expr::lift_from` (subst.rs:511).
    pub fn lift_from(&self, start: u32, amount: u32) -> Expr {
        self.lift_at(start, amount)
    }

    // VERBATIM `Expr::get_app_fn` (expr/constructors.rs:256) — the VERIFIED App-spine
    // head walk (reused by field_motive_index).
    pub fn get_app_fn(&self) -> &Expr {
        let mut current = self;
        while let ExprKind::App(f, _) = &current.kind {
            current = f;
        }
        current
    }

    // VERBATIM `Expr::has_loose_bvar` (subst.rs:547).
    pub fn has_loose_bvar(&self, idx: u32) -> bool {
        self.has_loose_bvar_in_range(idx, idx + 1)
    }

    // VERBATIM `Expr::has_loose_bvar_in_range` (subst.rs:595) — the real wraps
    // `has_loose_bvar_in_range_impl` in `stack_safe(||..)` (a maybe_grow that is a
    // no-op on these small trees); dropped, calling the impl directly.
    pub fn has_loose_bvar_in_range(&self, start: u32, end: u32) -> bool {
        self.has_loose_bvar_in_range_impl(start, end)
    }

    // VERBATIM `has_loose_bvar_in_range_impl` (subst.rs:601). Only the modeled ExprKind
    // arms are present (the CubicalPath/MData/SProp/Squash/... arms are unconstructible
    // in this slice; the `_ => false` on leaves matches the real FVar/Sort/Const/Lit).
    fn has_loose_bvar_in_range_impl(&self, start: u32, end: u32) -> bool {
        if end != u32::MAX && start >= end {
            return false;
        }
        // O(1) metadata guard: all loose BVar indices are < loose_bvar_range(),
        // so if loose_bvar_range() <= start, no BVars exist in [start, end).
        if self.loose_bvar_range() <= start {
            return false;
        }
        match &self.kind {
            ExprKind::BVar(idx) => bvar_in_range(*idx, start, end),
            ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Const(_, _) | ExprKind::Lit(_) => {
                false
            }
            ExprKind::App(f, a) => {
                f.has_loose_bvar_in_range(start, end) || a.has_loose_bvar_in_range(start, end)
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                let body_has_loose = match shift_bvar_range(start, end) {
                    Some((next_start, next_end)) => {
                        body.has_loose_bvar_in_range(next_start, next_end)
                    }
                    None => false,
                };
                ty.has_loose_bvar_in_range(start, end) || body_has_loose
            }
            ExprKind::Let(_, ty, val, body, _) => {
                let body_has_loose = match shift_bvar_range(start, end) {
                    Some((next_start, next_end)) => {
                        body.has_loose_bvar_in_range(next_start, next_end)
                    }
                    None => false,
                };
                ty.has_loose_bvar_in_range(start, end)
                    || val.has_loose_bvar_in_range(start, end)
                    || body_has_loose
            }
            ExprKind::Proj(_, _, e) => e.has_loose_bvar_in_range(start, end),
        }
    }

    // VERBATIM `infer_implicit` (subst.rs:560) — strict-mode wrapper over infer_implicit_n.
    pub fn infer_implicit(&self, strict: bool) -> Expr {
        self.infer_implicit_n(u32::MAX, strict)
    }

    // VERBATIM `infer_implicit_n` (subst.rs:567). `bd.info != BinderInfo::Default`
    // -> `bd.info != INFO_DEFAULT`; `BinderData::new(BinderInfo::Implicit, bd.mult)`
    // -> `BinderData::new(1, bd.mult)`.
    pub fn infer_implicit_n(&self, num_params: u32, strict: bool) -> Expr {
        if num_params == 0 {
            return self.clone();
        }
        match &self.kind {
            ExprKind::Pi(bd, domain, body) => {
                let new_body = body.infer_implicit_n(num_params - 1, strict);
                if bd.info != INFO_DEFAULT {
                    // Already non-explicit — keep as-is, just update body
                    Expr::pi(*bd, (**domain).clone(), new_body)
                } else if has_loose_bvars_in_domain(&new_body, 0, strict) {
                    // BVar 0 appears in a subsequent domain — mark implicit
                    Expr::pi(
                        BinderData::new(1, bd.mult),
                        (**domain).clone(),
                        new_body,
                    )
                } else {
                    Expr::pi(*bd, (**domain).clone(), new_body)
                }
            }
            _ => self.clone(),
        }
    }
}

// VERBATIM `has_loose_bvars_in_domain` (expr/mod.rs:140). `bd.info == BinderInfo::Default`
// -> `bd.info == INFO_DEFAULT`.
pub(crate) fn has_loose_bvars_in_domain(b: &Expr, vidx: u32, strict: bool) -> bool {
    match &b.kind {
        ExprKind::Pi(bd, domain, body) => {
            if domain.has_loose_bvar(vidx) {
                if bd.info == INFO_DEFAULT {
                    // vidx appears in an explicit argument's domain
                    return true;
                } else if has_loose_bvars_in_domain(body, 0, strict) {
                    // Transitivity
                    return true;
                }
            }
            has_loose_bvars_in_domain(body, vidx + 1, strict)
        }
        _ => {
            if !strict {
                b.has_loose_bvar(vidx)
            } else {
                false
            }
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// MODELED InductiveType — the struct build_recursor_type reads via `all_types`:
//   .name (ctor_motive_index / this_motive_idx / field_motive_index),
//   .type_ (count_pi_args / collect_pi_binders_after_skip for the motive-type builder),
//   .constructors (ctor_path_data — HIT check, modeled to return None).
// ════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Debug)]
pub struct Ctor {
    pub name: Name,
    pub type_: Expr,
}

#[derive(Clone, Debug)]
pub struct InductiveType {
    pub name: Name,
    pub type_: Expr,
    pub constructors: Vec<Ctor>,
}

// VERBATIM `ind_const_with_levels` (inductive_fixed_indices.rs:266).
pub(crate) fn ind_const_with_levels(name: &Name, level_params: &[Name]) -> Expr {
    // VERBATIM `level_params.iter().map(|p| Level::param(p.clone())).collect()` —
    // lowered to the equivalent push loop (identical: one Level::Param per param).
    let mut levels: Vec<Level> = Vec::new();
    {
        let mut _i = 0usize;
        while _i < level_params.len() {
            levels.push(Level::Param(level_params[_i]));
            _i += 1;
        }
    }
    Expr::const_(*name, levels)
}

// VERBATIM `get_return_type` (inductive/mod.rs:650) — walk past the Pi telescope.
pub(crate) fn get_return_type(expr: &Expr) -> &Expr {
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = &current.kind {
        current = body;
    }
    current
}

// ════════════════════════════════════════════════════════════════════════════
// The Environment-method PILLARS transcribed as free fns over the modeled types.
// ════════════════════════════════════════════════════════════════════════════

#[inline]
fn usize_to_u32(value: usize) -> u32 {
    u32::try_from(value).unwrap_or(u32::MAX)
}

// VERBATIM `count_pi_args` (inductive/mod.rs:608).
pub(crate) fn count_pi_args(expr: &Expr) -> u32 {
    let mut count = 0u32;
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = &current.kind {
        count = count.saturating_add(1);
        current = body;
    }
    count
}

// MODELED `consume_type_annotations` (inductive/mod.rs:676). The real fn peels
// optParam/autoParam (arity-2) and outParam/semiOutParam (arity-1) wrapper Consts by
// comparing `name.to_string()` to those literals. No synthetic domain in this slice uses
// a reserved wrapper Name, so the scan is a faithful no-op returning its input unchanged.
// (Const-name interning `to_string` is off this fn's construction/lift/read path.)
pub(crate) fn consume_type_annotations(expr: &Expr) -> &Expr {
    expr
}

// VERBATIM `field_motive_index` (inductive_recursor_types.rs:45).
pub(crate) fn field_motive_index(field_ty: &Expr, all_types: &[InductiveType]) -> usize {
    let ret_ty = get_return_type(field_ty);
    let head = ret_ty.get_app_fn();
    if let ExprKind::Const(name, _) = &head.kind {
        // VERBATIM `for (idx, ind_type) in all_types.iter().enumerate()` — index loop.
        let mut idx = 0usize;
        while idx < all_types.len() {
            if &all_types[idx].name == name {
                return idx;
            }
            idx += 1;
        }
    }
    0
}

// VERBATIM `ctor_motive_index` (inductive_recursor_types.rs:28).
pub(crate) fn ctor_motive_index(ctor_name: &Name, all_types: &[InductiveType]) -> usize {
    // VERBATIM `for (idx, ind_type) in all_types.iter().enumerate()` — index loops.
    let mut idx = 0usize;
    while idx < all_types.len() {
        let mut ci = 0usize;
        while ci < all_types[idx].constructors.len() {
            if &all_types[idx].constructors[ci].name == ctor_name {
                return idx;
            }
            ci += 1;
        }
        idx += 1;
    }
    0
}

// MODELED `ctor_path_data` (inductive_recursor_minor.rs:175). The real fn returns
// `Some((left,right))` ONLY when a ctor's return type is `ExprKind::CubicalPath{..}`
// (a HIT path ctor). The modeled ExprKind has NO CubicalPath variant and every test
// inductive is non-HIT, so this ALWAYS returns None — the is_path / path-minor branch
// is provably dead on every verified case.
pub(crate) fn ctor_path_data(
    _ctor_name: &Name,
    _all_types: &[InductiveType],
) -> Option<(Expr, Expr)> {
    None
}

// VERBATIM `count_pi_binders` (inductive_recursor_rules.rs:24).
pub(crate) fn count_pi_binders(expr: &Expr) -> usize {
    let mut count = 0;
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = &current.kind {
        count += 1;
        current = body;
    }
    count
}

// VERBATIM `collect_pi_domains` (inductive_recursor_rules.rs:39).
pub(crate) fn collect_pi_domains(expr: &Expr) -> Vec<(BinderData, Expr)> {
    let mut domains = Vec::new();
    let mut current = expr;
    while let ExprKind::Pi(bi, domain, body) = &current.kind {
        domains.push((*bi, (**domain).clone()));
        current = body;
    }
    domains
}

// VERBATIM `collect_pi_binders` (inductive_recursor.rs:988). The real collects through
// `consume_type_annotations(domain)` (modeled no-op).
pub(crate) fn collect_pi_binders(ty: &Expr, count: u32) -> Vec<(BinderData, Expr)> {
    let mut result = Vec::new();
    let mut current = ty.clone();
    let mut collected = 0u32;
    while collected < count {
        if let ExprKind::Pi(bi, domain, codomain) = &current.kind {
            result.push((*bi, consume_type_annotations(domain).clone()));
            current = (**codomain).clone();
            collected += 1;
        } else {
            break;
        }
    }
    result
}

// VERBATIM `collect_pi_binders_after_skip` (inductive_recursor_types.rs:510).
pub(crate) fn collect_pi_binders_after_skip(
    ty: &Expr,
    skip: u32,
    count: u32,
) -> Vec<(BinderData, Expr)> {
    let mut current = ty.clone();
    {
        let mut _s = 0u32;
        while _s < skip {
            if let ExprKind::Pi(_, _, body) = &current.kind {
                current = (**body).clone();
            }
            _s += 1;
        }
    }
    collect_pi_binders(&current, count)
}

// VERBATIM `get_constructor_return_indices` (inductive_recursor.rs:951).
pub(crate) fn get_constructor_return_indices(ctor_ty: &Expr, num_params: u32) -> Vec<Expr> {
    let mut current = ctor_ty.clone();
    while let ExprKind::Pi(_, _, codomain) = &current.kind {
        current = (**codomain).clone();
    }
    let mut args: Vec<Expr> = Vec::new();
    while let ExprKind::App(f, a) = &current.kind {
        args.push((**a).clone());
        current = (**f).clone();
    }
    // args collected rightmost-first; VERBATIM `args.reverse()` then
    // `.into_iter().skip(num_params).collect()` — single forward emit over the reversed
    // (source-order) indices, skipping the first num_params.
    let np = num_params as usize;
    let n = args.len();
    let mut out: Vec<Expr> = Vec::new();
    {
        let mut s = 0usize;
        while s < n {
            if s >= np {
                out.push(args[n - 1 - s].clone());
            }
            s += 1;
        }
    }
    out
}

// VERBATIM `remap_residual_index_bvars_for_minor` (inductive_recursor_rules.rs:94).
pub(crate) fn remap_residual_index_bvars_for_minor(
    expr: &Expr,
    field_idx: usize,
    nf: usize,
    ih_offset: usize,
    n_pis: usize,
) -> Expr {
    match &expr.kind {
        ExprKind::BVar(k) => {
            let k = *k as usize;
            let new_k = if k < n_pis {
                k
            } else {
                let ctor_k = k - n_pis;
                if ctor_k < field_idx {
                    let field_j = field_idx - 1 - ctor_k;
                    ih_offset + nf - 1 - field_j + n_pis
                } else {
                    let param_j = ctor_k - field_idx;
                    ih_offset + nf + 1 + param_j + n_pis
                }
            };
            Expr::bvar(usize_to_u32(new_k))
        }
        ExprKind::App(f, a) => {
            let f2 = remap_residual_index_bvars_for_minor(f, field_idx, nf, ih_offset, n_pis);
            let a2 = remap_residual_index_bvars_for_minor(a, field_idx, nf, ih_offset, n_pis);
            Expr::app(f2, a2)
        }
        _ => expr.clone(),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// VERIFIED PILLAR — `build_minor_premise_type`, VERBATIM from
// inductive_recursor_minor.rs:33 (already native==JIT verified). Reused here as the
// per-ctor minor-premise slot filler; `BinderInfo::Default` -> `bi_default()`.
// ════════════════════════════════════════════════════════════════════════════

#[allow(clippy::too_many_arguments)]
pub fn build_minor_premise_type(
    ind_name: &Name,
    ctor_name: &Name,
    num_fields: u32,
    recursive_flags: &[bool],
    field_types: &[Expr],
    num_params: u32,
    ind_level_params: &[Name],
    ctor_indices: &[Expr],
    num_motives: usize,
    conclusion_motive_idx: usize,
    all_types: &[InductiveType],
) -> Expr {
    // VERBATIM `recursive_flags.iter().filter(|&&b| b).count()` — explicit count loop.
    let mut num_ihs: usize = 0;
    {
        let mut _ci = 0usize;
        while _ci < recursive_flags.len() {
            if recursive_flags[_ci] {
                num_ihs += 1;
            }
            _ci += 1;
        }
    }
    let num_fields = num_fields as usize;

    let conclusion_motive_bvar =
        num_fields + num_ihs + (num_motives - 1 - conclusion_motive_idx);

    let adjust_index_expr = |expr: Expr, ih_offset: usize| -> Expr {
        let mut adjusted = expr.lift(usize_to_u32(ih_offset));
        adjusted = adjusted.lift_from(
            usize_to_u32(ih_offset + num_fields),
            num_motives as u32,
        );
        adjusted
    };

    // VERBATIM `ind_level_params.iter().map(|p| Level::param(p.clone())).collect()`.
    let mut ctor_levels: Vec<Level> = Vec::new();
    {
        let mut _pi = 0usize;
        while _pi < ind_level_params.len() {
            ctor_levels.push(Level::Param(ind_level_params[_pi]));
            _pi += 1;
        }
    }
    let mut ctor_app = Expr::const_(*ctor_name, ctor_levels);
    {
        let mut i: u32 = 0;
        while i < num_params {
            let param_depth =
                num_fields + num_ihs + num_motives + (num_params as usize - 1 - i as usize);
            ctor_app = Expr::app(ctor_app, Expr::bvar(usize_to_u32(param_depth)));
            i += 1;
        }
    }
    {
        let mut i: usize = 0;
        while i < num_fields {
            let field_depth = (num_fields - 1 - i) + num_ihs;
            ctor_app = Expr::app(ctor_app, Expr::bvar(usize_to_u32(field_depth)));
            i += 1;
        }
    }

    let mut result = Expr::bvar(usize_to_u32(conclusion_motive_bvar));
    {
        let mut _ii = 0usize;
        while _ii < ctor_indices.len() {
            let adjusted = adjust_index_expr(ctor_indices[_ii].clone(), num_ihs);
            result = Expr::app(result, adjusted);
            _ii += 1;
        }
    }
    result = Expr::app(result, ctor_app);

    let mut ih_offset = 0usize;
    let mut _ri = recursive_flags.len();
    while _ri > 0 {
        _ri -= 1;
        let i = _ri;
        let is_recursive = recursive_flags[i];
        if is_recursive {
            let ihs_above = num_ihs - 1 - ih_offset;
            let field_depth = (num_fields - 1 - i) + ihs_above;

            let ih_motive_idx = match field_types.get(i) {
                Some(ft) => field_motive_index(ft, all_types),
                None => conclusion_motive_idx,
            };
            let motive_at_ih = num_fields + ihs_above + (num_motives - 1 - ih_motive_idx);

            let n_pis = match field_types.get(i) {
                Some(ft) => count_pi_binders(ft),
                None => 0,
            };

            let ih_motive = motive_at_ih + n_pis;
            let ih_field_depth = field_depth + n_pis;

            let mut ih_type = Expr::bvar(usize_to_u32(ih_motive));

            let field_ty = match field_types.get(i) {
                Some(ft) => ft.clone(),
                None => ind_const_with_levels(ind_name, ind_level_params),
            };
            let field_indices = get_constructor_return_indices(&field_ty, num_params);
            {
                let mut _fi = 0usize;
                while _fi < field_indices.len() {
                    let remapped = remap_residual_index_bvars_for_minor(
                        &field_indices[_fi], i, num_fields, ihs_above, n_pis,
                    );
                    ih_type = Expr::app(ih_type, remapped);
                    _fi += 1;
                }
            }

            let mut major = Expr::bvar(usize_to_u32(ih_field_depth));
            {
                let mut _k = n_pis;
                while _k > 0 {
                    _k -= 1;
                    major = Expr::app(major, Expr::bvar(usize_to_u32(_k)));
                }
            }
            ih_type = Expr::app(ih_type, major);

            let pi_domains = match field_types.get(i) {
                Some(ft) => collect_pi_domains(ft),
                None => Vec::new(),
            };
            {
                let mut _pd = pi_domains.len();
                while _pd > 0 {
                    _pd -= 1;
                    let k = _pd;
                    let (bi, domain) = &pi_domains[k];
                    let remapped = remap_residual_index_bvars_for_minor(
                        domain, i, num_fields, ihs_above, k,
                    );
                    ih_type = Expr::pi(*bi, remapped, ih_type);
                }
            }

            result = Expr::pi(bi_default(), ih_type, result);
            ih_offset += 1;
        }
    }

    {
        let mut _fb = num_fields;
        while _fb > 0 {
            _fb -= 1;
            let i = _fb;
            let field_ty = match field_types.get(i) {
                Some(ft) => ft.clone(),
                None => ind_const_with_levels(ind_name, ind_level_params),
            };
            let lifted_field_ty = field_ty.lift_from(usize_to_u32(i), num_motives as u32);
            result = Expr::pi(bi_default(), lifted_field_ty, result);
        }
    }

    result
}

// ════════════════════════════════════════════════════════════════════════════
// THE SOUNDNESS-CRITICAL FN — `build_recursor_type`, VERBATIM from
// inductive_recursor_types.rs:89. `&self` (Environment) is dropped: on this path it is
// used ONLY to reach the associated helper fns (`self.collect_pi_binders`,
// `self.collect_pi_binders_after_skip`, `self.build_minor_premise_type`), all transcribed
// above. The `build_ind_app` closure is preserved verbatim.
// `BinderInfo::Default`/`::Implicit` -> `bi_default()`/`bi_implicit()`.
//
// A CtorInfo is `(ctor_name, num_fields, recursive_flags, field_types, return_indices)`.
// ════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Debug)]
pub struct CtorInfo {
    pub name: Name,
    pub num_fields: u32,
    pub recursive_flags: Vec<bool>,
    pub field_types: Vec<Expr>,
    pub return_indices: Vec<Expr>,
}

#[allow(clippy::too_many_arguments)]
pub fn build_recursor_type(
    ind_name: &Name,
    ind_type: &Expr,
    num_params: u32,
    num_indices: u32,
    motive_univ_name: Option<&Name>,
    ind_level_params: &[Name],
    ctor_infos: &[CtorInfo],
    all_types: &[InductiveType],
) -> Expr {
    // Prop-only elimination: motive targets Sort 0 (Prop). Large elimination: Sort u.
    // VERBATIM `match motive_univ_name { Some(name) => Level::param(name.clone()),
    //   None => Level::zero() }`.
    let motive_univ = match motive_univ_name {
        Some(name) => Level::Param(*name),
        None => Level::Zero,
    };
    let ind_const = ind_const_with_levels(ind_name, ind_level_params);

    let num_motives = all_types.len();

    // Collect parameter and index binders from the inductive type.
    let param_binders = collect_pi_binders(ind_type, num_params);
    let mut current = ind_type.clone();
    {
        let mut _p = 0u32;
        while _p < num_params {
            if let ExprKind::Pi(_, _, body) = &current.kind {
                current = (**body).clone();
            }
            _p += 1;
        }
    }
    let index_binders = collect_pi_binders(&current, num_indices);
    let num_minors = ctor_infos.len();

    // Helper to build Ind applied to params and indices at given depths (VERBATIM closure).
    let build_ind_app = |param_offset: u32, index_offset: u32| -> Expr {
        let mut ind_app = ind_const.clone();
        {
            let mut i: u32 = 0;
            while i < num_params {
                let idx = param_offset + (num_params - 1 - i);
                ind_app = Expr::app(ind_app, Expr::bvar(idx));
                i += 1;
            }
        }
        {
            let mut i: u32 = 0;
            while i < num_indices {
                let idx = index_offset + (num_indices - 1 - i);
                ind_app = Expr::app(ind_app, Expr::bvar(idx));
                i += 1;
            }
        }
        ind_app
    };

    // Build motive types for ALL types in the mutual block.
    // Each motive: Π indices_i, Π (major : Type_i indices_i), Sort u.
    let mut motive_types: Vec<Expr> = Vec::with_capacity(num_motives);
    {
        let mut _t = 0usize;
        while _t < all_types.len() {
            let t = &all_types[_t];
            let t_const = ind_const_with_levels(&t.name, ind_level_params);
            let t_type_arity = count_pi_args(&t.type_);
            let t_num_indices = t_type_arity.saturating_sub(num_params);
            let t_index_binders =
                collect_pi_binders_after_skip(&t.type_, num_params, t_num_indices);

            let mut mtype = Expr::from_kind(ExprKind::Sort(motive_univ.clone()));
            // major type: Type_i params indices
            let mut major_ty_for_motive = t_const.clone();
            {
                let mut i: u32 = 0;
                while i < num_params {
                    let idx = t_num_indices + (num_params - 1 - i);
                    major_ty_for_motive = Expr::app(major_ty_for_motive, Expr::bvar(idx));
                    i += 1;
                }
            }
            {
                let mut i: u32 = 0;
                while i < t_num_indices {
                    let idx = t_num_indices - 1 - i;
                    major_ty_for_motive = Expr::app(major_ty_for_motive, Expr::bvar(idx));
                    i += 1;
                }
            }
            mtype = Expr::pi(bi_default(), major_ty_for_motive, mtype);
            // Add the index binders, outermost (idx_0) last. Each I_i placed UNCHANGED
            // (see the real comment: the standalone-motive and inductive-telescope
            // contexts are identical; a previous over-shift was the multi-index bug).
            // VERBATIM `for (binder_info, index_ty) in t_index_binders.iter().rev()`.
            {
                let mut _ib = t_index_binders.len();
                while _ib > 0 {
                    _ib -= 1;
                    let (binder_info, index_ty) = &t_index_binders[_ib];
                    mtype = Expr::pi(*binder_info, index_ty.clone(), mtype);
                }
            }
            motive_types.push(mtype);
            _t += 1;
        }
    }

    // Determine which motive index corresponds to ind_name.
    // VERBATIM `all_types.iter().position(|t| &t.name == ind_name).unwrap_or(0)`.
    let this_motive_idx = {
        let mut found: Option<usize> = None;
        let mut _i = 0usize;
        while _i < all_types.len() {
            if &all_types[_i].name == ind_name {
                found = Some(_i);
                break;
            }
            _i += 1;
        }
        match found {
            Some(v) => v,
            None => 0,
        }
    };

    // Build minor premise types. Each entry is (type, is_path).
    let mut minor_types: Vec<(Expr, bool)> = Vec::new();
    {
        let mut minor_self_idx = 0usize;
        while minor_self_idx < ctor_infos.len() {
            let ci = &ctor_infos[minor_self_idx];
            let ctor_name = &ci.name;
            let num_fields = ci.num_fields;
            let recursive_flags = &ci.recursive_flags;
            let field_types = &ci.field_types;
            let return_indices = &ci.return_indices;

            let ctor_motive_idx = ctor_motive_index(ctor_name, all_types);
            match ctor_path_data(ctor_name, all_types) {
                Some(_lr) => {
                    // Provably dead on every non-HIT test case (ctor_path_data == None).
                    // Path-minor construction is NOT modeled; unreachable here.
                    minor_types.push((Expr::bvar(0), true));
                }
                None => {
                    let minor_ty = build_minor_premise_type(
                        ind_name,
                        ctor_name,
                        num_fields,
                        recursive_flags,
                        field_types,
                        num_params,
                        ind_level_params,
                        return_indices,
                        num_motives,
                        ctor_motive_idx,
                        all_types,
                    );
                    minor_types.push((minor_ty, false));
                }
            }
            minor_self_idx += 1;
        }
    }

    // Build the full rec type from inside out:
    // params → motives → minors → indices → major → motive_i indices major
    let this_motive_bvar = usize_to_u32(
        num_minors + num_indices as usize + 1 + (num_motives - 1 - this_motive_idx),
    );
    let mut result_ty = Expr::bvar(this_motive_bvar);
    {
        let mut i: u32 = 0;
        while i < num_indices {
            let idx = usize_to_u32(num_indices as usize - i as usize);
            result_ty = Expr::app(result_ty, Expr::bvar(idx));
            i += 1;
        }
    }
    result_ty = Expr::app(result_ty, Expr::bvar(0)); // major

    // Add major premise: (t : Ind params indices) → result.
    let major_ty = build_ind_app(num_indices + num_minors as u32 + num_motives as u32, 0);
    result_ty = Expr::pi(bi_default(), major_ty, result_ty);

    // Add index binders. Param-referencing BVars shifted by (num_minors + num_motives).
    // VERBATIM `for (i, (binder_info, index_ty)) in index_binders.iter().enumerate().rev()`.
    let extra = usize_to_u32(num_minors + num_motives);
    {
        let mut _ix = index_binders.len();
        while _ix > 0 {
            _ix -= 1;
            let i = _ix;
            let (binder_info, index_ty) = &index_binders[i];
            let lifted_index_ty = if extra > 0 {
                index_ty.lift_from(i as u32, extra)
            } else {
                index_ty.clone()
            };
            result_ty = Expr::pi(*binder_info, lifted_index_ty, result_ty);
        }
    }

    // Add minor premises (reverse order). Each minor's BVars reference the motives; a
    // non-path minor at index i is lifted by i. Path minors (dead here) skip the lift.
    // VERBATIM `for (i, (minor_ty, is_path)) in minor_types.iter().enumerate().rev()`.
    {
        let mut _m = minor_types.len();
        while _m > 0 {
            _m -= 1;
            let i = _m;
            let (minor_ty, is_path) = &minor_types[i];
            let lifted_minor_ty = if *is_path || i == 0 {
                minor_ty.clone()
            } else {
                minor_ty.lift(usize_to_u32(i))
            };
            result_ty = Expr::pi(bi_default(), lifted_minor_ty, result_ty);
        }
    }

    // Add motives (innermost motive last). Motive_i lifted by i.
    // VERBATIM `for (i, mtype) in motive_types.iter().enumerate().rev()`.
    {
        let mut _mo = motive_types.len();
        while _mo > 0 {
            _mo -= 1;
            let i = _mo;
            let mtype = &motive_types[i];
            let lifted_mtype = if i > 0 {
                mtype.lift(usize_to_u32(i))
            } else {
                mtype.clone()
            };
            result_ty = Expr::pi(bi_implicit(), lifted_mtype, result_ty);
        }
    }

    // Add parameters (outermost).
    // VERBATIM `for (_i, (binder_info, param_ty)) in param_binders.iter().enumerate().rev()`.
    {
        let mut _pb = param_binders.len();
        while _pb > 0 {
            _pb -= 1;
            let (binder_info, param_ty) = &param_binders[_pb];
            result_ty = Expr::pi(*binder_info, param_ty.clone(), result_ty);
        }
    }

    // infer_implicit: mark explicit binders Implicit when their bvar appears in a
    // subsequent Pi domain (strict). Ref: lean4-ref/src/kernel/inductive.cpp:767.
    result_ty = result_ty.infer_implicit(true);

    result_ty
}

// ════════════════════════════════════════════════════════════════════════════
// MONO ROOT (#[no_mangle]) — the single closure-free root the emitter picks with
// `--mir-emit-closure build_rec_type_root`. It receives the inductive + per-ctor
// description in a flat, closure-free encoding, reconstructs the slices + CtorInfo,
// calls build_recursor_type, and writes the resulting `Expr` (the full recursor TYPE)
// through the sret pointer (deep-compared native == JIT).
// ════════════════════════════════════════════════════════════════════════════

pub const IND: u32 = 1; // the inductive head I
pub const PARAM0: u32 = 50; // a parameter/type const used for non-recursive fields / param domains
pub const IDX_TY: u32 = 55; // a const used as an index-binder domain (indexed families)
pub const CTOR_BASE: u32 = 100; // ctor names: CTOR_BASE + j for ctor j
pub const ULEVEL: u32 = 7; // the universe level-param name `u`

// Per-ctor flat description the caller flattens; the root rebuilds CtorInfo from it.
#[repr(C)]
pub struct FlatCtor {
    pub name_raw: u32,
    pub num_fields: u32,
    pub recursive_flags_ptr: *const bool,
    pub recursive_flags_len: usize,
    pub field_types_ptr: *const Expr,
    pub field_types_len: usize,
    pub return_indices_ptr: *const Expr,
    pub return_indices_len: usize,
}

#[repr(C)]
pub struct BuildRecTypeArgs {
    pub ind_name_raw: u32,
    pub num_params: u32,
    pub num_indices: u32,
    pub motive_univ_is_some: u32, // 1 => Some(ULEVEL) (large elim); 0 => None (Prop)
    pub ind_type_ptr: *const Expr,
    pub ind_level_params_ptr: *const Name,
    pub ind_level_params_len: usize,
    pub flat_ctors_ptr: *const FlatCtor,
    pub flat_ctors_len: usize,
    pub all_types_ptr: *const InductiveType,
    pub all_types_len: usize,
}

#[no_mangle]
pub extern "C" fn build_rec_type_root(out: *mut Expr, args: *const BuildRecTypeArgs) {
    let a: &BuildRecTypeArgs = unsafe { &*args };
    let ind_type: &Expr = unsafe { &*a.ind_type_ptr };
    let ind_level_params: &[Name] =
        unsafe { std::slice::from_raw_parts(a.ind_level_params_ptr, a.ind_level_params_len) };
    let flat_ctors: &[FlatCtor] =
        unsafe { std::slice::from_raw_parts(a.flat_ctors_ptr, a.flat_ctors_len) };
    let all_types: &[InductiveType] =
        unsafe { std::slice::from_raw_parts(a.all_types_ptr, a.all_types_len) };

    // Rebuild the CtorInfo Vec from the flat per-ctor descriptions.
    let mut ctor_infos: Vec<CtorInfo> = Vec::new();
    {
        let mut j = 0usize;
        while j < flat_ctors.len() {
            let fc = &flat_ctors[j];
            let rf: &[bool] =
                unsafe { std::slice::from_raw_parts(fc.recursive_flags_ptr, fc.recursive_flags_len) };
            let ft: &[Expr] =
                unsafe { std::slice::from_raw_parts(fc.field_types_ptr, fc.field_types_len) };
            let ri: &[Expr] =
                unsafe { std::slice::from_raw_parts(fc.return_indices_ptr, fc.return_indices_len) };
            let mut rf_v: Vec<bool> = Vec::new();
            {
                let mut k = 0usize;
                while k < rf.len() {
                    rf_v.push(rf[k]);
                    k += 1;
                }
            }
            let mut ft_v: Vec<Expr> = Vec::new();
            {
                let mut k = 0usize;
                while k < ft.len() {
                    ft_v.push(ft[k].clone());
                    k += 1;
                }
            }
            let mut ri_v: Vec<Expr> = Vec::new();
            {
                let mut k = 0usize;
                while k < ri.len() {
                    ri_v.push(ri[k].clone());
                    k += 1;
                }
            }
            ctor_infos.push(CtorInfo {
                name: Name(fc.name_raw),
                num_fields: fc.num_fields,
                recursive_flags: rf_v,
                field_types: ft_v,
                return_indices: ri_v,
            });
            j += 1;
        }
    }

    let ind_name = Name(a.ind_name_raw);
    let ulevel = Name(ULEVEL);
    let motive_univ_name: Option<&Name> = if a.motive_univ_is_some != 0 {
        Some(&ulevel)
    } else {
        None
    };

    let result = build_recursor_type(
        &ind_name,
        ind_type,
        a.num_params,
        a.num_indices,
        motive_univ_name,
        ind_level_params,
        &ctor_infos,
        all_types,
    );

    unsafe {
        std::ptr::write(out, result);
    }
}

// ── Caller-side input builders (used by the standalone harness AND mirrored by the
//    native test). NOT part of the emitted root; they may use full Rust. ──

fn ind_head(level_params: &[Name]) -> Expr {
    ind_const_with_levels(&Name(IND), level_params)
}

// Build the field type Expr for a given field_kind:
//   0 => recursive field : I@{u}
//   2 => indexed recursive field : I@{u} #0
//   3 => reflexive recursive field : Π (_:PARAM0). I@{u}  (one Pi binder → n_pis=1)
//   _ => non-recursive Type field : PARAM0
pub fn build_field_ty(field_kind: u8, level_params: &[Name]) -> Expr {
    match field_kind {
        0 => ind_head(level_params),
        2 => {
            let head = ind_head(level_params);
            Expr::app(head, Expr::bvar(0))
        }
        3 => {
            let head = ind_head(level_params);
            Expr::pi(bi_default(), Expr::const_(Name(PARAM0), Vec::new()), head)
        }
        _ => Expr::const_(Name(PARAM0), Vec::new()),
    }
}

pub fn build_level_params() -> Vec<Name> {
    vec![Name(ULEVEL)]
}

// Build ctor_indices (return_indices) from index-kind tags:
//   0 => bvar(0) ; 1 => const PARAM0.
pub fn build_return_indices(kinds: &[u8]) -> Vec<Expr> {
    let mut v: Vec<Expr> = Vec::new();
    let mut i = 0usize;
    while i < kinds.len() {
        if kinds[i] == 0 {
            v.push(Expr::bvar(0));
        } else {
            v.push(Expr::const_(Name(PARAM0), Vec::new()));
        }
        i += 1;
    }
    v
}

// Build an inductive TYPE Pi-telescope: `Π p_0..p_{np-1} : PARAM0. Π i_0..i_{ni-1} : IDX_TY. Sort u`
// (params + indices, then a Sort). This is exactly what `collect_pi_binders`/`count_pi_args`
// scan to recover the param/index binders + arity.
pub fn build_ind_type(np: u32, ni: u32, level_params: &[Name]) -> Expr {
    let mut ty = Expr::sort(Level::Param(level_params[0]));
    // indices innermost
    {
        let mut i = 0u32;
        while i < ni {
            ty = Expr::pi(bi_default(), Expr::const_(Name(IDX_TY), Vec::new()), ty);
            i += 1;
        }
    }
    // params outermost
    {
        let mut i = 0u32;
        while i < np {
            ty = Expr::pi(bi_default(), Expr::const_(Name(PARAM0), Vec::new()), ty);
            i += 1;
        }
    }
    ty
}

// ════════════════════════════════════════════════════════════════════════════
// Standalone re-emit validate harness — exercise the full recursor-type assembly
// across a simple non-parametric inductive (Nat), a parametric one (List), an
// indexed one, and a 2-field non-recursive struct (And), all routed through
// build_rec_type_root, and self-check native == via-root (structure + meta word).
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

// A compact per-ctor spec: (name_raw, field_kinds, recursive_flags, return_index_kinds).
#[derive(Clone)]
struct CtorSpec {
    name_raw: u32,
    field_kinds: Vec<u8>,
    recursive_flags: Vec<bool>,
    return_index_kinds: Vec<u8>,
}

// A compact inductive spec.
#[derive(Clone)]
struct IndSpec {
    num_params: u32,
    num_indices: u32,
    motive_univ_is_some: u32,
    ctors: Vec<CtorSpec>,
}

// Backing store so slices in the args stay alive across the call.
struct Backing {
    ind_type: Box<Expr>,
    level_params: Vec<Name>,
    all_types: Vec<InductiveType>,
    // per-ctor owned data (kept alive; the FlatCtor slices point into these)
    rf: Vec<Vec<bool>>,
    ft: Vec<Vec<Expr>>,
    ri: Vec<Vec<Expr>>,
    flat: Vec<FlatCtor>,
}

fn assemble(spec: &IndSpec) -> Backing {
    let level_params = build_level_params();
    let ind_type = Box::new(build_ind_type(spec.num_params, spec.num_indices, &level_params));

    // Build the all_types mutual block (single inductive I with its ctors).
    let mut ctors_meta: Vec<Ctor> = Vec::new();
    for cs in &spec.ctors {
        ctors_meta.push(Ctor {
            name: Name(cs.name_raw),
            type_: Expr::const_(Name(IND), Vec::new()),
        });
    }
    let all_types = vec![InductiveType {
        name: Name(IND),
        type_: (*ind_type).clone(),
        constructors: ctors_meta,
    }];

    let mut rf: Vec<Vec<bool>> = Vec::new();
    let mut ft: Vec<Vec<Expr>> = Vec::new();
    let mut ri: Vec<Vec<Expr>> = Vec::new();
    for cs in &spec.ctors {
        rf.push(cs.recursive_flags.clone());
        let mut ftv: Vec<Expr> = Vec::new();
        for &k in &cs.field_kinds {
            ftv.push(build_field_ty(k, &level_params));
        }
        ft.push(ftv);
        ri.push(build_return_indices(&cs.return_index_kinds));
    }

    let mut flat: Vec<FlatCtor> = Vec::new();
    for (i, cs) in spec.ctors.iter().enumerate() {
        flat.push(FlatCtor {
            name_raw: cs.name_raw,
            num_fields: cs.field_kinds.len() as u32,
            recursive_flags_ptr: rf[i].as_ptr(),
            recursive_flags_len: rf[i].len(),
            field_types_ptr: ft[i].as_ptr(),
            field_types_len: ft[i].len(),
            return_indices_ptr: ri[i].as_ptr(),
            return_indices_len: ri[i].len(),
        });
    }

    Backing { ind_type, level_params, all_types, rf, ft, ri, flat }
}

// Native oracle: build the CtorInfo Vec + call build_recursor_type directly.
fn native_rec_type(spec: &IndSpec) -> Expr {
    let b = assemble(spec);
    let mut ctor_infos: Vec<CtorInfo> = Vec::new();
    for (i, cs) in spec.ctors.iter().enumerate() {
        ctor_infos.push(CtorInfo {
            name: Name(cs.name_raw),
            num_fields: cs.field_kinds.len() as u32,
            recursive_flags: b.rf[i].clone(),
            field_types: b.ft[i].clone(),
            return_indices: b.ri[i].clone(),
        });
    }
    let ulevel = Name(ULEVEL);
    let motive_univ_name: Option<&Name> = if spec.motive_univ_is_some != 0 {
        Some(&ulevel)
    } else {
        None
    };
    build_recursor_type(
        &Name(IND),
        &b.ind_type,
        spec.num_params,
        spec.num_indices,
        motive_univ_name,
        &b.level_params,
        &ctor_infos,
        &b.all_types,
    )
}

// Via-root: build the args struct + drive the FFI root.
fn root_rec_type(spec: &IndSpec) -> Expr {
    let b = assemble(spec);
    let args = BuildRecTypeArgs {
        ind_name_raw: IND,
        num_params: spec.num_params,
        num_indices: spec.num_indices,
        motive_univ_is_some: spec.motive_univ_is_some,
        ind_type_ptr: &*b.ind_type as *const Expr,
        ind_level_params_ptr: b.level_params.as_ptr(),
        ind_level_params_len: b.level_params.len(),
        flat_ctors_ptr: b.flat.as_ptr(),
        flat_ctors_len: b.flat.len(),
        all_types_ptr: b.all_types.as_ptr(),
        all_types_len: b.all_types.len(),
    };
    let mut slot = std::mem::MaybeUninit::<Expr>::uninit();
    unsafe {
        build_rec_type_root(slot.as_mut_ptr(), &args as *const BuildRecTypeArgs);
        slot.assume_init()
    }
}

// The four canonical test inductives.
fn spec_nat() -> IndSpec {
    IndSpec {
        num_params: 0, num_indices: 0, motive_univ_is_some: 1,
        ctors: vec![
            CtorSpec { name_raw: CTOR_BASE + 0, field_kinds: vec![], recursive_flags: vec![], return_index_kinds: vec![] },
            CtorSpec { name_raw: CTOR_BASE + 1, field_kinds: vec![0], recursive_flags: vec![true], return_index_kinds: vec![] },
        ],
    }
}
fn spec_list() -> IndSpec {
    IndSpec {
        num_params: 1, num_indices: 0, motive_univ_is_some: 1,
        ctors: vec![
            CtorSpec { name_raw: CTOR_BASE + 10, field_kinds: vec![], recursive_flags: vec![], return_index_kinds: vec![] },
            CtorSpec { name_raw: CTOR_BASE + 11, field_kinds: vec![1, 0], recursive_flags: vec![false, true], return_index_kinds: vec![] },
        ],
    }
}
fn spec_and() -> IndSpec {
    IndSpec {
        num_params: 2, num_indices: 0, motive_univ_is_some: 0, // And : Prop-valued (Sort 0 motive)
        ctors: vec![
            CtorSpec { name_raw: CTOR_BASE + 20, field_kinds: vec![1, 1], recursive_flags: vec![false, false], return_index_kinds: vec![] },
        ],
    }
}
fn spec_indexed() -> IndSpec {
    IndSpec {
        num_params: 1, num_indices: 1, motive_univ_is_some: 1,
        ctors: vec![
            CtorSpec { name_raw: CTOR_BASE + 30, field_kinds: vec![2], recursive_flags: vec![true], return_index_kinds: vec![0] },
        ],
    }
}

fn main() {
    let cases: Vec<(IndSpec, &str)> = vec![
        (spec_nat(), "Nat (0 param, 0 index, 2 ctors zero/succ)"),
        (spec_list(), "List (1 param, 0 index, nil/cons)"),
        (spec_and(), "And (2 param, 1 ctor, 2 non-rec fields, Prop)"),
        (spec_indexed(), "Indexed (1 param, 1 index, 1 recursive ctor)"),
    ];
    let mut ok = true;
    for (spec, label) in &cases {
        let native = native_rec_type(spec);
        let viaroot = root_rec_type(spec);
        let eq = deep_eq(&native, &viaroot);
        println!("{label}: meta={:#018x} eq={eq}", native.meta.raw());
        if !eq {
            ok = false;
        }
    }
    std::process::exit((!ok) as i32);
}
