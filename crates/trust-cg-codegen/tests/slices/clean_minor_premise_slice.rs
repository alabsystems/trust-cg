// SELF-CONTAINED clean-kernel RECURSOR MINOR-PREMISE slice — the SOUNDNESS-CRITICAL
// elimination-rule construction `Environment::build_minor_premise_type`
// ($HOME/clean/crates/clean-kernel/src/env/inductive_recursor_minor.rs:33), the function
// that builds the *type* of each minor premise (one per constructor) of an inductive's
// recursor `I.rec`.
//
// WHY A BUG HERE = UNSOUNDNESS. The recursor is the ONLY way to ELIMINATE (use a
// proof/value of) an inductive type. Its type is
//   I.rec : {motives} -> {minor premise per ctor} -> (major : I ..) -> motive .. major
// The MINOR PREMISE for a ctor `c (x:F0) .. : I .. (idx..)` is exactly the proof
// obligation the eliminator demands for that ctor:
//   (x0:F0) .. (xn:Fn) -> (IH for each recursive field) -> motive (idx..) (c x0..xn)
// If this shape is WRONG — e.g. the conclusion uses the wrong motive, the wrong
// indices, the IH is over the wrong motive/major, or a field/IH binder is mis-placed
// in the de-Bruijn telescope — then the recursor is a BOGUS eliminator: a user can
// discharge a too-weak obligation and obtain a proof of a stronger (false) conclusion,
// i.e. a route to `False`. So `build_minor_premise_type` IS a recursor-soundness gate,
// the elimination-rule the already-verified inductive gates (positivity / large-elim /
// ctor-return / decl gate) protect.
//
// Transcribed VERBATIM from $HOME/clean/crates/clean-kernel/src/env/:
//   * build_minor_premise_type            (inductive_recursor_minor.rs:33)  — THE FN
//   * field_motive_index                  (inductive_recursor_types.rs:45)  — pillar
//   * get_constructor_return_indices      (inductive_recursor.rs:951)       — pillar (App-spine + Pi-telescope)
//   * count_pi_binders                    (inductive_recursor_rules.rs:24)  — pillar
//   * collect_pi_domains                  (inductive_recursor_rules.rs:39)  — pillar
//   * remap_residual_index_bvars_for_minor(inductive_recursor_rules.rs:94)  — pillar (BVar remap)
//   * get_return_type                     (inductive/mod.rs:650)            — pillar (Pi-telescope)
//   * get_app_fn                          (expr/constructors.rs:256)        — VERIFIED pillar
//   * ind_const_with_levels               (inductive_fixed_indices.rs:266)  — Const ctor helper
//   * usize_to_u32                        (env/mod.rs:3054)                 — helper
//
// COMPOSED VERIFIED CONSTRUCTION PILLARS (over the REAL hashconsed Expr/ExprMeta):
//   - Expr::{bvar,app,lam,pi,const_} -> from_kind -> compute_meta -> mk_app_meta /
//     mk_binder_meta / pack / mix_hash / KaniHasher  (the VERBATIM construction core
//     from clean_expr_construction_slice.rs — Arc::new children lower to heap_alloc).
//   - Expr::lift / lift_from -> lift_at  (the VERIFIED de-Bruijn lift; WRITE primitive
//     from clean_expr_{construction,instantiate}_slice.rs).
//   - get_app_fn (the VERIFIED App-spine head walk, reused by field_motive_index).
//
// FAITHFULNESS / control flow is VERBATIM the real `build_minor_premise_type`:
//   conclusion = motive_c (ctor_indices..) (ctor field..); add IH binders for the
//   recursive fields (reverse order, each with the field's motive index, n_pis Pi-wrap
//   for reflexive fields, remapped index args, the (field xs) major); add the field
//   binders outermost (each lifted by num_motives at depth i). Every BVar depth, every
//   lift_from / lift, every Pi/App is byte-for-byte the real arithmetic.
//
// MODELING boundary:
//   * `InductiveType` -> a minimal `{name: Name, ctors: Vec<Ctor>}` where
//     `Ctor{name,type_}` — exactly the fields `field_motive_index` reads (`.name`) and
//     the only struct the fn touches via `all_types`. The fn NEVER reads anything else.
//   * BinderInfo::Default / Implicit -> the real BinderData {info,mult} scalar pair
//     (the real `Expr::pi(BinderInfo, ..)` lowers `BinderInfo` to this; modeled
//     directly as the scalar the constructor stores).
//   * `consume_type_annotations` is NOT on this fn's path (the fn takes already-stripped
//     `field_types`/`ctor_indices` from its caller `build_recursor_type`), so it is not
//     modeled — the slice receives the field/index Exprs the real caller would pass.
//   * Leaf-payload Hash (Name/Level/Literal) is MODELED exactly as the verified
//     construction slice (KaniHasher seeds present verbatim; off the App/Pi/BVar/Const
//     construction-path hashing this fn drives, which is 100% mix_hash integer mixing).
//
// Crate name is load-bearing (appears in the mangled extern symbols the JIT binds):
// it MUST stay `clean_minor_premise_slice`.

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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BinderData {
    pub info: u8,
    pub mult: u8,
}

// BinderInfo::Default / Implicit -> the scalar BinderData the real constructor stores.
// Built as RUNTIME locals (NOT `const` items): the real `Expr::pi(BinderInfo::Default,..)`
// passes a freshly-`Into`-converted `BinderData`, and the frontend lowers a struct-adt
// only as a runtime aggregate (a struct-adt *constant* call-arg cannot lower). These
// `#[inline]` fns return the same scalar pair as `BinderInfo::Default.into()`.
#[inline]
fn bi_default() -> BinderData {
    BinderData { info: 0, mult: 0 }
}
#[inline]
fn bi_implicit() -> BinderData {
    BinderData { info: 1, mult: 0 }
}

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
            // ── CONSTRUCTION ARMS (reached by build_minor_premise_type) — VERBATIM ──
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
            ExprKind::Const(name, _levels) => {
                // MODELED: real arm hashes `levels` via hash_to_u64 + iterates for
                // has_params/has_mvar. Off the verified path; the construction here
                // builds Const with level-PARAM vecs (ctor levels = Param(p)). To stay
                // faithful for has_level_param we OR in the param flag verbatim below.
                let name_hash = hash_name(name);
                // VERBATIM the real `levels.iter().any(|l| l.has_params())` — lowered
                // to the equivalent explicit loop (the `Iterator::any` adapter does not
                // lower in this closure context). Semantically identical: true iff any
                // level is a `Param`. This keeps the has_level_param meta bit faithful
                // for the Const(ctor, [Param(u)..]) nodes this construction path builds.
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
            ExprKind::Sort(lvl) => ExprMeta::pack(
                mix_hash(11, hash_level(lvl)) as u32,
                0,
                0,
                false,
                false,
                level_has_mvar(lvl),
                lvl.has_params(),
            ),
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
// subst.rs — VERBATIM lift_at (the VERIFIED de-Bruijn lift; lift = lift_at(0,n),
// lift_from(s,n) = lift_at(s,n)). Direct-recursion form (FoldMemo deferred — a
// no-op on a tree). `checked_add_u32` -> saturating_add (its real not(kani) body).
// ════════════════════════════════════════════════════════════════════════════

#[inline]
pub(crate) fn checked_add_u32(a: u32, b: u32) -> u32 {
    a.saturating_add(b)
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
}

// ════════════════════════════════════════════════════════════════════════════
// MODELED InductiveType — the minimal struct `build_minor_premise_type` reads via
// `all_types` (only `.name` for field_motive_index; constructors carry `.name`/`.type_`
// for the HIT path-data path which this fn never calls). Exactly the real fields used.
// ════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Debug)]
pub struct Ctor {
    pub name: Name,
    pub type_: Expr,
}

#[derive(Clone, Debug)]
pub struct InductiveType {
    pub name: Name,
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
// The Environment-method PILLARS (transcribed as free fns over the modeled types;
// the real ones are `impl Environment` but take no `self` state on this path —
// build_minor_premise_type only uses `self` to reach these associated fns).
// ════════════════════════════════════════════════════════════════════════════

#[inline]
fn usize_to_u32(value: usize) -> u32 {
    u32::try_from(value).unwrap_or(u32::MAX)
}

// VERBATIM `field_motive_index` (inductive_recursor_types.rs:45).
pub(crate) fn field_motive_index(field_ty: &Expr, all_types: &[InductiveType]) -> usize {
    let ret_ty = get_return_type(field_ty);
    let head = ret_ty.get_app_fn();
    if let ExprKind::Const(name, _) = &head.kind {
        // VERBATIM `for (idx, ind_type) in all_types.iter().enumerate()` — index loop
        // (identical: idx = enumerate index over the mutual block, in order).
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

// VERBATIM `get_constructor_return_indices` (inductive_recursor.rs:951).
// (consume_type_annotations is upstream of the field/index Exprs the caller passes;
// not on THIS fn's path.) Pure App-spine + Pi-telescope scan.
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
    // args were collected rightmost-first; VERBATIM `args.reverse()` then
    // `args.into_iter().skip(num_params).collect()` — lowered to a single forward
    // emit loop over the reversed (source-order) indices, skipping the first
    // num_params (the parameters), keeping the rest (the indices). Identical result.
    let np = num_params as usize;
    let n = args.len();
    let mut out: Vec<Expr> = Vec::new();
    {
        // source order index s = n-1-j for the j-th collected (rightmost-first) arg.
        let mut s = 0usize;
        while s < n {
            if s >= np {
                // the (n-1-s)-th collected element is the s-th in source order.
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
// THE SOUNDNESS-CRITICAL FN — `build_minor_premise_type`, VERBATIM from
// inductive_recursor_minor.rs:33. The `&self` (Environment) is dropped: on this
// path it is used ONLY to reach `self.get_constructor_return_indices` (a pillar
// transcribed above as a free fn). `Level::param`/`Expr::const_`/`Expr::bvar`/
// `Expr::app`/`Expr::pi`/`lift`/`lift_from` are the verified construction/lift
// pillars; `BinderInfo::Default` -> `BI_DEFAULT` (the scalar the ctor stores).
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
    // VERBATIM `recursive_flags.iter().filter(|&&b| b).count()` — lowered to the
    // equivalent explicit count loop (the frontend does not lower the `Filter::count`
    // iterator-adapter in this closure context; the loop is semantically identical:
    // it counts the `true` flags = the number of IH parameters).
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

    // Build ctor applied to all field arguments.
    // VERBATIM `ind_level_params.iter().map(|p| Level::param(p.clone())).collect()` —
    // the `map().collect()` adapter is lowered to the equivalent push loop (identical:
    // one Level::Param per level-param, in order).
    let mut ctor_levels: Vec<Level> = Vec::new();
    {
        let mut _pi = 0usize;
        while _pi < ind_level_params.len() {
            ctor_levels.push(Level::Param(ind_level_params[_pi]));
            _pi += 1;
        }
    }
    let mut ctor_app = Expr::const_(*ctor_name, ctor_levels);
    // VERBATIM `for i in 0..num_params` / `for i in 0..num_fields` — ascending while
    // loops (identical; avoids the Range iterator-adapter externs the JIT cannot bind).
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

    // Build conclusion: motive_c indices (ctor fields).
    // VERBATIM `for idx_expr in ctor_indices` — lowered to an index loop (identical).
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

    // Add IH binders for recursive arguments (in reverse order).
    // VERBATIM `for (i, &is_recursive) in recursive_flags.iter().enumerate().rev()` —
    // lowered to a descending index loop (identical: i runs num_fields-1..=0, the
    // `enumerate` index, in reverse — the `.rev()` adapter — with `is_recursive`
    // = recursive_flags[i]).
    let mut ih_offset = 0usize;
    let mut _ri = recursive_flags.len();
    while _ri > 0 {
        _ri -= 1;
        let i = _ri;
        let is_recursive = recursive_flags[i];
        if is_recursive {
            let ihs_above = num_ihs - 1 - ih_offset;
            let field_depth = (num_fields - 1 - i) + ihs_above;

            // VERBATIM `field_types.get(i).map(|ft| field_motive_index(ft,all_types))
            //   .unwrap_or(conclusion_motive_idx)` — explicit match (identical: the
            // Some/None of the `.get(i)` Option, the `.map` then `.unwrap_or`).
            let ih_motive_idx = match field_types.get(i) {
                Some(ft) => field_motive_index(ft, all_types),
                None => conclusion_motive_idx,
            };
            let motive_at_ih = num_fields + ihs_above + (num_motives - 1 - ih_motive_idx);

            // VERBATIM `field_types.get(i).map(Self::count_pi_binders).unwrap_or(0)`.
            let n_pis = match field_types.get(i) {
                Some(ft) => count_pi_binders(ft),
                None => 0,
            };

            let ih_motive = motive_at_ih + n_pis;
            let ih_field_depth = field_depth + n_pis;

            let mut ih_type = Expr::bvar(usize_to_u32(ih_motive));

            // VERBATIM `field_types.get(i).cloned().unwrap_or_else(|| ind_const_..)` —
            // explicit match (identical: clone the field type or the ind const fallback).
            let field_ty = match field_types.get(i) {
                Some(ft) => ft.clone(),
                None => ind_const_with_levels(ind_name, ind_level_params),
            };
            let field_indices = get_constructor_return_indices(&field_ty, num_params);
            // VERBATIM `for idx_expr in &field_indices` — index loop (identical).
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
            // VERBATIM `for k in (0..n_pis).rev()` — descending while loop (identical:
            // k runs n_pis-1..=0).
            {
                let mut _k = n_pis;
                while _k > 0 {
                    _k -= 1;
                    major = Expr::app(major, Expr::bvar(usize_to_u32(_k)));
                }
            }
            ih_type = Expr::app(ih_type, major);

            // VERBATIM `field_types.get(i).map(Self::collect_pi_domains)
            //   .unwrap_or_default()` — explicit match (identical: empty Vec on None).
            let pi_domains = match field_types.get(i) {
                Some(ft) => collect_pi_domains(ft),
                None => Vec::new(),
            };
            // VERBATIM `for (k, (bi, domain)) in pi_domains.iter().enumerate().rev()` —
            // descending index loop (identical: k = enumerate index, in reverse).
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

    // Add field binders (outermost), using constructor field types.
    // VERBATIM `for i in (0..num_fields).rev()` — descending while loop (identical).
    {
        let mut _fb = num_fields;
        while _fb > 0 {
            _fb -= 1;
            let i = _fb;
            // VERBATIM `field_types.get(i).cloned().unwrap_or_else(|| ind_const_..)`.
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
// MONO ROOT (#[no_mangle]) — the single closure-free root the emitter picks with
// `--mir-emit-closure build_minor_root`. It receives the constructor description
// in a flat, closure-free encoding (the same data `build_recursor_type` threads
// per ctor), reconstructs the slices, calls build_minor_premise_type, and writes
// the resulting `Expr` through the sret pointer (deep-compared native == JIT).
//
// Encoding (all heap-backed Vecs, fat-pointer slices at the boundary):
//   field_kinds[i]: which field type Expr to use for field i —
//     0 => the inductive head `I` (a recursive field, type = ind_const)
//     1 => the param const `PARAM0`  (a non-recursive Type field)
//     2 => an indexed recursive field `I` applied to one bvar index (indexed family)
//   recursive_flags[i]: whether field i is recursive (IH generated)
//   ctor_index_kinds[j]: 0 => bvar(field_bvar for field 0) ; 1 => a const PARAM0
// This covers: non-recursive fields, direct recursion (Nat.succ shape), multiple
// recursive fields (binary node), and an indexed family with a return-index arg.
// ════════════════════════════════════════════════════════════════════════════

pub const IND: u32 = 1; // the inductive head I
pub const PARAM0: u32 = 50; // a parameter/type const used for non-recursive fields
pub const CTORN: u32 = 100; // the constructor name
pub const ULEVEL: u32 = 7; // the universe level-param name `u`

// All composite inputs in ONE struct, passed to the root BY POINTER — a 2-arg ABI
// (out-sret, args-ptr) with NO stack-passed args (16 flat args overflow the 8 arg
// registers, and the u32/u64 stack-slot packing differs between the JIT and the
// host C ABI — passing one struct pointer sidesteps that entirely). The caller (test
// / harness) builds this with full Rust; the root just reads the slices out of it.
#[repr(C)]
pub struct BuildMinorArgs {
    pub ctor_name_raw: u32,
    pub num_fields: u32,
    pub num_params: u32,
    pub num_motives: u32,
    pub conclusion_motive_idx: u32,
    pub recursive_flags_ptr: *const bool,
    pub recursive_flags_len: usize,
    pub field_types_ptr: *const Expr,
    pub field_types_len: usize,
    pub ind_level_params_ptr: *const Name,
    pub ind_level_params_len: usize,
    pub ctor_indices_ptr: *const Expr,
    pub ctor_indices_len: usize,
    pub all_types_ptr: *const InductiveType,
    pub all_types_len: usize,
}

// The MONO ROOT: reconstruct the slices from the args struct, call the verified fn,
// write the resulting `Expr` through the sret pointer for a native==JIT deep-compare.
// Mirrors the verified `Expr__lift_at` construction rung (caller builds inputs, the
// constructing fn is emitted, the result is returned by sret).
#[no_mangle]
pub extern "C" fn build_minor_root(out: *mut Expr, args: *const BuildMinorArgs) {
    let a: &BuildMinorArgs = unsafe { &*args };
    let recursive_flags: &[bool] =
        unsafe { std::slice::from_raw_parts(a.recursive_flags_ptr, a.recursive_flags_len) };
    let field_types: &[Expr] =
        unsafe { std::slice::from_raw_parts(a.field_types_ptr, a.field_types_len) };
    let ind_level_params: &[Name] =
        unsafe { std::slice::from_raw_parts(a.ind_level_params_ptr, a.ind_level_params_len) };
    let ctor_indices: &[Expr] =
        unsafe { std::slice::from_raw_parts(a.ctor_indices_ptr, a.ctor_indices_len) };
    let all_types: &[InductiveType] =
        unsafe { std::slice::from_raw_parts(a.all_types_ptr, a.all_types_len) };

    let ind_name = Name(IND);
    let ctor_name = Name(a.ctor_name_raw);

    let result = build_minor_premise_type(
        &ind_name,
        &ctor_name,
        a.num_fields,
        recursive_flags,
        field_types,
        a.num_params,
        ind_level_params,
        ctor_indices,
        a.num_motives as usize,
        a.conclusion_motive_idx as usize,
        all_types,
    );

    unsafe {
        std::ptr::write(out, result);
    }
}

// ── Caller-side input builders (used by the standalone harness AND mirrored by the
//    native test). NOT part of the emitted root; they may use full Rust. ──

// Build the field type Expr for a given `field_kind`:
//   0 => recursive field : I@{u}            (the inductive head, level-param u)
//   2 => indexed recursive field : I@{u} #0 (one return-index arg)
//   _ => non-recursive Type field : PARAM0
pub fn build_field_ty(field_kind: u8, ind_level_params: &[Name]) -> Expr {
    match field_kind {
        0 => ind_const_with_levels(&Name(IND), ind_level_params),
        2 => {
            let head = ind_const_with_levels(&Name(IND), ind_level_params);
            Expr::app(head, Expr::bvar(0))
        }
        _ => Expr::const_(Name(PARAM0), Vec::new()),
    }
}

// The modeled single-inductive mutual block (just I with its one ctor).
pub fn build_all_types() -> Vec<InductiveType> {
    vec![InductiveType {
        name: Name(IND),
        constructors: vec![Ctor {
            name: Name(CTORN),
            type_: Expr::const_(Name(IND), Vec::new()),
        }],
    }]
}

// The modeled level-param list `[u]`.
pub fn build_level_params() -> Vec<Name> {
    vec![Name(ULEVEL)]
}

// Build ctor_indices from index-kind tags: 0 => bvar(0) (a field-0 ref the
// adjust_index_expr re-targets) ; 1 => const PARAM0.
pub fn build_ctor_indices(ctor_index_kinds: &[u8]) -> Vec<Expr> {
    ctor_index_kinds
        .iter()
        .map(|&k| {
            if k == 0 {
                Expr::bvar(0)
            } else {
                Expr::const_(Name(PARAM0), Vec::new())
            }
        })
        .collect()
}

// ════════════════════════════════════════════════════════════════════════════
// Standalone re-emit validate harness — exercise the minor-premise builder across
// non-recursive, direct-recursive, binary-node, and indexed-family ctor shapes,
// all routed through build_minor_root, and self-check the resulting meta word.
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

// Caller-side input assembly (used by BOTH the native oracle and the root path) —
// builds the composite slices from the compact tag encoding.
fn assemble(
    field_kinds: &[u8],
    ctor_index_kinds: &[u8],
) -> (Vec<Name>, Vec<Expr>, Vec<Expr>, Vec<InductiveType>) {
    let ind_level_params = build_level_params();
    let field_types: Vec<Expr> = field_kinds
        .iter()
        .map(|&k| build_field_ty(k, &ind_level_params))
        .collect();
    let ctor_indices = build_ctor_indices(ctor_index_kinds);
    let all_types = build_all_types();
    (ind_level_params, field_types, ctor_indices, all_types)
}

// Native oracle: call build_minor_premise_type directly (mirror of build_minor_root
// minus the FFI/sret), for the standalone harness self-check.
fn native_minor(
    field_kinds: &[u8],
    recursive_flags: &[bool],
    ctor_index_kinds: &[u8],
    num_params: u32,
    num_motives: u32,
    conclusion_motive_idx: u32,
) -> Expr {
    let (ind_level_params, field_types, ctor_indices, all_types) =
        assemble(field_kinds, ctor_index_kinds);
    let num_fields = field_types.len() as u32;
    build_minor_premise_type(
        &Name(IND),
        &Name(CTORN),
        num_fields,
        recursive_flags,
        &field_types,
        num_params,
        &ind_level_params,
        &ctor_indices,
        num_motives as usize,
        conclusion_motive_idx as usize,
        &all_types,
    )
}

fn root_to_expr(
    field_kinds: &[u8],
    recursive_flags: &[bool],
    ctor_index_kinds: &[u8],
    num_params: u32,
    num_motives: u32,
    conclusion_motive_idx: u32,
) -> Expr {
    let (ind_level_params, field_types, ctor_indices, all_types) =
        assemble(field_kinds, ctor_index_kinds);
    let num_fields = field_types.len() as u32;
    let args = BuildMinorArgs {
        ctor_name_raw: CTORN,
        num_fields,
        num_params,
        num_motives,
        conclusion_motive_idx,
        recursive_flags_ptr: recursive_flags.as_ptr(),
        recursive_flags_len: recursive_flags.len(),
        field_types_ptr: field_types.as_ptr(),
        field_types_len: field_types.len(),
        ind_level_params_ptr: ind_level_params.as_ptr(),
        ind_level_params_len: ind_level_params.len(),
        ctor_indices_ptr: ctor_indices.as_ptr(),
        ctor_indices_len: ctor_indices.len(),
        all_types_ptr: all_types.as_ptr(),
        all_types_len: all_types.len(),
    };
    let mut slot = std::mem::MaybeUninit::<Expr>::uninit();
    unsafe {
        build_minor_root(slot.as_mut_ptr(), &args as *const BuildMinorArgs);
        slot.assume_init()
    }
}

fn main() {
    // (field_kinds, recursive_flags, ctor_index_kinds, num_params, num_motives, motive_idx, label)
    let cases: Vec<(Vec<u8>, Vec<bool>, Vec<u8>, u32, u32, u32, &str)> = vec![
        // Nat.zero-like: no fields → conclusion motive (ctor) only.
        (vec![], vec![], vec![], 0, 1, 0, "nullary ctor (Nat.zero shape)"),
        // Nat.succ-like: one recursive field → (n:Nat) -> motive n -> motive (succ n).
        (vec![0], vec![true], vec![], 0, 1, 0, "one recursive field (Nat.succ shape)"),
        // List.cons-like (1 param): non-recursive head + recursive tail.
        (vec![1, 0], vec![false, true], vec![], 1, 1, 0, "head + recursive tail (cons shape)"),
        // binary node: two recursive fields → two IH binders.
        (vec![0, 0], vec![true, true], vec![], 0, 1, 0, "two recursive fields (binary node)"),
        // non-recursive 2-field ctor (And.intro-like): no IHs.
        (vec![1, 1], vec![false, false], vec![], 0, 1, 0, "two non-recursive fields (no IH)"),
        // indexed family: recursive field of type `I (bvar)`, one return index arg.
        (vec![2], vec![true], vec![0], 1, 1, 0, "indexed recursive field + return index"),
        // mutual block (num_motives=2): a recursive field still selects motive 0.
        (vec![0], vec![true], vec![], 0, 2, 0, "mutual block, recursive field, motive 0"),
    ];

    let mut ok = true;
    for (fk, rf, cik, np, nm, mi, label) in &cases {
        let native = native_minor(fk, rf, cik, *np, *nm, *mi);
        let viaroot = root_to_expr(fk, rf, cik, *np, *nm, *mi);
        let eq = deep_eq(&native, &viaroot);
        println!(
            "{label}: meta={:#018x} eq={eq}",
            native.meta.raw()
        );
        if !eq {
            ok = false;
        }
    }
    std::process::exit((!ok) as i32);
}
