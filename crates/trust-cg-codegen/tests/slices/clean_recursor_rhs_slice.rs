// SELF-CONTAINED clean-kernel RECURSOR IOTA-RULE RHS slice — the SOUNDNESS-CRITICAL
// iota-computation-rule construction `Environment::build_recursor_rule_rhs`
// ($HOME/clean/crates/clean-kernel/src/env/inductive_recursor_rules.rs:148), the companion
// to the just-verified `build_minor_premise_type`. It builds the RIGHT-HAND SIDE of the
// recursor's iota (computation) rule — i.e. what
//   I.rec C minor_0 .. minor_{k-1} (I.ctor_j args..)
// REDUCES TO.
//
// WHY A BUG HERE = UNSOUNDNESS. The iota rule is the *computation rule* for the
// eliminator: it defines how `I.rec` actually COMPUTES on a constructor. Its RHS is
//   λ params. λ motives. λ minors. λ fields.
//     minor_j field_0 .. field_{n-1} IH_0 .. IH_m
// where each IH_r for a recursive field is `I.rec params motives minors [indices] field_r`
// (i.e. the recursor applied to the recursive subterm — the induction hypothesis). If this
// RHS SHAPE is WRONG — wrong minor selected, fields applied in the wrong de-Bruijn order,
// an IH built over the wrong recursor / wrong recursive field / wrong index args, a
// mis-lifted field-type binder — then `I.rec` COMPUTES THE WRONG THING. A wrong iota
// reduction is a definitional-equality unsoundness: two terms the kernel deems equal (via
// the bogus reduction) are not; a user can then transport a proof along a false equation
// and reach `False`. So `build_recursor_rule_rhs` IS the recursor's *computation*-rule
// soundness gate — the exact companion of the *elimination*-rule gate
// `build_minor_premise_type` (which builds the minor-premise TYPE); together with
// positivity / large-elim / ctor-return / decl-gate they are the complete inductive
// soundness picture.
//
// Transcribed VERBATIM from $HOME/clean/crates/clean-kernel/src/env/:
//   * build_recursor_rule_rhs             (inductive_recursor_rules.rs:148) — THE FN
//   * count_pi_binders                    (inductive_recursor_rules.rs:24)  — pillar
//   * collect_pi_domains                  (inductive_recursor_rules.rs:39)  — pillar
//   * remap_residual_index_bvars          (inductive_recursor_rules.rs:51)  — pillar (BVar remap; the
//                                          NON-minor variant, distinct from _for_minor)
//   * get_constructor_return_indices      (inductive_recursor.rs:951)       — pillar (App-spine + Pi-telescope)
//   * get_return_type                     (inductive/mod.rs:650)            — pillar (Pi-telescope)
//   * get_app_fn                          (expr/constructors.rs:256)        — VERIFIED pillar (App-spine head)
//   * usize_to_u32                        (env/mod.rs)                      — helper
//
// COMPOSED VERIFIED CONSTRUCTION PILLARS (over the REAL hashconsed Expr/ExprMeta):
//   - Expr::{bvar,app,lam,pi,const_,sort} -> from_kind -> compute_meta -> mk_app_meta /
//     mk_binder_meta / pack / mix_hash / KaniHasher  (the VERBATIM construction core
//     from clean_expr_construction_slice.rs — Arc::new children lower to heap_alloc).
//   - Expr::lift_from -> lift_at  (the VERIFIED de-Bruijn lift).
//   - get_app_fn (the VERIFIED App-spine head walk, reused by the mutual ih_rec_name path).
//
// FAITHFULNESS / control flow is VERBATIM the real `build_recursor_rule_rhs`:
//   body = minor_k; apply all fields (outermost..innermost); for each recursive field add
//   an IH = rec@{levels} params motives minors [remapped indices] (field xs), wrapped in
//   n_pis lambdas for reflexive fields; then wrap the whole body in λ params λ motives
//   λ minors λ fields, using the ACTUAL domain types read from the eliminator type's Pi
//   telescope (dummy Sort(0) only when the telescope is shorter than expected), lifting
//   each field type by (nm + n_minors) at depth i. Every BVar depth, every lift_from, every
//   Pi/App/Lam/Sort is byte-for-byte the real arithmetic.
//
// MODELING boundary:
//   * `InductiveType` -> a minimal `{name: Name, constructors:[{name,type_}]}` — exactly
//     the fields the fn reads. On the JIT-verified path `all_types.len() == 1`, so the
//     `all_types.len() > 1` mutual branch (which calls `Name::from_string(format!("{name}.rec"))`
//     — real string interning) is NOT taken: `ih_rec_name == rec_name.clone()`. The mutual
//     rec-name-derivation path is DOCUMENTED as modeled-out (single-inductive families are
//     the exercised, soundness-covered cases; a wrong single-inductive iota RHS is already a
//     route to False). The get_return_type/get_app_fn head-walk inside that branch is still
//     transcribed verbatim so the branch is faithful were it ever taken with a synthesized name.
//   * BinderInfo::Default -> the real BinderData {info,mult} scalar pair the ctor stores.
//   * Leaf-payload Hash (Name/Level/Literal) MODELED exactly as the verified construction
//     slice (KaniHasher seeds verbatim; off the App/Pi/Lam/BVar/Const/Sort construction path
//     this fn drives, which is 100% mix_hash integer mixing).
//
// Crate name is load-bearing (it appears in the mangled extern symbols the JIT binds):
// it MUST stay `clean_recursor_rhs_slice`.

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
    // VERBATIM `Level::zero` (level/mod.rs:259).
    pub fn zero() -> Self {
        Level::Zero
    }
    // VERBATIM `Level::param` (level/mod.rs:357).
    pub fn param(name: Name) -> Self {
        Level::Param(name)
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

// BinderInfo::Default -> the scalar BinderData the real constructor stores.
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
            // ── CONSTRUCTION ARMS (reached by build_recursor_rule_rhs) — VERBATIM ──
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
                let name_hash = hash_name(name);
                // VERBATIM `levels.iter().any(|l| l.has_params())` — explicit loop.
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
            // Sort arm — reached by the `dummy_ty = Expr::sort(Level::zero())` fallback
            // and any Sort domain read from the eliminator type. VERBATIM the real arm.
            ExprKind::Sort(lvl) => ExprMeta::pack(
                mix_hash(11, hash_level(lvl)) as u32,
                0,
                0,
                false,
                false,
                level_has_mvar(lvl),
                lvl.has_params(),
            ),
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
// subst.rs — VERBATIM lift_at (the VERIFIED de-Bruijn lift; lift_from(s,n) = lift_at(s,n)).
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
    // head walk (reused by the mutual ih_rec_name derivation).
    pub fn get_app_fn(&self) -> &Expr {
        let mut current = self;
        while let ExprKind::App(f, _) = &current.kind {
            current = f;
        }
        current
    }
}

// ════════════════════════════════════════════════════════════════════════════
// MODELED InductiveType — the minimal struct build_recursor_rule_rhs reads via
// `all_types` (`.len()` for the mutual test; `.name`/`.type_` in the mutual head-walk).
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

// VERBATIM `get_return_type` (inductive/mod.rs:650) — walk past the Pi telescope.
pub(crate) fn get_return_type(expr: &Expr) -> &Expr {
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = &current.kind {
        current = body;
    }
    current
}

// ════════════════════════════════════════════════════════════════════════════
// The Environment-method PILLARS (free fns over the modeled types — the real ones
// are `impl Environment` but take no `self` STATE on this path; build_recursor_rule_rhs
// uses `self` only to reach `self.get_constructor_return_indices`).
// ════════════════════════════════════════════════════════════════════════════

#[inline]
fn usize_to_u32(value: usize) -> u32 {
    u32::try_from(value).unwrap_or(u32::MAX)
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
    // `.into_iter().skip(num_params).collect()` — single forward emit over the
    // reversed (source-order) indices, skipping the first num_params.
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

// VERBATIM `remap_residual_index_bvars` (inductive_recursor_rules.rs:51) — the
// NON-minor variant (distinct arithmetic from _for_minor).
pub(crate) fn remap_residual_index_bvars(
    expr: &Expr,
    field_idx: usize,
    np: usize,
    nf: usize,
    n_minors: usize,
    nm: usize,
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
                    nf - 1 - field_j + n_pis
                } else {
                    let param_j = np - 1 - (ctor_k - field_idx);
                    nf + n_minors + nm + np - 1 - param_j + n_pis
                }
            };
            Expr::bvar(usize_to_u32(new_k))
        }
        ExprKind::App(f, a) => {
            let f2 = remap_residual_index_bvars(f, field_idx, np, nf, n_minors, nm, n_pis);
            let a2 = remap_residual_index_bvars(a, field_idx, np, nf, n_minors, nm, n_pis);
            Expr::app(f2, a2)
        }
        _ => expr.clone(),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// THE SOUNDNESS-CRITICAL FN — `build_recursor_rule_rhs`, VERBATIM from
// inductive_recursor_rules.rs:148. The `&self` (Environment) is dropped: on this
// path it is used ONLY to reach `self.get_constructor_return_indices` (transcribed
// as a free fn). `Level::param`/`Expr::{const_,bvar,app,lam,pi,sort}`/`lift_from` are
// the verified construction/lift pillars; `BinderInfo::Default` -> `bi_default()`.
//
// NOTE ON THE MUTUAL BRANCH: on the JIT-verified path `all_types.len() == 1`, so the
// `all_types.len() > 1` branch (which calls `Name::from_string(format!("{name}.rec"))`,
// real string interning, MODELED-OUT) is NOT taken; `ih_rec_name = rec_name.clone()`.
// The head-walk inside the branch (get_return_type/get_app_fn) is transcribed verbatim
// for faithfulness, and a synthesized modeled `Name` is used in place of from_string so
// the branch is exercisable in the (documented, non-JIT-verified) mutual harness case.
// ════════════════════════════════════════════════════════════════════════════

// Model of `Name::from_string(&format!("{name}.rec"))`: the real path splits on '.' and
// interns; DOCUMENTED as modeled-out. For the (non-JIT-verified) mutual harness we derive
// a distinct rec-name deterministically from the head name so the branch is exercisable.
#[inline]
fn synth_rec_name(head: &Name) -> Name {
    Name(head.0 ^ 0x5245_4300) // "REC" tag XOR — a deterministic distinct rec name
}

#[allow(clippy::too_many_arguments)]
pub fn build_recursor_rule_rhs(
    rec_name: &Name,
    rec_level_params: &[Name],
    num_params: u32,
    num_motives: u32,
    num_indices: u32,
    num_fields: u32,
    recursive_flags: &[bool],
    field_types: &[Expr],
    num_ctors: usize,
    ctor_idx: usize,
    eliminator_type: &Expr,
    all_types: &[InductiveType],
) -> Expr {
    let nf = num_fields as usize;
    let np = num_params as usize;
    let nm = num_motives as usize;
    let n_minors = num_ctors;
    let total_binders = np + nm + n_minors + nf;

    // minor for ctor_idx (minors go minor_0 outermost .. minor_{n-1} innermost).
    let minor_bvar = usize_to_u32(nf + n_minors - 1 - ctor_idx);
    let mut body = Expr::bvar(minor_bvar);

    // Apply all fields to minor: minor field_0 .. field_{nf-1}.
    // VERBATIM `for i in 0..nf` — ascending while loop.
    {
        let mut i: usize = 0;
        while i < nf {
            let field_bvar = usize_to_u32(nf - 1 - i);
            body = Expr::app(body, Expr::bvar(field_bvar));
            i += 1;
        }
    }

    // rec_levels = rec_level_params.iter().map(|n| Level::param(n.clone())).collect()
    // VERBATIM — explicit push loop.
    let mut rec_levels: Vec<Level> = Vec::new();
    {
        let mut _li = 0usize;
        while _li < rec_level_params.len() {
            rec_levels.push(Level::param(rec_level_params[_li]));
            _li += 1;
        }
    }

    // Apply IH for each recursive field.
    // VERBATIM `for (i, &is_recursive) in recursive_flags.iter().enumerate()` — ascending index loop.
    {
        let mut i: usize = 0;
        while i < recursive_flags.len() {
            let is_recursive = recursive_flags[i];
            if is_recursive {
                // n_pis = field_types.get(i).map(count_pi_binders).unwrap_or(0)
                let n_pis = match field_types.get(i) {
                    Some(ft) => count_pi_binders(ft),
                    None => 0,
                };
                let shift = n_pis;

                // ih_rec_name: mutual (all_types.len() > 1) walks the field return head;
                // single-inductive uses rec_name.clone(). VERBATIM control flow.
                let ih_rec_name = if all_types.len() > 1 {
                    match field_types.get(i) {
                        Some(field_ty) => {
                            let ret_ty = get_return_type(field_ty);
                            let head = ret_ty.get_app_fn();
                            match &head.kind {
                                ExprKind::Const(name, _) => synth_rec_name(name),
                                _ => *rec_name,
                            }
                        }
                        None => *rec_name,
                    }
                } else {
                    *rec_name
                };

                // ih = ih_rec@{levels} params motives minors [indices] (field xs)
                let mut ih = Expr::const_(ih_rec_name, rec_levels.clone());

                // Apply params (outermost group).
                // VERBATIM `for j in 0..np`.
                {
                    let mut j: usize = 0;
                    while j < np {
                        let param_bvar = usize_to_u32(total_binders - 1 - j + shift);
                        ih = Expr::app(ih, Expr::bvar(param_bvar));
                        j += 1;
                    }
                }
                // Apply motives.
                {
                    let mut j: usize = 0;
                    while j < nm {
                        let motive_bvar = usize_to_u32(nf + n_minors + nm - 1 - j + shift);
                        ih = Expr::app(ih, Expr::bvar(motive_bvar));
                        j += 1;
                    }
                }
                // Apply minors.
                {
                    let mut j: usize = 0;
                    while j < n_minors {
                        let minor_bvar_idx = usize_to_u32(nf + n_minors - 1 - j + shift);
                        ih = Expr::app(ih, Expr::bvar(minor_bvar_idx));
                        j += 1;
                    }
                }

                // Apply index arguments for indexed inductives.
                if num_indices > 0 {
                    if let Some(field_ty) = field_types.get(i) {
                        let indices = get_constructor_return_indices(field_ty, num_params);
                        // VERBATIM `for idx_expr in indices`.
                        {
                            let mut _ix = 0usize;
                            while _ix < indices.len() {
                                let remapped = remap_residual_index_bvars(
                                    &indices[_ix], i, np, nf, n_minors, nm, n_pis,
                                );
                                ih = Expr::app(ih, remapped);
                                _ix += 1;
                            }
                        }
                    }
                }

                // Apply the recursive field as major premise.
                let mut major = Expr::bvar(usize_to_u32(nf - 1 - i + shift));
                // VERBATIM `for k in (0..n_pis).rev()` — descending while loop.
                {
                    let mut _k = n_pis;
                    while _k > 0 {
                        _k -= 1;
                        major = Expr::app(major, Expr::bvar(usize_to_u32(_k)));
                    }
                }
                ih = Expr::app(ih, major);

                // Wrap IH in lambda binders for Pi-bound variables (reflexive fields).
                let pi_domains = match field_types.get(i) {
                    Some(ft) => collect_pi_domains(ft),
                    None => Vec::new(),
                };
                // VERBATIM `for (k, (bi, domain)) in pi_domains.iter().enumerate().rev()`.
                {
                    let mut _pd = pi_domains.len();
                    while _pd > 0 {
                        _pd -= 1;
                        let k = _pd;
                        let (bi, domain) = &pi_domains[k];
                        let remapped =
                            remap_residual_index_bvars(domain, i, np, nf, n_minors, nm, k);
                        ih = Expr::lam(*bi, remapped, ih);
                    }
                }

                body = Expr::app(body, ih);
            }
            i += 1;
        }
    }

    // Extract actual domain types from the eliminator type's Pi binders:
    // Π params. Π motive. Π minors. Π rest...
    let dummy_ty = Expr::sort(Level::zero());
    let mut elim_cursor = eliminator_type.clone();
    let mut param_domain_types: Vec<Expr> = Vec::new();
    {
        let mut _p = 0usize;
        while _p < np {
            match &elim_cursor.kind {
                ExprKind::Pi(_, domain, body) => {
                    param_domain_types.push((**domain).clone());
                    elim_cursor = (**body).clone();
                }
                _ => {
                    param_domain_types.push(dummy_ty.clone());
                }
            }
            _p += 1;
        }
    }
    let mut motive_domain_types: Vec<Expr> = Vec::new();
    {
        let mut _m = 0usize;
        while _m < nm {
            match &elim_cursor.kind {
                ExprKind::Pi(_, domain, body) => {
                    motive_domain_types.push((**domain).clone());
                    elim_cursor = (**body).clone();
                }
                _ => {
                    motive_domain_types.push(dummy_ty.clone());
                }
            }
            _m += 1;
        }
    }
    let mut minor_domain_types: Vec<Expr> = Vec::new();
    {
        let mut _mn = 0usize;
        while _mn < n_minors {
            match &elim_cursor.kind {
                ExprKind::Pi(_, domain, body) => {
                    minor_domain_types.push((**domain).clone());
                    elim_cursor = (**body).clone();
                }
                _ => {
                    minor_domain_types.push(dummy_ty.clone());
                }
            }
            _mn += 1;
        }
    }

    // Wrap body in λ params. λ motives. λ minors. λ fields. body
    let mut result = body;

    // Fields (innermost) — lift field types by (nm + n_minors) at depth i.
    let lift_amount = usize_to_u32(nm + n_minors);
    // VERBATIM `for i in (0..nf).rev()` — descending while loop.
    {
        let mut _fi = nf;
        while _fi > 0 {
            _fi -= 1;
            let i = _fi;
            let field_ty = match field_types.get(i) {
                Some(ft) => {
                    if lift_amount > 0 {
                        ft.lift_from(i as u32, lift_amount)
                    } else {
                        ft.clone()
                    }
                }
                None => dummy_ty.clone(),
            };
            result = Expr::lam(bi_default(), field_ty, result);
        }
    }
    // Minors (innermost minor first wrapping outward).
    // VERBATIM `for minor_ty in minor_domain_types.iter().rev()`.
    {
        let mut _mi = minor_domain_types.len();
        while _mi > 0 {
            _mi -= 1;
            result = Expr::lam(bi_default(), minor_domain_types[_mi].clone(), result);
        }
    }
    // Motives.
    {
        let mut _mo = motive_domain_types.len();
        while _mo > 0 {
            _mo -= 1;
            result = Expr::lam(bi_default(), motive_domain_types[_mo].clone(), result);
        }
    }
    // Params (innermost param first wrapping outward).
    {
        let mut _pa = param_domain_types.len();
        while _pa > 0 {
            _pa -= 1;
            result = Expr::lam(bi_default(), param_domain_types[_pa].clone(), result);
        }
    }

    result
}

// ════════════════════════════════════════════════════════════════════════════
// MONO ROOT (#[no_mangle]) — the single closure-free root the emitter picks with
// `--mir-emit-closure build_rec_rhs_root`. It receives the flat, closure-free ctor +
// recursor description, reconstructs the slices, calls build_recursor_rule_rhs, and
// writes the resulting `Expr` (the iota-rule RHS) through the sret pointer.
// ════════════════════════════════════════════════════════════════════════════

pub const IND: u32 = 1; // the inductive head I
pub const PARAM0: u32 = 50; // a parameter/type const for non-recursive fields
pub const RECN: u32 = 200; // the recursor name I.rec
pub const ULEVEL: u32 = 7; // the universe level-param name `u`
pub const MOTIVE_DOM: u32 = 60; // a synthetic motive-domain const in the elim type
pub const MINOR_DOM: u32 = 61; // a synthetic minor-domain const in the elim type
pub const PARAM_DOM: u32 = 62; // a synthetic param-domain const in the elim type

#[repr(C)]
pub struct BuildRhsArgs {
    pub rec_name_raw: u32,
    pub num_params: u32,
    pub num_motives: u32,
    pub num_indices: u32,
    pub num_fields: u32,
    pub num_ctors: u32,
    pub ctor_idx: u32,
    pub recursive_flags_ptr: *const bool,
    pub recursive_flags_len: usize,
    pub field_types_ptr: *const Expr,
    pub field_types_len: usize,
    pub rec_level_params_ptr: *const Name,
    pub rec_level_params_len: usize,
    pub eliminator_type_ptr: *const Expr,
    pub all_types_ptr: *const InductiveType,
    pub all_types_len: usize,
}

#[no_mangle]
pub extern "C" fn build_rec_rhs_root(out: *mut Expr, args: *const BuildRhsArgs) {
    let a: &BuildRhsArgs = unsafe { &*args };
    let recursive_flags: &[bool] =
        unsafe { std::slice::from_raw_parts(a.recursive_flags_ptr, a.recursive_flags_len) };
    let field_types: &[Expr] =
        unsafe { std::slice::from_raw_parts(a.field_types_ptr, a.field_types_len) };
    let rec_level_params: &[Name] =
        unsafe { std::slice::from_raw_parts(a.rec_level_params_ptr, a.rec_level_params_len) };
    let all_types: &[InductiveType] =
        unsafe { std::slice::from_raw_parts(a.all_types_ptr, a.all_types_len) };
    let eliminator_type: &Expr = unsafe { &*a.eliminator_type_ptr };

    let rec_name = Name(a.rec_name_raw);

    let result = build_recursor_rule_rhs(
        &rec_name,
        rec_level_params,
        a.num_params,
        a.num_motives,
        a.num_indices,
        a.num_fields,
        recursive_flags,
        field_types,
        a.num_ctors as usize,
        a.ctor_idx as usize,
        eliminator_type,
        all_types,
    );

    unsafe {
        std::ptr::write(out, result);
    }
}

// ── Caller-side input builders (used by the standalone harness AND mirrored by the
//    native test). NOT part of the emitted root; they may use full Rust. ──

// Build the field type Expr for a given `field_kind`:
//   0 => recursive field : I@{u}
//   2 => indexed recursive field : I@{u} #0
//   3 => reflexive recursive field : Π (_:PARAM0). I@{u}  (one Pi binder → n_pis=1)
//   _ => non-recursive Type field : PARAM0
pub fn build_field_ty(field_kind: u8, rec_level_params: &[Name]) -> Expr {
    match field_kind {
        0 => ind_head(rec_level_params),
        2 => {
            let head = ind_head(rec_level_params);
            Expr::app(head, Expr::bvar(0))
        }
        3 => {
            let head = ind_head(rec_level_params);
            Expr::pi(bi_default(), Expr::const_(Name(PARAM0), Vec::new()), head)
        }
        _ => Expr::const_(Name(PARAM0), Vec::new()),
    }
}

fn ind_head(rec_level_params: &[Name]) -> Expr {
    let mut levels: Vec<Level> = Vec::new();
    {
        let mut i = 0usize;
        while i < rec_level_params.len() {
            levels.push(Level::Param(rec_level_params[i]));
            i += 1;
        }
    }
    Expr::const_(Name(IND), levels)
}

// The modeled single-inductive mutual block (just I with its ctors — content beyond
// `.len()==1` is unused on the single-inductive JIT path).
pub fn build_all_types() -> Vec<InductiveType> {
    vec![InductiveType {
        name: Name(IND),
        constructors: vec![Ctor {
            name: Name(RECN),
            type_: Expr::const_(Name(IND), Vec::new()),
        }],
    }]
}

pub fn build_level_params() -> Vec<Name> {
    vec![Name(ULEVEL)]
}

// Build a synthetic eliminator type Π param.. Π motive.. Π minor.. Sort0, with distinct
// domain consts so the domain-extraction reads real (non-dummy) types.
pub fn build_eliminator_type(np: usize, nm: usize, n_minors: usize) -> Expr {
    let mut ty = Expr::sort(Level::zero());
    // minors (innermost)
    {
        let mut i = 0usize;
        while i < n_minors {
            ty = Expr::pi(bi_default(), Expr::const_(Name(MINOR_DOM), Vec::new()), ty);
            i += 1;
        }
    }
    {
        let mut i = 0usize;
        while i < nm {
            ty = Expr::pi(bi_default(), Expr::const_(Name(MOTIVE_DOM), Vec::new()), ty);
            i += 1;
        }
    }
    {
        let mut i = 0usize;
        while i < np {
            ty = Expr::pi(bi_default(), Expr::const_(Name(PARAM_DOM), Vec::new()), ty);
            i += 1;
        }
    }
    ty
}

// ════════════════════════════════════════════════════════════════════════════
// Standalone re-emit validate harness — exercise the iota-RHS builder across
// nullary / direct-recursive / binary-node / indexed / reflexive ctor shapes,
// all routed through build_rec_rhs_root, and self-check the resulting meta word.
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

fn assemble(
    field_kinds: &[u8],
) -> (Vec<Name>, Vec<Expr>, Vec<InductiveType>) {
    let rec_level_params = build_level_params();
    let field_types: Vec<Expr> = field_kinds
        .iter()
        .map(|&k| build_field_ty(k, &rec_level_params))
        .collect();
    let all_types = build_all_types();
    (rec_level_params, field_types, all_types)
}

fn native_rhs(
    field_kinds: &[u8],
    recursive_flags: &[bool],
    num_params: u32,
    num_motives: u32,
    num_indices: u32,
    ctor_idx: u32,
    num_ctors: u32,
) -> Expr {
    let (rec_level_params, field_types, all_types) = assemble(field_kinds);
    let nf = field_types.len() as u32;
    let elim = build_eliminator_type(num_params as usize, num_motives as usize, num_ctors as usize);
    build_recursor_rule_rhs(
        &Name(RECN),
        &rec_level_params,
        num_params,
        num_motives,
        num_indices,
        nf,
        recursive_flags,
        &field_types,
        num_ctors as usize,
        ctor_idx as usize,
        &elim,
        &all_types,
    )
}

fn root_to_expr(
    field_kinds: &[u8],
    recursive_flags: &[bool],
    num_params: u32,
    num_motives: u32,
    num_indices: u32,
    ctor_idx: u32,
    num_ctors: u32,
) -> Expr {
    let (rec_level_params, field_types, all_types) = assemble(field_kinds);
    let nf = field_types.len() as u32;
    let elim = build_eliminator_type(num_params as usize, num_motives as usize, num_ctors as usize);
    let args = BuildRhsArgs {
        rec_name_raw: RECN,
        num_params,
        num_motives,
        num_indices,
        num_fields: nf,
        num_ctors,
        ctor_idx,
        recursive_flags_ptr: recursive_flags.as_ptr(),
        recursive_flags_len: recursive_flags.len(),
        field_types_ptr: field_types.as_ptr(),
        field_types_len: field_types.len(),
        rec_level_params_ptr: rec_level_params.as_ptr(),
        rec_level_params_len: rec_level_params.len(),
        eliminator_type_ptr: &elim as *const Expr,
        all_types_ptr: all_types.as_ptr(),
        all_types_len: all_types.len(),
    };
    let mut slot = std::mem::MaybeUninit::<Expr>::uninit();
    unsafe {
        build_rec_rhs_root(slot.as_mut_ptr(), &args as *const BuildRhsArgs);
        slot.assume_init()
    }
}

fn main() {
    // (field_kinds, recursive_flags, num_params, num_motives, num_indices, ctor_idx, num_ctors, label)
    let cases: Vec<(Vec<u8>, Vec<bool>, u32, u32, u32, u32, u32, &str)> = vec![
        (vec![], vec![], 0, 1, 0, 0, 1, "nullary ctor (Nat.zero): λ.. minor_0"),
        (vec![0], vec![true], 0, 1, 0, 1, 2, "Nat.succ: minor_1 field IH(rec .. field)"),
        (vec![1, 0], vec![false, true], 1, 1, 0, 1, 2, "List.cons: head + recursive tail IH"),
        (vec![0, 0], vec![true, true], 0, 1, 0, 0, 1, "binary node: two fields two IHs"),
        (vec![1, 1], vec![false, false], 0, 1, 0, 0, 1, "And.intro: two non-rec fields, no IH"),
        (vec![2], vec![true], 1, 1, 1, 0, 1, "indexed recursive field + return index in IH"),
        (vec![3], vec![true], 0, 1, 0, 0, 1, "reflexive field (Π-wrapped IH, n_pis=1)"),
        (vec![1, 0, 0], vec![false, true, true], 1, 1, 0, 2, 3, "param head + two recursive fields"),
    ];

    let mut ok = true;
    for (fk, rf, np, nm, ni, ci, nc, label) in &cases {
        let native = native_rhs(fk, rf, *np, *nm, *ni, *ci, *nc);
        let viaroot = root_to_expr(fk, rf, *np, *nm, *ni, *ci, *nc);
        let eq = deep_eq(&native, &viaroot);
        println!("{label}: meta={:#018x} eq={eq}", native.meta.raw());
        if !eq {
            ok = false;
        }
    }
    std::process::exit((!ok) as i32);
}
