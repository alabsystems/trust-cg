// SELF-CONTAINED clean-kernel STRICT-POSITIVITY slice — the soundness-critical
// gate that decides whether an inductive declaration may be added (a bug here =
// an unsound inductive type, e.g. the `Bad : (Bad -> Bad) -> Bad` paradox).
//
// Transcribed VERBATIM from $HOME/clean/crates/clean-kernel/src/inductive/mod.rs:
//   * check_positivity                       (mod.rs:307)  — public entry
//   * check_positivity_in_ctor_type_impl     (mod.rs:349)  — walk the ctor Pi telescope
//   * check_strictly_positive_impl           (mod.rs:388)  — the core: I may appear,
//                                                            but NEVER left of an arrow
//   * check_no_negative_occurrence           (mod.rs:559)  — Err if name occurs at all
//   * mentions_name                          (mod.rs:596)  — structural Const-occurrence scan
//
// These compose the same Expr/ExprKind/Level/ExprMeta machinery as the prior
// VERIFIED real-Expr slices (clean_expr_{infer,whnf,infer_ext}_slice.rs): the
// Arc<Expr> heap graph, the real bit-packed ExprMeta (real compute_meta MurmurHash),
// the App-spine walks get_app_fn / get_app_args (a VERIFIED pillar, reused here),
// and Name equality. Strict positivity does NOT need whnf/def_eq/infer — it is a
// pure SYNTACTIC analysis over the constructor type expression — so the only
// "pillar" it composes is the App-spine decomposition (get_app_fn/get_app_args)
// plus the structural Const-occurrence scan (mentions_name).
//
// FAITHFULNESS / control flow is VERBATIM the real arms:
//   - check_positivity_in_ctor_type_impl: Pi -> {check domain strictly positive;
//     recurse on codomain}; otherwise (the return type) Ok.
//   - check_strictly_positive_impl: leaf/Const/Sort/Lit/BVar/FVar -> Ok; App ->
//     if head is the inductive, every arg must contain NO mutual inductive (the
//     is_valid_ind_app / has_ind_occ rule, #2145), else recurse on f and a;
//     Pi (an ARROW inside a ctor arg) -> the CRITICAL case: neither `inductive_name`
//     NOR any sibling mutual inductive may occur in the domain (#107 / Wave 107),
//     and the codomain is still positive; Lam/Let/Proj/MData -> structural recurse.
//   - check_no_negative_occurrence: Err(NonPositive) iff mentions_name(expr, name).
//   - mentions_name: true iff a Const(name,..) occurs ANYWHERE (the ExprVisitor
//     `visit_const` override; transcribed as direct structural recursion — identical
//     semantics: combine = OR over all sub-expressions, only Const matches).
//
// MODELING boundary: NONE for the env (this check takes no Environment — it is a
// pure function of (inductive_name, expr, param_count, all_ind_names)). The only
// modeling is the EXOTIC ExprKind arms (Cubical*/ZFC*/SProp/Squash): they are NOT
// constructed by the positivity test cases (the kernel's ordinary inductives use
// only BVar/Const/App/Pi/Lam/Let/Proj/MData), so they recurse conservatively
// exactly as the real arms do. The `stack_safe` wrapper in the real code is a
// stacker::maybe_grow pass-through; inlined to a direct call here.

#![allow(dead_code)]
#![allow(clippy::all)]
#![allow(unused_variables)]

use std::sync::Arc;

// ───────────────────────── Name / FVarId / Level ─────────────────────────

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
    pub fn has_params(&self) -> bool {
        match self {
            Level::Zero => false,
            Level::Succ(l) => l.has_params(),
            Level::Param(_) => true,
        }
    }
}

pub type LevelVec = Vec<Level>;
pub type NameVec = Vec<Name>;

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

// ───────────────────────── KaniHasher (clean's own) ─────────────────────────

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

pub struct KaniHasher {
    state: u64,
}
impl KaniHasher {
    fn new() -> Self {
        KaniHasher { state: 0 }
    }
}
impl std::hash::Hasher for KaniHasher {
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
fn hash_name(value: &Name) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}
#[inline]
fn hash_level(value: &Level) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}
#[inline]
fn hash_lit(value: &Literal) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[inline]
fn level_has_mvar(_l: &Level) -> bool {
    false
}

// ───────────────────────── ExprMeta (real bit-pack) ─────────────────────────

#[derive(Clone, Copy, Debug)]
pub struct ExprMeta(u64);

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
    fn mk_wrapper_meta(inner: ExprMeta, extra_hash: u64) -> ExprMeta {
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

// ───────────────────────── Expr / ExprKind ─────────────────────────

#[derive(Clone, Debug)]
pub enum ZFCSetExpr {
    Empty,
    Separation { set: Arc<Expr>, pred: Arc<Expr> },
    Replacement { set: Arc<Expr>, func: Arc<Expr> },
}

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
    MData(u32, Arc<Expr>),
    CubicalInterval,
    CubicalI0,
    CubicalI1,
    CubicalPath {
        ty: Arc<Expr>,
        left: Arc<Expr>,
        right: Arc<Expr>,
    },
    CubicalPathLam {
        body: Arc<Expr>,
    },
    CubicalPathApp {
        path: Arc<Expr>,
        arg: Arc<Expr>,
    },
    ZFCSet(ZFCSetExpr),
    ZFCMem {
        element: Arc<Expr>,
        set: Arc<Expr>,
    },
    ZFCComprehension {
        domain: Arc<Expr>,
        pred: Arc<Expr>,
    },
    SProp,
    Squash(Arc<Expr>),
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
            ExprKind::FVar(id) => ExprMeta::pack(
                mix_hash(13, id.0) as u32,
                0,
                0,
                true,
                false,
                false,
                false,
            ),
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
            ExprKind::MData(_, expr) => ExprMeta::mk_wrapper_meta(expr.meta(), 0),
            ExprKind::CubicalInterval => {
                ExprMeta::pack(mix_hash(17, 0) as u32, 0, 0, false, false, false, false)
            }
            ExprKind::CubicalI0 => {
                ExprMeta::pack(mix_hash(17, 1) as u32, 0, 0, false, false, false, false)
            }
            ExprKind::CubicalI1 => {
                ExprMeta::pack(mix_hash(17, 2) as u32, 0, 0, false, false, false, false)
            }
            ExprKind::SProp => {
                ExprMeta::pack(mix_hash(19, 0) as u32, 0, 0, false, false, false, false)
            }
            ExprKind::Squash(inner) => ExprMeta::mk_wrapper_meta(inner.meta(), 23),
            ExprKind::CubicalPath { ty, left, right } => {
                let m = ExprMeta::mk_app_meta(ty.meta(), left.meta());
                ExprMeta::mk_app_meta(m, right.meta())
            }
            ExprKind::CubicalPathLam { body } => ExprMeta::mk_wrapper_meta(body.meta(), 29),
            ExprKind::CubicalPathApp { path, arg } => ExprMeta::mk_app_meta(path.meta(), arg.meta()),
            ExprKind::ZFCSet(_) => {
                ExprMeta::pack(mix_hash(31, 0) as u32, 0, 0, false, false, false, false)
            }
            ExprKind::ZFCMem { element, set } => ExprMeta::mk_app_meta(element.meta(), set.meta()),
            ExprKind::ZFCComprehension { domain, pred } => {
                ExprMeta::mk_app_meta(domain.meta(), pred.meta())
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct Expr {
    kind: ExprKind,
    meta: ExprMeta,
}

impl Expr {
    pub fn from_kind(kind: ExprKind) -> Self {
        let meta = kind.compute_meta();
        Expr { kind, meta }
    }
    pub fn meta(&self) -> ExprMeta {
        self.meta
    }
    pub fn kind(&self) -> &ExprKind {
        &self.kind
    }
    pub fn loose_bvar_range(&self) -> u32 {
        self.meta.loose_bvar_range()
    }
    pub fn bvar(idx: u32) -> Self {
        Expr::from_kind(ExprKind::BVar(idx))
    }
    pub fn fvar(id: FVarId) -> Self {
        Expr::from_kind(ExprKind::FVar(id))
    }
    pub fn const_(name: Name, levels: LevelVec) -> Self {
        Expr::from_kind(ExprKind::Const(name, levels))
    }
    pub fn sort(l: Level) -> Self {
        Expr::from_kind(ExprKind::Sort(l))
    }
    pub fn sort0() -> Self {
        Expr::from_kind(ExprKind::Sort(Level::Zero))
    }
    pub fn nat(n: u64) -> Self {
        Expr::from_kind(ExprKind::Lit(Literal::Nat(n)))
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
    pub fn lett(name: Name, ty: Expr, val: Expr, body: Expr, nondep: bool) -> Self {
        Expr::from_kind(ExprKind::Let(
            name,
            Arc::new(ty),
            Arc::new(val),
            Arc::new(body),
            nondep,
        ))
    }
    pub fn proj(name: Name, idx: u32, e: Expr) -> Self {
        Expr::from_kind(ExprKind::Proj(name, idx, Arc::new(e)))
    }
    pub fn mdata(tag: u32, e: Expr) -> Self {
        Expr::from_kind(ExprKind::MData(tag, Arc::new(e)))
    }

    // VERBATIM get_app_fn / get_app_args (the VERIFIED App-spine pillar, reused).
    fn get_app_fn(&self) -> Expr {
        let mut current = self.clone();
        loop {
            let next = match &current.kind {
                ExprKind::App(f, _) => f.as_ref().clone(),
                _ => return current,
            };
            current = next;
        }
    }
    fn get_app_args(&self) -> Vec<Expr> {
        let mut args: Vec<Expr> = Vec::new();
        let mut current = self.clone();
        while let ExprKind::App(f, a) = &current.kind {
            args.push(a.as_ref().clone());
            let next = f.as_ref().clone();
            current = next;
        }
        args.reverse();
        args
    }
}

// ───────────────────────── InductiveError ─────────────────────────
// The real InductiveError has many variants; the positivity path produces ONLY
// NonPositive(Name, Name). Modeled as a single-variant enum (the relevant one),
// so Result<(), InductiveError> lowers exactly (an enum payload + a unit Ok).

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InductiveError {
    NonPositive(Name, Name),
}

// ═══════════════════════ STRICT POSITIVITY (the GATE) ═══════════════════════
// VERBATIM $HOME/clean/crates/clean-kernel/src/inductive/mod.rs. The real code wraps
// each fn in `stack_safe(|| ...)` (stacker::maybe_grow); that is a transparent
// pass-through and is inlined to a direct call here.

/// Public entry — check positivity in a constructor type.
/// VERBATIM mod.rs:307 check_positivity -> check_positivity_in_ctor_type.
pub fn check_positivity(
    inductive_name: &Name,
    expr: &Expr,
    param_count: u32,
    all_ind_names: &[&Name],
) -> Result<(), InductiveError> {
    check_positivity_in_ctor_type_impl(inductive_name, expr, param_count, all_ind_names)
}

/// Walk a constructor type's Pi telescope: each domain must be strictly positive,
/// then recurse on the codomain; the final (non-Pi) return type is unrestricted.
/// VERBATIM mod.rs:349 check_positivity_in_ctor_type_impl.
fn check_positivity_in_ctor_type_impl(
    inductive_name: &Name,
    expr: &Expr,
    param_count: u32,
    all_ind_names: &[&Name],
) -> Result<(), InductiveError> {
    match &expr.kind {
        ExprKind::Pi(_, domain, codomain) => {
            check_strictly_positive_impl(inductive_name, domain, param_count, all_ind_names)?;
            check_positivity_in_ctor_type_impl(
                inductive_name,
                codomain,
                param_count,
                all_ind_names,
            )?;
            Ok(())
        }
        _ => Ok(()),
    }
}

/// The CORE rule: the inductive may appear, but NEVER to the left of an arrow.
/// VERBATIM mod.rs:388 check_strictly_positive_impl.
fn check_strictly_positive_impl(
    inductive_name: &Name,
    expr: &Expr,
    _param_count: u32,
    all_ind_names: &[&Name],
) -> Result<(), InductiveError> {
    match &expr.kind {
        ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => Ok(()),

        ExprKind::Const(_name, _) => Ok(()),

        ExprKind::App(f, a) => {
            // Check if head is the inductive type.
            let head = expr.get_app_fn();
            if let ExprKind::Const(name, _) = &head.kind {
                if name == inductive_name {
                    // I applied to args — args must not mention ANY mutual
                    // inductive negatively (#2145, is_valid_ind_app/has_ind_occ).
                    let args = expr.get_app_args();
                    for arg in &args {
                        for ind_name in all_ind_names {
                            check_no_negative_occurrence(ind_name, arg)?;
                        }
                    }
                    return Ok(());
                }
            }
            // General application: check both parts for strict positivity.
            check_strictly_positive_impl(inductive_name, f, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, a, _param_count, all_ind_names)?;
            Ok(())
        }

        ExprKind::Pi(_, domain, codomain) => {
            // The CRITICAL case: (A -> B) in a constructor argument. The inductive
            // CANNOT appear in A (negative); neither can any sibling mutual
            // inductive (Wave 107). But it CAN appear in B (still positive).
            check_no_negative_occurrence(inductive_name, domain)?;
            for sibling in all_ind_names {
                if *sibling != inductive_name {
                    check_no_negative_occurrence(sibling, domain)?;
                }
            }
            check_strictly_positive_impl(inductive_name, codomain, _param_count, all_ind_names)?;
            Ok(())
        }

        ExprKind::Lam(_, ty, body) => {
            check_strictly_positive_impl(inductive_name, ty, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, body, _param_count, all_ind_names)?;
            Ok(())
        }

        ExprKind::Let(_, ty, val, body, _) => {
            check_strictly_positive_impl(inductive_name, ty, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, val, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, body, _param_count, all_ind_names)?;
            Ok(())
        }

        ExprKind::Proj(_, _, e) => {
            check_strictly_positive_impl(inductive_name, e, _param_count, all_ind_names)?;
            Ok(())
        }

        ExprKind::MData(_, inner) => {
            check_strictly_positive_impl(inductive_name, inner, _param_count, all_ind_names)
        }

        // Mode-specific extensions — conservative: check all subexpressions
        // (VERBATIM the real arms; not constructed by ordinary inductives).
        ExprKind::CubicalInterval | ExprKind::CubicalI0 | ExprKind::CubicalI1 => Ok(()),
        ExprKind::CubicalPath { ty, left, right } => {
            check_strictly_positive_impl(inductive_name, ty, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, left, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, right, _param_count, all_ind_names)
        }
        ExprKind::CubicalPathLam { body } => {
            check_strictly_positive_impl(inductive_name, body, _param_count, all_ind_names)
        }
        ExprKind::CubicalPathApp { path, arg } => {
            check_strictly_positive_impl(inductive_name, path, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, arg, _param_count, all_ind_names)
        }
        ExprKind::ZFCSet(set_expr) => {
            check_strictly_positive_zfc_set(inductive_name, set_expr, _param_count, all_ind_names)
        }
        ExprKind::ZFCMem { element, set } => {
            check_strictly_positive_impl(inductive_name, element, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, set, _param_count, all_ind_names)
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            check_strictly_positive_impl(inductive_name, domain, _param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, pred, _param_count, all_ind_names)
        }
        ExprKind::SProp => Ok(()),
        ExprKind::Squash(inner) => {
            check_strictly_positive_impl(inductive_name, inner, _param_count, all_ind_names)
        }
    }
}

/// VERBATIM mod.rs:524 check_strictly_positive_zfc_set.
fn check_strictly_positive_zfc_set(
    inductive_name: &Name,
    set_expr: &ZFCSetExpr,
    param_count: u32,
    all_ind_names: &[&Name],
) -> Result<(), InductiveError> {
    match set_expr {
        ZFCSetExpr::Empty => Ok(()),
        ZFCSetExpr::Separation { set, pred } | ZFCSetExpr::Replacement { set, func: pred } => {
            check_strictly_positive_impl(inductive_name, set, param_count, all_ind_names)?;
            check_strictly_positive_impl(inductive_name, pred, param_count, all_ind_names)
        }
    }
}

/// Err(NonPositive) iff `expr` mentions `inductive_name` at all.
/// VERBATIM mod.rs:559 check_no_negative_occurrence.
fn check_no_negative_occurrence(inductive_name: &Name, expr: &Expr) -> Result<(), InductiveError> {
    if mentions_name(expr, inductive_name) {
        Err(InductiveError::NonPositive(*inductive_name, *inductive_name))
    } else {
        Ok(())
    }
}

/// Returns true iff `expr` contains `Const(name, ..)` anywhere.
/// VERBATIM the ExprVisitor `visit_const` override (mod.rs:570-598): the trait's
/// structural recursion with combine = OR; only Const matches. Transcribed as
/// direct structural recursion (identical semantics).
pub fn mentions_name(expr: &Expr, name: &Name) -> bool {
    match &expr.kind {
        ExprKind::Const(n, _) => n == name,
        ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => false,
        ExprKind::App(f, a) => mentions_name(f, name) || mentions_name(a, name),
        ExprKind::Lam(_, ty, body) => mentions_name(ty, name) || mentions_name(body, name),
        ExprKind::Pi(_, ty, body) => mentions_name(ty, name) || mentions_name(body, name),
        ExprKind::Let(_, ty, val, body, _) => {
            mentions_name(ty, name) || mentions_name(val, name) || mentions_name(body, name)
        }
        ExprKind::Proj(_, _, e) => mentions_name(e, name),
        ExprKind::MData(_, inner) => mentions_name(inner, name),
        ExprKind::CubicalInterval | ExprKind::CubicalI0 | ExprKind::CubicalI1 => false,
        ExprKind::CubicalPath { ty, left, right } => {
            mentions_name(ty, name) || mentions_name(left, name) || mentions_name(right, name)
        }
        ExprKind::CubicalPathLam { body } => mentions_name(body, name),
        ExprKind::CubicalPathApp { path, arg } => {
            mentions_name(path, name) || mentions_name(arg, name)
        }
        ExprKind::ZFCSet(set_expr) => mentions_name_zfc(set_expr, name),
        ExprKind::ZFCMem { element, set } => {
            mentions_name(element, name) || mentions_name(set, name)
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            mentions_name(domain, name) || mentions_name(pred, name)
        }
        ExprKind::SProp => false,
        ExprKind::Squash(inner) => mentions_name(inner, name),
    }
}

fn mentions_name_zfc(set_expr: &ZFCSetExpr, name: &Name) -> bool {
    match set_expr {
        ZFCSetExpr::Empty => false,
        ZFCSetExpr::Separation { set, pred } | ZFCSetExpr::Replacement { set, func: pred } => {
            mentions_name(set, name) || mentions_name(pred, name)
        }
    }
}

// ───────────────────────── MONO ROOT (#[no_mangle]) ─────────────────────────
// A single monomorphic, closure-free root the emitter can pick with
// `--mir-emit-closure check_positivity_root`. It forwards to check_positivity over
// concrete arguments (the inductive name, the ctor type, param_count, and the
// mutual-name slice), returning the discriminant of the Result (0 = Ok/accept,
// 1 = Err/reject) so the boundary is a plain i32.
#[no_mangle]
pub extern "C" fn check_positivity_root(
    ind_name_raw: u32,
    expr: &Expr,
    param_count: u32,
    sibling_raw: u32,
    sibling_count: u32,
) -> i32 {
    let ind = Name(ind_name_raw);
    let sib = Name(sibling_raw);
    // 0, 1, or 2 mutual names: just `ind`, or `ind` + one sibling.
    let names_one = [&ind];
    let names_two = [&ind, &sib];
    let all: &[&Name] = if sibling_count >= 2 {
        &names_two
    } else {
        &names_one
    };
    match check_positivity(&ind, expr, param_count, all) {
        Ok(()) => 0,
        Err(_) => 1,
    }
}

fn main() {
    // Standalone re-emit validate harness: build a couple of ctor types and run.
    let bd = BinderData { info: 0, mult: 0 };
    let tree = Name(1);
    // GOOD: (Tree -> Tree) ... wait, that's negative. Use a positive one:
    //   mk : Tree -> Tree   (Tree strictly positive — direct recursive arg)
    let good = Expr::pi(bd, Expr::const_(tree, vec![]), Expr::const_(tree, vec![]));
    // BAD: (Tree -> Bool) -> Tree   (Tree NEGATIVE: left of an inner arrow)
    let bad = Expr::pi(
        bd,
        Expr::pi(bd, Expr::const_(tree, vec![]), Expr::const_(Name(2), vec![])),
        Expr::const_(tree, vec![]),
    );
    let g = check_positivity_root(1, &good, 0, 0, 1);
    let b = check_positivity_root(1, &bad, 0, 0, 1);
    println!("good={g} bad={b}");
    std::process::exit((g != 0 || b != 1) as i32);
}
