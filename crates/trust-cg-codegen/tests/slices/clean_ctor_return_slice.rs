// SELF-CONTAINED clean-kernel CONSTRUCTOR-RETURN-TYPE WELL-FORMEDNESS slice — the
// soundness-critical admit-time gate that decides, for every constructor of an
// inductive being added, that the constructor's RETURN TYPE is a valid application
// of the inductive being defined: (1) the head IS the inductive `Const`; (2) the
// parameter arguments are exactly the declared params (as BVar de-Bruijn refs);
// (3) the index arguments do NOT mention any inductive in the mutual block.
//
// WHY a bug here = UNSOUNDNESS. This is the kernel's `is_valid_ind_app`
// (Lean 4 kernel/inductive.cpp). It runs in `validate_inductive` ALONGSIDE
// strict-positivity (the already-verified sibling gate). A bug in ANY of the three
// checks admits an inductive whose constructor lies about what it builds, which is
// directly exploitable:
//   * Head check (1): if a constructor of `I` were allowed to return some OTHER
//     type `J` (or a non-`Const` head), the generated recursor's minor premises and
//     the constructor's stored "inductive_name" diverge — `J.rec` would accept an
//     `I`-built term as a `J`, collapsing the two inductives' eliminators and
//     letting a proof of one stand in for the other (a route to `False`).
//   * Param check (2): the recursor is generated assuming each constructor returns
//     `I p0 .. p(k-1) idx..` with the params bound to the SHARED parameter
//     telescope. If a constructor instead returned `I t0 ..` for some non-parameter
//     `t0`, the motive `C : .. -> I p.. -> Sort` and the minor premise would be
//     instantiated at inconsistent parameters — the recursor's computation rule
//     (iota) would fire on a major premise whose actual params differ from the ones
//     the minor premise was typed against, yielding an ill-typed reduct accepted as
//     well-typed (unsound iota).
//   * Index check (3): an index argument that mentions the inductive being defined
//     is the lean4#2125 unsoundness — it lets the inductive's OWN index depend on a
//     value of the inductive, defeating the strict-positivity/termination argument
//     for the eliminator (the indices must be "small" data independent of `I`).
//     Admitting it = a non-well-founded inductive family = `False`.
//
// Transcribed VERBATIM from $HOME/clean/crates/clean-kernel/src/inductive/mod.rs:
//   * validate_ctor_return_type             (mod.rs:752)  — the gate (the 3 checks)
//   * get_return_type                       (mod.rs:650)  — strip the Pi telescope
//   * count_pi_args                         (mod.rs:608)  — count leading Pis
//   * mentions_name                         (mod.rs:596)  — structural Const scan
//   * Expr::get_app_fn / get_app_args       (App-spine pillar, VERIFIED, reused)
//   * validate_path_ctor_return_type        (mod.rs:1090) — cubical HIT branch,
//                                              modeled conservatively (see below)
//
// PILLARS composed (all PURE, SYNTACTIC — no whnf/def_eq/infer needed): the App-spine
// decomposition get_app_fn/get_app_args (a VERIFIED pillar, reused from the prior
// real-Expr slices), the Pi-telescope walks get_return_type/count_pi_args, the
// structural Const-occurrence scan mentions_name, Name equality, and BVar-index
// equality. Like strict positivity, this gate is a pure function of the inductive
// declaration's expression shape — it threads NO Environment and NO cache, so there
// is no env/cache modeling boundary.
//
// MODELING boundary: the real `validate_ctor_return_type` takes `&Constructor`,
// `&InductiveType`, `&InductiveDecl`, `&[&Name]`; those structs are kept FAITHFUL
// here (Constructor{name,type_}, InductiveType{name,type_,constructors},
// InductiveDecl{num_params,types}). The `#[no_mangle]` root builds them from
// primitives. The CUBICAL HIT branch (validate_path_ctor_return_type, reached only
// when the return type is a `CubicalPath` — never for an ordinary inductive) is
// transcribed as a conservative reject: ordinary inductives' return types are
// `Const`/`App` heads (BVar/Const/App/Pi only), so the path branch is NEVER taken by
// the test cases, exactly as the positivity slice's Cubical*/ZFC*/SProp arms are
// never constructed by ordinary inductives. The exotic ExprKind arms in mentions_name
// recurse conservatively VERBATIM the real arms.

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

// ───────────────────────── Pi-telescope helpers ─────────────────────────
// VERBATIM inductive/mod.rs:608 count_pi_args and mod.rs:650 get_return_type.

/// Count the number of leading Pi binders. VERBATIM mod.rs:608.
pub fn count_pi_args(expr: &Expr) -> u32 {
    let mut count = 0u32;
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = &current.kind {
        count = count.saturating_add(1);
        current = body;
    }
    count
}

/// Get the return type of a Pi-telescope (strip ALL Pis). VERBATIM mod.rs:650.
fn get_return_type(expr: &Expr) -> &Expr {
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = &current.kind {
        current = body;
    }
    current
}

/// Returns true iff `expr` contains `Const(name, ..)` anywhere.
/// VERBATIM the ExprVisitor `visit_const` override (mod.rs:596): structural
/// recursion with combine = OR; only Const matches. (Identical to the positivity
/// slice's mentions_name — the SAME kernel function, reused by this gate's index
/// check.)
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

// ───────────────────────── Inductive decl structs (FAITHFUL) ─────────────────────────
// FAITHFUL mirrors of inductive/mod.rs Constructor (l.33), InductiveType (l.42),
// InductiveDecl (l.53). Only the fields the gate reads are kept.

#[derive(Clone, Debug)]
pub struct Constructor {
    pub name: Name,
    pub type_: Expr,
}

#[derive(Clone, Debug)]
pub struct InductiveType {
    pub name: Name,
    pub type_: Expr,
    pub constructors: Vec<Constructor>,
}

#[derive(Clone, Debug)]
pub struct InductiveDecl {
    pub num_params: u32,
    pub types: Vec<InductiveType>,
}

// ───────────────────────── InductiveError (the rejection reasons) ─────────────────────────
// FAITHFUL to the three rejection variants this gate produces (mod.rs InductiveError):
// ConstructorReturnType, ConstructorParamMismatch, IndexArgMentionsInductive. The
// real enum has more variants but THIS gate only ever yields these three.

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InductiveError {
    ConstructorReturnType(Name, Name),
    ConstructorParamMismatch {
        ctor_name: Name,
        ind_name: Name,
        param_idx: u32,
    },
    IndexArgMentionsInductive {
        ctor_name: Name,
        ind_name: Name,
        index_pos: u32,
    },
}

// ═══════════════════ CONSTRUCTOR RETURN-TYPE GATE (the GATE) ═══════════════════
// VERBATIM $HOME/clean/crates/clean-kernel/src/inductive/mod.rs:752.

/// Validate a constructor's return type application (head, params, and indices).
/// Lean 4 reference: kernel/inductive.cpp `is_valid_ind_app`.
/// VERBATIM mod.rs:752 validate_ctor_return_type.
fn validate_ctor_return_type(
    ctor: &Constructor,
    ind_type: &InductiveType,
    decl: &InductiveDecl,
    all_names: &[&Name],
) -> Result<(), InductiveError> {
    let return_type = get_return_type(&ctor.type_);

    // Cubical HIT path constructor: the return type is a `CubicalPath`. Reached
    // ONLY in cubical mode; an ordinary inductive's return type is `Const`/`App`.
    // Transcribed dispatch VERBATIM; the path validator is modeled conservatively.
    if let ExprKind::CubicalPath { ty, left, right } = &return_type.kind {
        return validate_path_ctor_return_type(ctor, ind_type, decl, ty, left, right);
    }

    let head = return_type.get_app_fn();

    // Check 1: constructor returns the correct inductive type.
    match &head.kind {
        ExprKind::Const(name, _) if name == &ind_type.name => {}
        _ => {
            return Err(InductiveError::ConstructorReturnType(
                ctor.name.clone(),
                ind_type.name.clone(),
            ));
        }
    }

    let args = return_type.get_app_args();
    let args_len = args.len();

    // Check 2: parameter arguments match declared params as BVars.
    // Each a_i (for i < num_params) must be BVar(total_binders - 1 - i).
    // TRANSCRIPTION NOTE: the kernel writes this as
    //   `for i in 0..num_params { let ok = if total_binders>i { args.get(i)
    //    .is_some_and(|a| matches!(a.kind, BVar(idx) if idx==expected)) } else {false}; .. }`.
    // Transcribed here as an index `while`-loop over `args` (the de-Bruijn dual of the
    // `Range`+`get`+`is_some_and`-closure form) — SEMANTICALLY IDENTICAL (same bound,
    // same per-param BVar-index test, same first-failure rejection), avoiding the
    // Range/Option-closure iterator adapters in the lowering. `param_ok` is computed
    // exactly as the kernel: it is false when `total_binders <= i` OR when `args[i]` is
    // absent OR is not the expected `BVar(expected_bvar)`.
    if decl.num_params > 0 {
        let total_binders = count_pi_args(&ctor.type_);
        let mut i: u32 = 0;
        while i < decl.num_params {
            let mut param_ok = false;
            if total_binders > i {
                let expected_bvar = total_binders - 1 - i;
                let idx = i as usize;
                if idx < args_len {
                    if let ExprKind::BVar(b) = &args[idx].kind {
                        if *b == expected_bvar {
                            param_ok = true;
                        }
                    }
                }
            }
            if !param_ok {
                return Err(InductiveError::ConstructorParamMismatch {
                    ctor_name: ctor.name.clone(),
                    ind_name: ind_type.name.clone(),
                    param_idx: i,
                });
            }
            i += 1;
        }
    }

    // Check 3: index arguments must not mention any inductive in the mutual block.
    // Lean 4 reference: kernel/inductive.cpp lines 351-356 (lean4#2125).
    // TRANSCRIPTION NOTE: the kernel writes this as
    //   `for (idx_pos, idx_arg) in args.iter().skip(num_params).enumerate() { for
    //    ind_name in all_names { if mentions_name(idx_arg, ind_name) { reject } } }`.
    // Transcribed as an index `while`-loop over `args[num_params..]` with `idx_pos =
    // i - num_params` (the de-Bruijn dual of the `skip().enumerate()` form) —
    // SEMANTICALLY IDENTICAL (same index set, same `idx_pos`, same per-name
    // mentions_name reject, same first-failure order). The inner `for ind_name in
    // all_names` is preserved VERBATIM (slice into_iter, a shimmed pillar).
    let num_params = decl.num_params as usize;
    let mut j = num_params;
    while j < args_len {
        let idx_pos = (j - num_params) as u32;
        let idx_arg = &args[j];
        for ind_name in all_names {
            if mentions_name(idx_arg, ind_name) {
                return Err(InductiveError::IndexArgMentionsInductive {
                    ctor_name: ctor.name.clone(),
                    ind_name: (*ind_name).clone(),
                    index_pos: idx_pos,
                });
            }
        }
        j += 1;
    }

    Ok(())
}

/// Cubical HIT path-constructor validation. MODELED conservatively: the real
/// mod.rs:1090 dispatches on HIT-shape recognizers (is_suspension_shape /
/// is_prop_truncation_shape) and a `λ(_:I).body` line whose head targets the
/// inductive. NONE of this is reachable for an ordinary inductive (whose return
/// type is `Const`/`App`, never `CubicalPath`); the conservative reject here is
/// never exercised by the ordinary-inductive test cases — the SAME treatment the
/// positivity slice gives its Cubical*/ZFC* arms. Documented modeling boundary.
fn validate_path_ctor_return_type(
    ctor: &Constructor,
    ind_type: &InductiveType,
    _decl: &InductiveDecl,
    _line: &Expr,
    _left: &Expr,
    _right: &Expr,
) -> Result<(), InductiveError> {
    Err(InductiveError::ConstructorReturnType(
        ctor.name.clone(),
        ind_type.name.clone(),
    ))
}

// ───────────────────────── MONO ROOT (#[no_mangle]) ─────────────────────────
// A single monomorphic, closure-free root the emitter can pick with
// `--mir-emit-closure validate_ctor_root`. It builds a Constructor / InductiveType /
// InductiveDecl from primitives (the ctor type Expr, the inductive name, num_params,
// and 0/1 mutual sibling), runs validate_ctor_return_type, and returns a small i32
// code so each soundness check is DISTINGUISHABLE at the boundary:
//   0 = ACCEPT
//   1 = REJECT: wrong return-type head            (Check 1)
//   2 = REJECT: parameter argument mismatch       (Check 2)
//   3 = REJECT: index argument mentions inductive  (Check 3)
#[no_mangle]
pub extern "C" fn validate_ctor_root(
    ctor_name_raw: u32,
    ind_name_raw: u32,
    ctor_type: &Expr,
    num_params: u32,
    sibling_raw: u32,
    sibling_count: u32,
) -> i32 {
    let ctor_name = Name(ctor_name_raw);
    let ind_name = Name(ind_name_raw);
    let sib = Name(sibling_raw);

    let ctor = Constructor {
        name: ctor_name,
        type_: ctor_type.clone(),
    };
    // NOTE: `validate_ctor_return_type` (the ordinary, non-cubical path) reads ONLY
    // `ind_type.name`, `ctor.type_`/`ctor.name`, `decl.num_params`, and `all_names`.
    // The `constructors` / `types` Vecs are read ONLY by the cubical HIT branch
    // (never taken here), so they are left EMPTY — faithful for the ordinary path and
    // keeping the root's allocations to a single empty `Vec<Constructor>::new` leaf.
    let ind_type = InductiveType {
        name: ind_name,
        type_: Expr::sort0(),
        constructors: vec![],
    };
    let decl = InductiveDecl {
        num_params,
        types: vec![],
    };

    let names_one = [&ind_name];
    let names_two = [&ind_name, &sib];
    let all: &[&Name] = if sibling_count >= 2 {
        &names_two
    } else {
        &names_one
    };

    match validate_ctor_return_type(&ctor, &ind_type, &decl, all) {
        Ok(()) => 0,
        Err(InductiveError::ConstructorReturnType(_, _)) => 1,
        Err(InductiveError::ConstructorParamMismatch { .. }) => 2,
        Err(InductiveError::IndexArgMentionsInductive { .. }) => 3,
    }
}

fn main() {
    let bd = BinderData { info: 0, mult: 0 };
    let nat = Name(11);
    let tree = Name(1); // also the single param's domain name when num_params=1
    let list = Name(12);
    // num_params = 0 cases ───────────────────────────────────────────────
    // GOOD: mk : Nat -> Tree   (head = Tree)  -> 0
    let good = Expr::pi(bd, Expr::const_(nat, vec![]), Expr::const_(tree, vec![]));
    // BAD head: mk : Nat -> Nat   -> 1
    let bad_head = Expr::pi(bd, Expr::const_(nat, vec![]), Expr::const_(nat, vec![]));
    // num_params = 1 cases (param A, the single binder; return must be `Tree (BVar 0)`)
    // GOOD param: mk : (A:Sort) -> Tree (BVar 0)  -> 0  (total_binders=1, expected BVar 0)
    let good_param = Expr::pi(
        bd,
        Expr::sort0(),
        Expr::app(Expr::const_(tree, vec![]), Expr::bvar(0)),
    );
    // BAD param: mk : (A:Sort) -> Tree Nat   (param arg is Nat, not BVar 0)  -> 2
    let bad_param = Expr::pi(
        bd,
        Expr::sort0(),
        Expr::app(Expr::const_(tree, vec![]), Expr::const_(nat, vec![])),
    );
    // BAD index (lean4#2125): mk : (A:Sort) -> Tree (BVar 0) (List Tree)
    //   one param (ok) + one index `List Tree` that MENTIONS Tree  -> 3
    let bad_index = Expr::pi(
        bd,
        Expr::sort0(),
        Expr::app(
            Expr::app(Expr::const_(tree, vec![]), Expr::bvar(0)),
            Expr::app(Expr::const_(list, vec![]), Expr::const_(tree, vec![])),
        ),
    );
    let g = validate_ctor_root(100, 1, &good, 0, 0, 1);
    let b = validate_ctor_root(100, 1, &bad_head, 0, 0, 1);
    let gp = validate_ctor_root(100, 1, &good_param, 1, 0, 1);
    let bp = validate_ctor_root(100, 1, &bad_param, 1, 0, 1);
    let bi = validate_ctor_root(100, 1, &bad_index, 1, 0, 1);
    println!("good={g} bad_head={b} good_param={gp} bad_param={bp} bad_index={bi}");
    let ok = g == 0 && b == 1 && gp == 0 && bp == 2 && bi == 3;
    std::process::exit((!ok) as i32);
}
