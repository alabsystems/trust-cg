// clean_expr_whnf_slice — self-contained slice of the real clean-kernel Expr +
// the three kernel pillars over it: WHNF (reduction), DEF_EQ (equality), and now
// INFER_TYPE (inference). Verbatim modeling of clean/crates/clean-kernel/src
// (expr/meta.rs, cert/reduction.rs whnf_impl, cert/expr_eq.rs def_eq_impl, and
// tc/infer.rs infer_type_fast_inner — the cleanest self-contained typing rules).
//
// Crate name is load-bearing: it appears in the mangled symbols of the trait/extern
// leaves the JIT binds, so it MUST stay `clean_expr_whnf_slice`.
#![allow(dead_code)]
#![allow(clippy::all)]

use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Name(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FVarId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Level { Zero, Succ(Box<Level>), Param(Name) }

impl Level {
    pub fn has_params(&self) -> bool {
        match self { Level::Zero => false, Level::Succ(l) => l.has_params(), Level::Param(_) => true }
    }
    // Slice-model of `Level::is_def_eq` (Zero/Succ/Param congruence; Max/IMax + full
    // universe-unification normalization DEFERRED — not in this Level model).
    pub fn is_def_eq(l1: &Level, l2: &Level) -> bool {
        match (l1, l2) {
            (Level::Zero, Level::Zero) => true,
            (Level::Succ(a), Level::Succ(b)) => Level::is_def_eq(a, b),
            (Level::Param(a), Level::Param(b)) => a.0 == b.0,
            _ => false,
        }
    }
    // succ(l) — for Sort(l) : Sort(succ l). (cloning ctor)
    pub fn succ(l: Level) -> Level { Level::Succ(Box::new(l)) }
    // imax(u, v): the Pi universe. MODELED: imax(u, 0) = 0; else max-of-Succ-depth
    // over the Zero/Succ fragment (the only Levels this slice constructs). Full
    // IMax/Max metavar normalization DEFERRED — see report.
    pub fn imax(u: Level, v: Level) -> Level {
        if Level::is_zero(&v) { return Level::Zero; }
        Level::max(u, v)
    }
    fn is_zero(l: &Level) -> bool { matches!(l, Level::Zero) }
    fn depth(l: &Level) -> u32 {
        match l { Level::Zero => 0, Level::Succ(inner) => 1 + Level::depth(inner), Level::Param(_) => 0 }
    }
    fn of_depth(d: u32) -> Level { if d == 0 { Level::Zero } else { Level::Succ(Box::new(Level::of_depth(d - 1))) } }
    fn max(u: Level, v: Level) -> Level {
        // Over the Zero/Succ fragment this is the deeper of the two. Params fall back
        // to u (DEFERRED — no Param appears in the verified universe cases).
        match (&u, &v) {
            (Level::Param(_), _) | (_, Level::Param(_)) => u,
            _ => Level::of_depth(Level::depth(&u).max(Level::depth(&v))),
        }
    }
}

pub type LevelVec = Vec<Level>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Literal { Nat(u64), Str(u32) }

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BinderData { pub info: u8, pub mult: u8 }

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

pub struct KaniHasher { state: u64 }
impl KaniHasher { fn new() -> Self { KaniHasher { state: 0 } } }
impl std::hash::Hasher for KaniHasher {
    fn finish(&self) -> u64 { self.state }
    fn write(&mut self, bytes: &[u8]) { for &b in bytes { self.state = self.state.wrapping_mul(31).wrapping_add(b as u64); } }
    fn write_u8(&mut self, i: u8) { self.state ^= i as u64; self.state = self.state.wrapping_mul(0x517cc1b727220a95); }
    fn write_u16(&mut self, i: u16) { self.state ^= i as u64; self.state = self.state.wrapping_mul(0x517cc1b727220a95); }
    fn write_u32(&mut self, i: u32) { self.state ^= i as u64; self.state = self.state.wrapping_mul(0x517cc1b727220a95); }
    fn write_u64(&mut self, i: u64) { self.state ^= i; self.state = self.state.wrapping_mul(0x517cc1b727220a95); }
    fn write_u128(&mut self, i: u128) { self.write_u64(i as u64); self.write_u64((i >> 64) as u64); }
    fn write_usize(&mut self, i: usize) { self.write_u64(i as u64); }
}

// Monomorphic per-type hashers (NOT a generic hash_to_u64<T>): a generic helper
// monomorphizes to several same-friendly-named bodies which collide as duplicate
// JIT symbols. These three distinct functions match the whnf/def_eq slice exactly.
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
fn level_has_mvar(_l: &Level) -> bool { false }

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

    fn pack(hash: u32, loose_bvar_range: u32, approx_depth: u32, has_fvar: bool, has_expr_mvar: bool, has_level_mvar: bool, has_level_param: bool) -> Self {
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
    fn raw(self) -> u64 { self.0 }
    fn hash(self) -> u32 { (self.0 & Self::HASH_MASK) as u32 }
    fn approx_depth(self) -> u8 { ((self.0 >> Self::DEPTH_SHIFT) & Self::DEPTH_MASK) as u8 }
    fn has_fvar(self) -> bool { (self.0 >> Self::HAS_FVAR_BIT) & 1 == 1 }
    fn has_expr_mvar(self) -> bool { (self.0 >> Self::HAS_EXPR_MVAR_BIT) & 1 == 1 }
    fn has_level_mvar(self) -> bool { (self.0 >> Self::HAS_LEVEL_MVAR_BIT) & 1 == 1 }
    fn has_level_param(self) -> bool { (self.0 >> Self::HAS_LEVEL_PARAM_BIT) & 1 == 1 }
    fn loose_bvar_range(self) -> u32 { (self.0 >> Self::BVAR_RANGE_SHIFT) as u32 }

    fn mk_app_meta(f: ExprMeta, a: ExprMeta) -> ExprMeta {
        let depth = (f.approx_depth().max(a.approx_depth()) as u32 + 1).min(Self::MAX_DEPTH);
        let range = f.loose_bvar_range().max(a.loose_bvar_range());
        let h = mix_hash(f.0, a.0) as u32;
        let flags = (f.0 | a.0) & (0xF_u64 << Self::HAS_FVAR_BIT);
        let bits = (h as u64) | ((depth as u64) << Self::DEPTH_SHIFT) | flags | ((range as u64) << Self::BVAR_RANGE_SHIFT);
        ExprMeta(bits)
    }
    fn mk_binder_meta(ty: ExprMeta, body: ExprMeta, extra_hash: u64) -> ExprMeta {
        let depth = (ty.approx_depth().max(body.approx_depth()) as u32 + 1).min(Self::MAX_DEPTH);
        let body_range = body.loose_bvar_range().saturating_sub(1);
        let range = ty.loose_bvar_range().max(body_range);
        let h = mix_hash(depth as u64, mix_hash(ty.hash() as u64, mix_hash(body.hash() as u64, extra_hash))) as u32;
        ExprMeta::pack(h, range, depth, ty.has_fvar() || body.has_fvar(), ty.has_expr_mvar() || body.has_expr_mvar(), ty.has_level_mvar() || body.has_level_mvar(), ty.has_level_param() || body.has_level_param())
    }
    fn mk_let_meta(ty: ExprMeta, val: ExprMeta, body: ExprMeta) -> ExprMeta {
        let depth = (ty.approx_depth().max(val.approx_depth()).max(body.approx_depth()) as u32 + 1).min(Self::MAX_DEPTH);
        let body_range = body.loose_bvar_range().saturating_sub(1);
        let range = ty.loose_bvar_range().max(val.loose_bvar_range()).max(body_range);
        let h = mix_hash(depth as u64, mix_hash(ty.hash() as u64, mix_hash(val.hash() as u64, body.hash() as u64))) as u32;
        ExprMeta::pack(h, range, depth, ty.has_fvar() || val.has_fvar() || body.has_fvar(), ty.has_expr_mvar() || val.has_expr_mvar() || body.has_expr_mvar(), ty.has_level_mvar() || val.has_level_mvar() || body.has_level_mvar(), ty.has_level_param() || val.has_level_param() || body.has_level_param())
    }
    fn mk_wrapper_meta(inner: ExprMeta, extra_hash: u64) -> ExprMeta {
        let depth = (inner.approx_depth() as u32 + 1).min(Self::MAX_DEPTH);
        let h = mix_hash(depth as u64, mix_hash(inner.hash() as u64, extra_hash)) as u32;
        ExprMeta::pack(h, inner.loose_bvar_range(), depth, inner.has_fvar(), inner.has_expr_mvar(), inner.has_level_mvar(), inner.has_level_param())
    }
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
}

impl ExprKind {
    fn compute_meta(&self) -> ExprMeta {
        match self {
            ExprKind::BVar(idx) => ExprMeta::pack(mix_hash(7, *idx as u64) as u32, idx.saturating_add(1), 0, false, false, false, false),
            ExprKind::App(f, a) => ExprMeta::mk_app_meta(f.meta(), a.meta()),
            ExprKind::Lam(_bi, ty, body) => ExprMeta::mk_binder_meta(ty.meta(), body.meta(), 0),
            ExprKind::Pi(_bi, ty, body) => ExprMeta::mk_binder_meta(ty.meta(), body.meta(), 1),
            ExprKind::FVar(id) => ExprMeta::pack(mix_hash(13, id.0) as u32, 0, 0, true, false, false, false),
            ExprKind::Sort(lvl) => ExprMeta::pack(mix_hash(11, hash_level(lvl)) as u32, 0, 0, false, false, level_has_mvar(lvl), lvl.has_params()),
            ExprKind::Const(name, _levels) => {
                let name_hash = hash_name(name);
                ExprMeta::pack(mix_hash(5, name_hash) as u32, 0, 0, false, false, false, false)
            }
            ExprKind::Let(_, ty, val, body, _) => ExprMeta::mk_let_meta(ty.meta(), val.meta(), body.meta()),
            ExprKind::Lit(lit) => ExprMeta::pack(mix_hash(3, hash_lit(lit)) as u32, 0, 0, false, false, false, false),
            ExprKind::Proj(name, idx, expr) => {
                let inner = expr.meta();
                let depth = (inner.approx_depth() as u32 + 1).min(255);
                let h = mix_hash(depth as u64, mix_hash(hash_name(name), mix_hash(*idx as u64, inner.hash() as u64))) as u32;
                ExprMeta::pack(h, inner.loose_bvar_range(), depth, inner.has_fvar(), inner.has_expr_mvar(), inner.has_level_mvar(), inner.has_level_param())
            }
            ExprKind::MData(_, expr) => ExprMeta::mk_wrapper_meta(expr.meta(), 0),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Expr { kind: ExprKind, meta: ExprMeta }

impl Expr {
    fn from_kind(kind: ExprKind) -> Self { let meta = kind.compute_meta(); Expr { kind, meta } }
    fn meta(&self) -> ExprMeta { self.meta }
    fn kind(&self) -> &ExprKind { &self.kind }
    fn loose_bvar_range(&self) -> u32 { self.meta.loose_bvar_range() }
    fn bvar(idx: u32) -> Self { Expr::from_kind(ExprKind::BVar(idx)) }
    fn cnst(name: Name) -> Self { Expr::from_kind(ExprKind::Const(name, vec![])) }
    fn sort0() -> Self { Expr::from_kind(ExprKind::Sort(Level::Zero)) }
    fn sort(l: Level) -> Self { Expr::from_kind(ExprKind::Sort(l)) }
    fn nat(n: u64) -> Self { Expr::from_kind(ExprKind::Lit(Literal::Nat(n))) }
    fn app(func: Expr, arg: Expr) -> Self { Expr::from_kind(ExprKind::App(Arc::new(func), Arc::new(arg))) }
    fn lam(bd: BinderData, ty: Expr, body: Expr) -> Self { Expr::from_kind(ExprKind::Lam(bd, Arc::new(ty), Arc::new(body))) }
    fn pi(bd: BinderData, ty: Expr, body: Expr) -> Self { Expr::from_kind(ExprKind::Pi(bd, Arc::new(ty), Arc::new(body))) }
    fn lett(name: Name, ty: Expr, val: Expr, body: Expr, nondep: bool) -> Self { Expr::from_kind(ExprKind::Let(name, Arc::new(ty), Arc::new(val), Arc::new(body), nondep)) }
    fn proj(name: Name, idx: u32, e: Expr) -> Self { Expr::from_kind(ExprKind::Proj(name, idx, Arc::new(e))) }
    fn mdata(tag: u32, e: Expr) -> Self { Expr::from_kind(ExprKind::MData(tag, Arc::new(e))) }

    // VERBATIM lift_at.
    fn lift_at(&self, start: u32, amount: u32) -> Expr {
        if amount == 0 { return self.clone(); }
        if start >= self.loose_bvar_range() { return self.clone(); }
        match &self.kind {
            ExprKind::BVar(idx) => { if *idx >= start { Expr::bvar(idx.saturating_add(amount)) } else { self.clone() } }
            ExprKind::App(f, a) => Expr::app(f.lift_at(start, amount), a.lift_at(start, amount)),
            ExprKind::Lam(bd, ty, body) => Expr::lam(*bd, ty.lift_at(start, amount), body.lift_at(start.saturating_add(1), amount)),
            ExprKind::Pi(bd, ty, body) => Expr::pi(*bd, ty.lift_at(start, amount), body.lift_at(start.saturating_add(1), amount)),
            _ => self.clone(),
        }
    }
    fn lift_from(&self, start: u32, amount: u32) -> Expr { self.lift_at(start, amount) }
    // VERBATIM instantiate / instantiate_at.
    fn instantiate(&self, val: &Expr) -> Expr { self.instantiate_at(val, 0) }
    fn instantiate_at(&self, val: &Expr, depth: u32) -> Expr {
        if depth >= self.loose_bvar_range() { return self.clone(); }
        match &self.kind {
            ExprKind::BVar(idx) => {
                if *idx == depth { val.lift_at(0, depth) }
                else if *idx > depth { Expr::bvar(idx.saturating_sub(1)) }
                else { self.clone() }
            }
            ExprKind::App(f, a) => Expr::app(f.instantiate_at(val, depth), a.instantiate_at(val, depth)),
            ExprKind::Lam(bd, ty, body) => Expr::lam(*bd, ty.instantiate_at(val, depth), body.instantiate_at(val, depth.saturating_add(1))),
            ExprKind::Pi(bd, ty, body) => Expr::pi(*bd, ty.instantiate_at(val, depth), body.instantiate_at(val, depth.saturating_add(1))),
            ExprKind::Let(name, ty, val_e, body, nondep) => Expr::lett(*name, ty.instantiate_at(val, depth), val_e.instantiate_at(val, depth), body.instantiate_at(val, depth.saturating_add(1)), *nondep),
            ExprKind::Proj(name, idx, e) => Expr::proj(*name, *idx, e.instantiate_at(val, depth)),
            _ => self.clone(),
        }
    }
    // VERBATIM get_app_fn (clone-returning).
    fn get_app_fn(&self) -> Expr {
        let mut current = self.clone();
        loop {
            let next = match &current.kind { ExprKind::App(f, _) => f.as_ref().clone(), _ => return current };
            current = next;
        }
    }
    // VERBATIM get_app_args (collect innermost-first, reverse to source order).
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

// Modeled environment (slice-scan): for each Const name, an optional unfolding
// value (delta). Layout is IDENTICAL to the whnf/def_eq slice (2 fields, 4 words)
// so the JIT `self` ABI is shared across all three pillars' tests.
pub struct CertVerifier<'env> {
    env: &'env [(Name, Option<Expr>)],
    ctors: &'env [(Name, u32)],
}

impl<'env> CertVerifier<'env> {
    fn unfold_const(&self, name: &Name) -> Option<Expr> {
        let mut i: usize = 0;
        let n = self.env.len();
        while i < n {
            let entry = &self.env[i];
            if entry.0 == *name { return entry.1.clone(); }
            i += 1;
        }
        None
    }
    fn get_constructor_num_params(&self, name: &Name) -> Option<u32> {
        let mut i: usize = 0;
        let n = self.ctors.len();
        while i < n {
            let entry = &self.ctors[i];
            if entry.0 == *name { return Some(entry.1); }
            i += 1;
        }
        None
    }
    // Modeled env type lookup for the Const typing rule. The real env stores a
    // declared `type_` per constant; here the modeled env carries the constant's
    // unfolding value, so the constant's TYPE is the inferred type of that value
    // (faithful for non-recursive defs: `def c := v` has `c : typeof(v)`). A
    // constant with no unfolding (opaque axiom) has no modeled type. Level-param
    // instantiation DEFERRED — see report.
    fn const_type(&self, name: &Name) -> Option<Expr> {
        match self.unfold_const(name) {
            Some(val) => match self.infer_type(&val) {
                Ok(ty) => Some(ty),
                Err(_) => None,
            },
            None => None,
        }
    }
    fn try_iota_reduction(&self, _e: &Expr) -> Option<Expr> { None }
    fn try_quot_reduction(&self, _e: &Expr) -> Option<Expr> { None }

    // ── WHNF pillar (cert/reduction.rs) — VERIFIED, reused by def_eq + infer. ──
    fn whnf_impl(&self, e: &Expr) -> Expr { self.whnf_inner(e) }
    fn whnf_inner(&self, e: &Expr) -> Expr {
        match &e.kind {
            ExprKind::App(f, a) => {
                let f_whnf = self.whnf_impl(f);
                match &f_whnf.kind {
                    ExprKind::Lam(_, _, body) => { let reduced = body.instantiate(a); self.whnf_impl(&reduced) }
                    _ => {
                        let app = Expr::from_kind(ExprKind::App(Arc::new(f_whnf), a.clone()));
                        if let Some(reduced) = self.try_iota_reduction(&app) { return self.whnf_impl(&reduced); }
                        if let Some(reduced) = self.try_quot_reduction(&app) { return self.whnf_impl(&reduced); }
                        app
                    }
                }
            }
            ExprKind::Let(_, _, val, body, _) => { let reduced = body.instantiate(val); self.whnf_impl(&reduced) }
            ExprKind::Const(name, _levels) => match self.unfold_const(name) {
                Some(val) => self.whnf_impl(&val),
                None => e.clone(),
            },
            ExprKind::Proj(struct_name, idx, expr) => self.reduce_proj(struct_name, *idx, expr),
            ExprKind::MData(_, inner) => self.whnf_impl(inner),
            _ => e.clone(),
        }
    }
    fn reduce_proj(&self, struct_name: &Name, idx: u32, expr: &Expr) -> Expr {
        let expr_whnf = self.whnf_impl(expr);
        let head = expr_whnf.get_app_fn();
        if let ExprKind::Const(ctor_name, _) = &head.kind {
            if let Some(num_params) = self.get_constructor_num_params(ctor_name) {
                let args = expr_whnf.get_app_args();
                let field_idx = num_params as usize + idx as usize;
                if field_idx < args.len() { return self.whnf_impl(&args[field_idx]); }
            }
        }
        Expr::from_kind(ExprKind::Proj(*struct_name, idx, Arc::new(expr_whnf)))
    }

    // ── DEF-EQ pillar (cert/expr_eq.rs) — VERIFIED, reused by infer (App/Let arg check). ──
    fn level_eq(&self, l1: &Level, l2: &Level) -> bool { Level::is_def_eq(l1, l2) }
    fn level_vec_eq(&self, ls1: &[Level], ls2: &[Level]) -> bool {
        if ls1.len() != ls2.len() { return false; }
        let mut i: usize = 0;
        let n = ls1.len();
        while i < n {
            if !self.level_eq(&ls1[i], &ls2[i]) { return false; }
            i += 1;
        }
        true
    }
    fn structural_eq(&self, a: &Expr, b: &Expr) -> bool {
        match (&a.kind, &b.kind) {
            (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
            (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => self.level_eq(l1, l2),
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => n1 == n2 && self.level_vec_eq(ls1, ls2),
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => self.structural_eq(f1, f2) && self.structural_eq(a1, a2),
            (ExprKind::Lam(_b1, ty1, b1), ExprKind::Lam(_b2, ty2, b2))
            | (ExprKind::Pi(_b1, ty1, b1), ExprKind::Pi(_b2, ty2, b2)) => self.structural_eq(ty1, ty2) && self.structural_eq(b1, b2),
            (ExprKind::Let(_, ty1, v1, b1, _), ExprKind::Let(_, ty2, v2, b2, _)) => self.structural_eq(ty1, ty2) && self.structural_eq(v1, v2) && self.structural_eq(b1, b2),
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => n1 == n2 && i1 == i2 && self.structural_eq(e1, e2),
            (ExprKind::MData(_, in1), ExprKind::MData(_, in2)) => self.structural_eq(in1, in2),
            _ => false,
        }
    }
    fn is_def_eq(&self, a: &Expr, b: &Expr) -> bool { self.def_eq_inner(a, b) }
    fn def_eq_impl(&self, a: &Expr, b: &Expr) -> bool { self.def_eq_inner(a, b) }
    fn def_eq_inner(&self, a: &Expr, b: &Expr) -> bool {
        let a_whnf = self.whnf_impl(a);
        let b_whnf = self.whnf_impl(b);
        if a_whnf.meta.raw() == b_whnf.meta.raw() && self.structural_eq(&a_whnf, &b_whnf) {
            return true;
        }
        let matched = match (&a_whnf.kind, &b_whnf.kind) {
            (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
            (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => self.level_eq(l1, l2),
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => n1 == n2 && self.level_vec_eq(ls1, ls2),
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => self.def_eq_impl(f1, f2) && self.def_eq_impl(a1, a2),
            (ExprKind::Lam(_b1, ty1, b1), ExprKind::Lam(_b2, ty2, b2))
            | (ExprKind::Pi(_b1, ty1, b1), ExprKind::Pi(_b2, ty2, b2)) => self.def_eq_impl(ty1, ty2) && self.def_eq_impl(b1, b2),
            (ExprKind::Let(_, ty1, v1, b1, _), ExprKind::Let(_, ty2, v2, b2, _)) => self.def_eq_impl(ty1, ty2) && self.def_eq_impl(v1, v2) && self.def_eq_impl(b1, b2),
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => n1 == n2 && i1 == i2 && self.def_eq_impl(e1, e2),
            (ExprKind::MData(_, in1), ExprKind::MData(_, in2)) => self.def_eq_impl(in1, in2),
            _ => false,
        };
        if matched { return true; }
        self.try_eta_expansion(&a_whnf, &b_whnf)
    }
    fn try_eta_expansion(&self, a: &Expr, b: &Expr) -> bool {
        match (&a.kind, &b.kind) {
            (ExprKind::Lam(_, _ty, body), _) => {
                let other_lifted = b.lift_from(0, 1);
                let other_applied = Expr::app(other_lifted, Expr::bvar(0));
                self.def_eq_impl(body, &other_applied)
            }
            (_, ExprKind::Lam(_, _ty, body)) => {
                let other_lifted = a.lift_from(0, 1);
                let other_applied = Expr::app(other_lifted, Expr::bvar(0));
                self.def_eq_impl(body, &other_applied)
            }
            _ => false,
        }
    }

    // ── INFER-TYPE pillar (tc/infer.rs infer_type_fast_inner) — the 3rd pillar. ──
    // Typing rules over the production Expr, threading a de-Bruijn-indexed
    // local_context (Vec<Expr> of binder types; push on entering a binder, index on
    // BVar, pop on leaving) — the verify_impl context pattern. Composes the VERIFIED
    // whnf (to expose Pi/Sort heads) + def_eq (to check argument / let-value types) +
    // instantiate (to substitute the App argument into the Pi result).
    fn infer_type(&self, e: &Expr) -> Result<Expr, TypeError> {
        let mut ctx: Vec<Expr> = Vec::new();
        self.infer_type_core(e, &mut ctx)
    }

    fn infer_type_core(&self, e: &Expr, ctx: &mut Vec<Expr>) -> Result<Expr, TypeError> {
        match &e.kind {
            // Sort(l) : Sort(succ l).
            ExprKind::Sort(l) => Ok(Expr::sort(Level::succ(l.clone()))),

            // BVar(i): the i-th binder counting OUTWARD from the use site. The context
            // is innermost-last; the type was recorded under fewer binders, so lift it
            // by (i+1) to move it into the current scope.
            ExprKind::BVar(idx) => {
                let depth = ctx.len();
                if (*idx as usize) >= depth {
                    return Err(TypeError::UnboundVariable(*idx));
                }
                let pos = depth - 1 - (*idx as usize);
                let raw = ctx[pos].clone();
                Ok(raw.lift_at(0, idx.saturating_add(1)))
            }

            // Const(n, _levels): the modeled env's declared type (already instantiated).
            ExprKind::Const(name, _levels) => match self.const_type(name) {
                Some(ty) => Ok(ty),
                None => Err(TypeError::UnknownConst(*name)),
            },

            // App(f, a): infer f, whnf to a Pi(A, B); check a : A by def_eq; the
            // result is B with `a` instantiated for the bound variable.
            ExprKind::App(f, a) => {
                let f_type = self.infer_type_core(f, ctx)?;
                let f_type_whnf = self.whnf_impl(&f_type);
                match &f_type_whnf.kind {
                    ExprKind::Pi(_, expected_arg_type, result_type) => {
                        let arg_type = self.infer_type_core(a, ctx)?;
                        if !self.is_def_eq(&arg_type, expected_arg_type) {
                            return Err(TypeError::TypeMismatch {
                                expected: Arc::new(expected_arg_type.as_ref().clone()),
                                inferred: Arc::new(arg_type),
                            });
                        }
                        Ok(result_type.instantiate(a))
                    }
                    _ => Err(TypeError::NotAPi { ty: Arc::new(f_type) }),
                }
            }

            // Lam(A, body) : Pi(A, B) where body : B under the context extended by A.
            ExprKind::Lam(bi, arg_type, body) => {
                let arg_sort = self.infer_type_core(arg_type, ctx)?;
                let arg_sort_whnf = self.whnf_impl(&arg_sort);
                match &arg_sort_whnf.kind {
                    ExprKind::Sort(_) => {}
                    _ => return Err(TypeError::ExpectedSort { ty: Arc::new(arg_sort) }),
                }
                ctx.push(arg_type.as_ref().clone());
                let body_type = self.infer_type_core(body, ctx);
                ctx.pop();
                let body_type = body_type?;
                Ok(Expr::pi(*bi, arg_type.as_ref().clone(), body_type))
            }

            // Pi(A, B) : Sort(imax u v) where A : Sort u, B : Sort v.
            ExprKind::Pi(_bi, arg_type, body) => {
                let arg_sort = self.infer_type_core(arg_type, ctx)?;
                let arg_sort_whnf = self.whnf_impl(&arg_sort);
                let l1 = match &arg_sort_whnf.kind {
                    ExprKind::Sort(l) => l.clone(),
                    _ => return Err(TypeError::ExpectedSort { ty: Arc::new(arg_sort) }),
                };
                ctx.push(arg_type.as_ref().clone());
                let body_sort = self.infer_type_core(body, ctx);
                ctx.pop();
                let body_sort = body_sort?;
                let body_sort_whnf = self.whnf_impl(&body_sort);
                let l2 = match &body_sort_whnf.kind {
                    ExprKind::Sort(l) => l.clone(),
                    _ => return Err(TypeError::ExpectedSort { ty: Arc::new(body_sort) }),
                };
                Ok(Expr::sort(Level::imax(l1, l2)))
            }

            // Let(_, A, val, body): check val : A by def_eq, infer body under the
            // context extended by A, then zeta-substitute val into the body type.
            ExprKind::Let(_name, ty, val, body, _nondep) => {
                let ty_sort = self.infer_type_core(ty, ctx)?;
                let ty_sort_whnf = self.whnf_impl(&ty_sort);
                match &ty_sort_whnf.kind {
                    ExprKind::Sort(_) => {}
                    _ => return Err(TypeError::ExpectedSort { ty: Arc::new(ty_sort) }),
                }
                let val_type = self.infer_type_core(val, ctx)?;
                if !self.is_def_eq(&val_type, ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: Arc::new(ty.as_ref().clone()),
                        inferred: Arc::new(val_type),
                    });
                }
                ctx.push(ty.as_ref().clone());
                let body_type = self.infer_type_core(body, ctx);
                ctx.pop();
                let body_type = body_type?;
                // zeta: substitute the let value for the bound variable in the body type.
                Ok(body_type.instantiate(val))
            }

            // Lit : modeled Nat/String const types. The const Name is built from a
            // scalar literal at the call site (Name(u32)) so no ADT-constant arg is
            // passed by value across the cnst() call.
            ExprKind::Lit(lit) => Ok(match lit {
                Literal::Nat(_) => Expr::cnst(Name(0xFFFF_0001)),
                Literal::Str(_) => Expr::cnst(Name(0xFFFF_0002)),
            }),

            // MData is transparent.
            ExprKind::MData(_, inner) => self.infer_type_core(inner, ctx),

            // Proj / FVar inference DEFERRED (need full struct-projection typing /
            // an FVar-decl context) — see report.
            _ => Err(TypeError::Unsupported),
        }
    }
}

// Slice TypeError: carries the offending Expr/Name directly (no format!/String).
#[derive(Clone, Debug)]
pub enum TypeError {
    UnboundVariable(u32),
    UnknownConst(Name),
    TypeMismatch { expected: Arc<Expr>, inferred: Arc<Expr> },
    NotAPi { ty: Arc<Expr> },
    ExpectedSort { ty: Arc<Expr> },
    Unsupported,
}

// Concrete monomorphization roots (lib codegen only seeds reachable items from
// exported symbols; the lifetime-generic CertVerifier methods need a concrete
// caller to be instantiated). These force `infer_type` (and the whnf/def_eq/
// instantiate it composes) into the mono set so `--mir-emit-closure` finds them.
// They are NOT part of the verified bodies — only scaffolding for emission.
#[no_mangle]
pub extern "C" fn __root_infer_type(v: &CertVerifier, e: &Expr) -> bool {
    v.infer_type(e).is_ok()
}

#[no_mangle]
pub extern "C" fn __root_def_eq(v: &CertVerifier, a: &Expr, b: &Expr) -> bool {
    v.def_eq_impl(a, b)
}

#[no_mangle]
pub extern "C" fn __root_whnf(v: &CertVerifier, e: &Expr) -> u64 {
    v.whnf_impl(e).meta().raw()
}
