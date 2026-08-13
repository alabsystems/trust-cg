// clean_struct_eta_slice — self-contained slice of the STRUCTURE-ETA def-eq
// completeness rule `try_structure_eta_core`
// (clean/crates/clean-kernel/src/tc/def_eq/structural.rs:181), the remaining
// def_eq completeness gap. The verified cert def_eq has FUNCTION-eta
// (try_eta_expansion) but not STRUCTURE-eta.
//
// STRUCTURE ETA (Lean 4 type_checker.cpp:786-811 try_eta_struct_core):
//   For a single-constructor inductive S (a "structure"), any value s : S is
//   def-eq to `S.mk (s.1) (s.2) .. (s.n)` (the constructor applied to its
//   projections). During def_eq, when `t` is LITERALLY a saturated ctor-app
//   `S.mk a_1 .. a_n` of a structure-like S, and `s` (the neutral other side)
//   has type S, then `t =?= s` succeeds iff FIELDWISE `Proj i s =?= a_i`.
//
// This is a COMPLETENESS + COHERENCE rule: an incompleteness here = the kernel
// REJECTS definitionally-equal structure terms -> a valid proof fails to check.
// The SOUNDNESS direction is that it must NOT wrongly ACCEPT: this rule only
// fires when `t` is a real ctor-app of a genuine structure-like inductive, and
// the actual accept/reject is delegated to the VERIFIED def_eq on the fields
// (distinct field values are correctly rejected).
//
// Composes the VERIFIED kernel pillars over the real clean-kernel Expr:
//   - WHNF        (cert/reduction.rs whnf_impl)  — VERIFIED, reused
//   - reduce_proj (whnf's Proj arm)              — VERIFIED, reused
//   - DEF_EQ      (cert/expr_eq.rs def_eq_impl)  — VERIFIED, reused (on the fields)
//   - INFER_TYPE  (tc/infer.rs infer_type)       — VERIFIED, reused (type of `s`)
// plus the NEW gate machinery on top:
//   - is_structure_like  (tc/eta.rs:81)          — the inductive-registry gate
//     (exactly 1 ctor, no indices, non-recursive)
//   - try_structure_eta_core   (def_eq/structural.rs:181) — the fieldwise algorithm
//   - try_structure_eta_expansion (structural.rs:158) — both-orientations entry
//
// The inductive info is modeled as a slice-scan (the inductive-gate slices'
// pattern): an inductive registry {name, num_ctors, ctor_name, num_indices,
// is_recursive} and a constructor registry {ctor_name, inductive_name,
// num_params, num_fields}. This mirrors the real Environment.get_inductive /
// get_constructor lookups the eta code performs.
//
// Crate name is load-bearing (mangled into the extern-leaf symbols the JIT
// binds), so it MUST stay `clean_struct_eta_slice`.
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
pub enum Level { Zero, Succ(Box<Level>), Param(Name) }

impl Level {
    pub fn has_params(&self) -> bool {
        match self { Level::Zero => false, Level::Succ(l) => l.has_params(), Level::Param(_) => true }
    }
    pub fn is_def_eq(l1: &Level, l2: &Level) -> bool {
        match (l1, l2) {
            (Level::Zero, Level::Zero) => true,
            (Level::Succ(a), Level::Succ(b)) => Level::is_def_eq(a, b),
            (Level::Param(a), Level::Param(b)) => a.0 == b.0,
            _ => false,
        }
    }
    pub fn succ(l: Level) -> Level { Level::Succ(Box::new(l)) }
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

// ───────────────────────── Expr / ExprKind ─────────────────────────

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
    fn const_(name: Name, levels: LevelVec) -> Self { Expr::from_kind(ExprKind::Const(name, levels)) }
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
    // VERBATIM get_app_fn (the VERIFIED App-spine pillar, reused).
    fn get_app_fn(&self) -> Expr {
        let mut current = self.clone();
        loop {
            let next = match &current.kind { ExprKind::App(f, _) => f.as_ref().clone(), _ => return current };
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

// ───────────────────────── InductiveType / Constructor (the registry model) ──
// The FAITHFUL model of the real Environment's inductive/constructor tables the
// eta code consults. The real `InductiveType` (inductive/mod.rs) carries
// `constructor_names: Vec<Name>`, `num_indices: u32`, `is_recursive: bool`
// (is_structure_like reads exactly these three). The real `Constructor` carries
// `inductive_name: Name`, `num_params: u32`, `num_fields: u32` (try_structure_eta_core
// reads exactly these). Modeled as compact records + a slice-scan registry — the
// same inductive-info modeling the inductive-gate slices use.

#[derive(Clone, Debug)]
pub struct InductiveInfo {
    pub name: Name,
    pub num_ctors: u32,
    pub num_indices: u32,
    pub is_recursive: bool,
}

#[derive(Clone, Debug)]
pub struct ConstructorInfo {
    pub ctor_name: Name,
    pub inductive_name: Name,
    pub num_params: u32,
    pub num_fields: u32,
}

// ───────────────────────── TypeError ─────────────────────────
#[derive(Clone, Debug)]
pub enum TypeError {
    UnboundVariable(u32),
    UnknownConst(Name),
    TypeMismatch { expected: Arc<Expr>, inferred: Arc<Expr> },
    NotAPi { ty: Arc<Expr> },
    ExpectedSort { ty: Arc<Expr> },
    Unsupported,
}

// ═══════════════════════ CertVerifier (the modeled Environment) ═════════════
// Five slice-scan tables mirror the real Environment lookups:
//   env         — Const delta-unfolding value (whnf)
//   ctor_np     — a constructor's num_params (reduce_proj's field offset)
//   decl_types  — a Const's declared type (infer_type's Const rule)
//   inductives  — the InductiveType registry (is_structure_like's 3-field gate)
//   ctors       — the Constructor registry (try_structure_eta_core's fields)
pub struct CertVerifier<'env> {
    env: &'env [(Name, Option<Expr>)],
    ctor_np: &'env [(Name, u32)],
    decl_types: &'env [(Name, Expr)],
    inductives: &'env [InductiveInfo],
    ctors: &'env [ConstructorInfo],
}

impl<'env> CertVerifier<'env> {
    // ── registry lookups (slice-scan model of Environment.get_*) ──
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
        let n = self.ctor_np.len();
        while i < n {
            let entry = &self.ctor_np[i];
            if entry.0 == *name { return Some(entry.1); }
            i += 1;
        }
        None
    }
    fn const_type(&self, name: &Name) -> Option<Expr> {
        let mut i: usize = 0;
        let n = self.decl_types.len();
        while i < n {
            let entry = &self.decl_types[i];
            if entry.0 == *name { return Some(entry.1.clone()); }
            i += 1;
        }
        match self.unfold_const(name) {
            Some(val) => match self.infer_type(&val) { Ok(ty) => Some(ty), Err(_) => None },
            None => None,
        }
    }
    // get_inductive(name): the InductiveType record (is_structure_like reads it).
    fn get_inductive(&self, name: &Name) -> Option<InductiveInfo> {
        let mut i: usize = 0;
        let n = self.inductives.len();
        while i < n {
            let entry = &self.inductives[i];
            if entry.name == *name { return Some(entry.clone()); }
            i += 1;
        }
        None
    }
    // get_constructor(name): the Constructor record (try_structure_eta_core reads it).
    fn get_constructor(&self, name: &Name) -> Option<ConstructorInfo> {
        let mut i: usize = 0;
        let n = self.ctors.len();
        while i < n {
            let entry = &self.ctors[i];
            if entry.ctor_name == *name { return Some(entry.clone()); }
            i += 1;
        }
        None
    }

    // ── WHNF pillar (cert/reduction.rs whnf_impl) — VERIFIED, reused. ──
    fn whnf_impl(&self, e: &Expr) -> Expr { self.whnf_inner(e) }
    fn whnf_inner(&self, e: &Expr) -> Expr {
        match &e.kind {
            ExprKind::App(f, a) => {
                let f_whnf = self.whnf_impl(f);
                match &f_whnf.kind {
                    ExprKind::Lam(_, _, body) => { let reduced = body.instantiate(a); self.whnf_impl(&reduced) }
                    _ => {
                        let app = Expr::from_kind(ExprKind::App(Arc::new(f_whnf), a.clone()));
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
    // reduce_proj — the Proj arm of whnf (VERIFIED pillar). Projects the field
    // out of a ctor-app, else re-forms the neutral Proj.
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

    // ── DEF-EQ pillar (cert/expr_eq.rs def_eq_impl) — VERIFIED, reused on fields. ──
    fn level_eq(&self, l1: &Level, l2: &Level) -> bool { Level::is_def_eq(l1, l2) }
    fn level_vec_eq(&self, ls1: &[Level], ls2: &[Level]) -> bool {
        if ls1.len() != ls2.len() { return false; }
        let mut i: usize = 0;
        let n = ls1.len();
        while i < n { if !self.level_eq(&ls1[i], &ls2[i]) { return false; } i += 1; }
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
    // function-eta (the ALREADY-VERIFIED cert eta template) — kept so def_eq is
    // the full verified pillar; structure-eta below is the NEW additive rule.
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

    // ── INFER-TYPE pillar (tc/infer.rs) — VERIFIED, reused (type of the neutral `s`). ──
    fn infer_type(&self, e: &Expr) -> Result<Expr, TypeError> {
        let mut ctx: Vec<Expr> = Vec::new();
        self.infer_type_core(e, &mut ctx)
    }
    fn infer_type_core(&self, e: &Expr, ctx: &mut Vec<Expr>) -> Result<Expr, TypeError> {
        match &e.kind {
            ExprKind::Sort(l) => Ok(Expr::sort(Level::succ(l.clone()))),
            ExprKind::BVar(idx) => {
                let depth = ctx.len();
                if (*idx as usize) >= depth { return Err(TypeError::UnboundVariable(*idx)); }
                let pos = depth - 1 - (*idx as usize);
                let raw = ctx[pos].clone();
                Ok(raw.lift_at(0, idx.saturating_add(1)))
            }
            ExprKind::Const(name, _levels) => match self.const_type(name) {
                Some(ty) => Ok(ty),
                None => Err(TypeError::UnknownConst(*name)),
            },
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
            ExprKind::Lam(bi, arg_type, body) => {
                let arg_sort = self.infer_type_core(arg_type, ctx)?;
                let arg_sort_whnf = self.whnf_impl(&arg_sort);
                match &arg_sort_whnf.kind { ExprKind::Sort(_) => {} _ => return Err(TypeError::ExpectedSort { ty: Arc::new(arg_sort) }) }
                ctx.push(arg_type.as_ref().clone());
                let body_type = self.infer_type_core(body, ctx);
                ctx.pop();
                let body_type = body_type?;
                Ok(Expr::pi(*bi, arg_type.as_ref().clone(), body_type))
            }
            ExprKind::Pi(_bi, arg_type, body) => {
                let arg_sort = self.infer_type_core(arg_type, ctx)?;
                let arg_sort_whnf = self.whnf_impl(&arg_sort);
                let l1 = match &arg_sort_whnf.kind { ExprKind::Sort(l) => l.clone(), _ => return Err(TypeError::ExpectedSort { ty: Arc::new(arg_sort) }) };
                ctx.push(arg_type.as_ref().clone());
                let body_sort = self.infer_type_core(body, ctx);
                ctx.pop();
                let body_sort = body_sort?;
                let body_sort_whnf = self.whnf_impl(&body_sort);
                let l2 = match &body_sort_whnf.kind { ExprKind::Sort(l) => l.clone(), _ => return Err(TypeError::ExpectedSort { ty: Arc::new(body_sort) }) };
                Ok(Expr::sort(Level::imax(l1, l2)))
            }
            ExprKind::Let(_name, ty, val, body, _nondep) => {
                let ty_sort = self.infer_type_core(ty, ctx)?;
                let ty_sort_whnf = self.whnf_impl(&ty_sort);
                match &ty_sort_whnf.kind { ExprKind::Sort(_) => {} _ => return Err(TypeError::ExpectedSort { ty: Arc::new(ty_sort) }) }
                let val_type = self.infer_type_core(val, ctx)?;
                if !self.is_def_eq(&val_type, ty) {
                    return Err(TypeError::TypeMismatch { expected: Arc::new(ty.as_ref().clone()), inferred: Arc::new(val_type) });
                }
                ctx.push(ty.as_ref().clone());
                let body_type = self.infer_type_core(body, ctx);
                ctx.pop();
                let body_type = body_type?;
                Ok(body_type.instantiate(val))
            }
            ExprKind::Lit(lit) => Ok(match lit {
                Literal::Nat(_) => Expr::cnst(Name(0xFFFF_0001)),
                Literal::Str(_) => Expr::cnst(Name(0xFFFF_0002)),
            }),
            ExprKind::MData(_, inner) => self.infer_type_core(inner, ctx),
            _ => Err(TypeError::Unsupported),
        }
    }

    // ══════════════════════════════════════════════════════════════════════
    // NEW GATE MACHINERY (structure-eta def-eq)
    // ══════════════════════════════════════════════════════════════════════

    // ── is_structure_like — VERBATIM tc/eta.rs:81.
    // An inductive is "structure-like" iff it has EXACTLY ONE constructor, NO
    // indices, and is NOT recursive. Only such inductives support eta:
    // s ≡ S.mk s.1 s.2 ... s.n. A missing inductive is not structure-like.
    fn is_structure_like(&self, name: &Name) -> bool {
        let ind = match self.get_inductive(name) { Some(i) => i, None => return false };
        ind.num_ctors == 1 && ind.num_indices == 0 && !ind.is_recursive
    }

    // ── try_structure_eta_expansion — VERBATIM def_eq/structural.rs:158.
    // Try structure-eta in BOTH orientations (either side may be the ctor-app).
    fn try_structure_eta_expansion(&self, a_whnf: &Expr, b_whnf: &Expr) -> bool {
        self.try_structure_eta_core(a_whnf, b_whnf) || self.try_structure_eta_core(b_whnf, a_whnf)
    }

    // ── try_structure_eta_core — VERBATIM def_eq/structural.rs:181 (Lean 4
    //    type_checker.cpp:786-811 try_eta_struct_core). `t` must be a SATURATED
    //    constructor application of a structure-like inductive; then `s` is
    //    compared FIELDWISE via projections: Proj i s =?= t.field_i. Composes
    //    infer_type (type of s) + whnf (expose the structure head) + reduce_proj
    //    (the Proj on s, via def_eq's whnf) + def_eq (on each field).
    fn try_structure_eta_core(&self, t: &Expr, s: &Expr) -> bool {
        // `t` must be a saturated constructor application of a structure.
        let head = t.get_app_fn();
        let head_name = match &head.kind {
            ExprKind::Const(head_name, _) => *head_name,
            _ => return false,
        };
        let ctor = match self.get_constructor(&head_name) { Some(c) => c, None => return false };
        if !self.is_structure_like(&ctor.inductive_name) {
            return false;
        }
        let num_params = ctor.num_params as usize;
        let num_fields = ctor.num_fields as usize;
        let args = t.get_app_args();
        if args.len() != num_params + num_fields {
            return false;
        }
        // `s`'s type must be the same structure. (infer_type + whnf pillars.)
        let s_type = match self.infer_type(s) { Ok(ty) => ty, Err(_) => return false };
        let s_type_whnf = self.whnf_impl(&s_type);
        let s_ind = match &s_type_whnf.get_app_fn().kind {
            ExprKind::Const(s_ind, _) => *s_ind,
            _ => return false,
        };
        if s_ind != ctor.inductive_name {
            return false;
        }
        // Fieldwise: Proj i s =?= t.field_i (def_eq pillar; reduce_proj on `s`).
        let mut i: usize = 0;
        while i < num_fields {
            let proj = Expr::proj(ctor.inductive_name, i as u32, s.clone());
            if !self.is_def_eq(&proj, &args[num_params + i]) {
                return false;
            }
            i += 1;
        }
        true
    }
}

// ───────────────────────── MODELED REGISTRY ──────────────────────────────
// Fixed Names for the demo structures/inductives + their field-type consts.
//   POINT     : a 2-field structure  (Point.mk : Nat -> Nat -> Point)  [structure-like]
//   PAIR       : a 1-field structure  (Pair.mk  : Nat -> Pair)          [structure-like]
//   BOOLLIKE  : a 2-CONSTRUCTOR inductive (NOT structure-like: fall-through)
//   LISTLIKE  : a single-ctor but RECURSIVE inductive (NOT structure-like)
//   VECLIKE   : a single-ctor but INDEXED inductive (num_indices>0; NOT structure-like)
//   NATTY      : Nat : Type 0 (the field domain type)
pub const POINT: u32 = 100;       // structure S  (2 fields)
pub const POINT_MK: u32 = 101;    // ctor Point.mk
pub const PAIR: u32 = 110;        // structure (1 field)
pub const PAIR_MK: u32 = 111;     // ctor Pair.mk
pub const BOOLLIKE: u32 = 120;    // 2-ctor inductive
pub const BOOLLIKE_T: u32 = 121;  // ctor .t
pub const BOOLLIKE_F: u32 = 122;  // ctor .f
pub const LISTLIKE: u32 = 130;    // single-ctor RECURSIVE inductive
pub const LISTLIKE_MK: u32 = 131; // ctor
pub const VECLIKE: u32 = 140;     // single-ctor INDEXED inductive
pub const VECLIKE_MK: u32 = 141;  // ctor
pub const NATTY: u32 = 200;       // Nat : Type 0

fn build_inductives() -> Vec<InductiveInfo> {
    vec![
        InductiveInfo { name: Name(POINT),    num_ctors: 1, num_indices: 0, is_recursive: false }, // structure-like
        InductiveInfo { name: Name(PAIR),     num_ctors: 1, num_indices: 0, is_recursive: false }, // structure-like
        InductiveInfo { name: Name(BOOLLIKE), num_ctors: 2, num_indices: 0, is_recursive: false }, // 2 ctors -> NOT
        InductiveInfo { name: Name(LISTLIKE), num_ctors: 1, num_indices: 0, is_recursive: true  }, // recursive -> NOT
        InductiveInfo { name: Name(VECLIKE),  num_ctors: 1, num_indices: 1, is_recursive: false }, // indexed -> NOT
    ]
}

fn build_ctors() -> Vec<ConstructorInfo> {
    vec![
        ConstructorInfo { ctor_name: Name(POINT_MK),    inductive_name: Name(POINT),    num_params: 0, num_fields: 2 },
        ConstructorInfo { ctor_name: Name(PAIR_MK),     inductive_name: Name(PAIR),     num_params: 0, num_fields: 1 },
        ConstructorInfo { ctor_name: Name(BOOLLIKE_T),  inductive_name: Name(BOOLLIKE), num_params: 0, num_fields: 0 },
        ConstructorInfo { ctor_name: Name(BOOLLIKE_F),  inductive_name: Name(BOOLLIKE), num_params: 0, num_fields: 0 },
        ConstructorInfo { ctor_name: Name(LISTLIKE_MK), inductive_name: Name(LISTLIKE), num_params: 0, num_fields: 1 },
        ConstructorInfo { ctor_name: Name(VECLIKE_MK),  inductive_name: Name(VECLIKE),  num_params: 0, num_fields: 1 },
    ]
}

// ctor num_params table (reduce_proj) — mirrors build_ctors' num_params.
fn build_ctor_np() -> Vec<(Name, u32)> {
    vec![
        (Name(POINT_MK), 0),
        (Name(PAIR_MK), 0),
        (Name(BOOLLIKE_T), 0),
        (Name(BOOLLIKE_F), 0),
        (Name(LISTLIKE_MK), 0),
        (Name(VECLIKE_MK), 0),
    ]
}

// Declared types (infer_type's Const rule). The neutral side `s` is an FVar-free
// Const `S_VAL : S` (an opaque value of the structure type), so infer_type(s)
// reads S off decl_types. Field values are Nat consts.
pub const POINT_VAL: u32 = 300;   // p : Point (opaque neutral of the structure)
pub const PAIR_VAL: u32 = 310;    // q : Pair
pub const BOOL_VAL: u32 = 320;    // b : BoolLike
pub const N0: u32 = 400;          // a : Nat
pub const N1: u32 = 401;          // b : Nat

fn build_decl_types() -> Vec<(Name, Expr)> {
    let type0 = Expr::sort(Level::succ(Level::Zero)); // Sort 1 = Type 0
    vec![
        (Name(NATTY), type0.clone()),                         // Nat : Type 0
        (Name(POINT), type0.clone()),                         // Point : Type 0
        (Name(PAIR), type0.clone()),                          // Pair  : Type 0
        (Name(BOOLLIKE), type0.clone()),                      // BoolLike : Type 0
        (Name(POINT_VAL), Expr::cnst(Name(POINT))),           // p : Point
        (Name(PAIR_VAL), Expr::cnst(Name(PAIR))),             // q : Pair
        (Name(BOOL_VAL), Expr::cnst(Name(BOOLLIKE))),         // b : BoolLike
        (Name(N0), Expr::cnst(Name(NATTY))),                  // a : Nat
        (Name(N1), Expr::cnst(Name(NATTY))),                  // b : Nat
    ]
}

// ───────────────────────── MONO ROOT (#[no_mangle]) ─────────────────────────
// The single monomorphic, closure-free root the emitter picks with
// `--mir-emit-closure struct_eta_root`. It builds the two comparison sides from
// scalar selectors and runs try_structure_eta_expansion, returning a plain i32:
// 1 = structure-eta proves them def-eq, 0 = it does not fire / fields differ.
//
// `a` (the ctor-app side) is `ctor_mk field0 field1?` for ctor `ctor_raw` with
// `nfields` applied field consts (field consts = f0_raw, f1_raw). `b` (the
// neutral side) is the opaque Const `neutral_raw`. This exercises:
//   - structure-eta TRUE: ctor-app of a structure vs a neutral s:S whose
//     projections def-eq the ctor args (the env has s unfold to the same ctor-app).
//   - fall-through: a 2-ctor / recursive / indexed inductive -> is_structure_like
//     false -> 0.
//   - field-mismatch: ctor args differ from s's actual field values -> 0.
#[no_mangle]
pub extern "C" fn struct_eta_root(
    ctor_raw: u32,
    f0_raw: u32,
    f1_raw: u32,
    nfields: u32,
    neutral_raw: u32,
    neutral_unfolds_to_ctor: u32, // 1 => env maps neutral -> the SAME ctor-app (so proj reduces)
) -> i32 {
    // Build side `a` = ctor_mk applied to nfields field consts.
    let ctor = Name(ctor_raw);
    let mut a = Expr::cnst(ctor);
    if nfields >= 1 { a = Expr::app(a, Expr::cnst(Name(f0_raw))); }
    if nfields >= 2 { a = Expr::app(a, Expr::cnst(Name(f1_raw))); }

    // Build the modeled Environment. If `neutral_unfolds_to_ctor`, the neutral
    // Const delta-unfolds to a FIXED CANONICAL ctor-app of its structure (NOT
    // tied to `a`), so reduce_proj on `Proj i s` yields that canonical form's
    // fields. Structure-eta then succeeds iff `a`'s ctor args def-eq the
    // canonical fields. Otherwise the neutral is opaque (`None` unfold): its Proj
    // stays neutral -> def_eq against the ctor arg fails structurally -> 0.
    //
    // Canonical unfoldings (independent of the ctor-app args passed in):
    //   POINT_VAL -> Point.mk N0 N1   (fields a, b)
    //   PAIR_VAL  -> Pair.mk  N0       (field  a)
    // A ctor-app matching this canonical form is structure-eta def-eq; a ctor-app
    // that differs (e.g. Point.mk N0 N0) is field-mismatch FALSE.
    //
    // The env is a single-element `vec![...]` literal (so the frontend lowers the
    // backing buffer inline — no Vec::push leaf; the Option carries the unfold-or-
    // opaque choice). A `None` unfold makes the neutral opaque.
    let canon: Expr = if neutral_raw == POINT_VAL {
        Expr::app(Expr::app(Expr::cnst(Name(POINT_MK)), Expr::cnst(Name(N0))), Expr::cnst(Name(N1)))
    } else if neutral_raw == PAIR_VAL {
        Expr::app(Expr::cnst(Name(PAIR_MK)), Expr::cnst(Name(N0)))
    } else {
        // default canonical for structures without a fixed form declared above.
        a.clone()
    };
    let unfold: Option<Expr> = if neutral_unfolds_to_ctor == 1 { Some(canon) } else { None };
    let env: Vec<(Name, Option<Expr>)> = vec![(Name(neutral_raw), unfold)];
    let ctor_np = build_ctor_np();
    let decl_types = build_decl_types();
    let inductives = build_inductives();
    let ctors = build_ctors();
    let v = CertVerifier {
        env: &env,
        ctor_np: &ctor_np,
        decl_types: &decl_types,
        inductives: &inductives,
        ctors: &ctors,
    };

    // side `b` = the neutral opaque value of the structure type.
    let b = Expr::cnst(Name(neutral_raw));

    // whnf both sides first (the def_eq_structural entry hands whnf'd terms to
    // try_structure_eta_expansion). Here `a` is already whnf (a ctor-app whose
    // head const has no unfold); `b` whnf's to itself unless it unfolds — but
    // for the eta test we DELIBERATELY compare the ctor-app against the NEUTRAL
    // form (not its unfolding), exactly as the kernel does: eta bridges the
    // ctor-app and the neutral s WITHOUT unfolding s. So use `b` as-is.
    let a_whnf = a.clone(); // ctor-app, already whnf
    let b_whnf = b.clone(); // neutral const (infer_type reads its declared type)

    if v.try_structure_eta_expansion(&a_whnf, &b_whnf) { 1 } else { 0 }
}

fn main() {
    // Standalone re-emit validate harness. Exercises the structure-eta gate's
    // TRUE / fall-through / field-mismatch branches end to end through the root.

    // (1) Point.mk a b  vs  p:Point (unfolds to Point.mk a b) -> structure-eta TRUE.
    let t_point = struct_eta_root(POINT_MK, N0, N1, 2, POINT_VAL, 1);
    // (2) Pair.mk a      vs  q:Pair (unfolds to Pair.mk a)     -> structure-eta TRUE.
    let t_pair = struct_eta_root(PAIR_MK, N0, N1, 1, PAIR_VAL, 1);
    // (3) BoolLike.t     vs  b:BoolLike -> 2-ctor -> NOT structure-like -> 0.
    let f_bool = struct_eta_root(BOOLLIKE_T, N0, N1, 0, BOOL_VAL, 1);
    // (4) Point.mk a b   vs  p:Point (OPAQUE, no unfold) -> projections stay neutral,
    //     def_eq(Proj0 p, a) fails -> structure-eta 0 (field-mismatch / no reduction).
    let f_opaque = struct_eta_root(POINT_MK, N0, N1, 2, POINT_VAL, 0);
    // (5) Point.mk a a   vs  p (unfolds to Point.mk a b) -> field 1 differs (a vs b) -> 0.
    let f_mismatch = struct_eta_root(POINT_MK, N0, N0, 2, POINT_VAL, 1);

    println!(
        "t_point={t_point} t_pair={t_pair} f_bool={f_bool} f_opaque={f_opaque} f_mismatch={f_mismatch}"
    );
    let ok = t_point == 1 && t_pair == 1 && f_bool == 0 && f_opaque == 0 && f_mismatch == 0;
    std::process::exit((!ok) as i32);
}
