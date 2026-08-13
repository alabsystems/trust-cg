// clean_elim_zero_slice — self-contained slice of the SOUNDNESS-CRITICAL
// LARGE-ELIMINATION gate `elim_only_at_universe_zero`
// (clean/crates/clean-kernel/src/env/elim_analysis.rs:38), the rule that decides
// whether a Prop-valued inductive's recursor may eliminate into a LARGER universe
// (Type u, u>0). A bug here = large elimination from a non-subsingleton Prop =
// extracting computational content from a proof = a DIRECT proof of False
// (Lean 4 kernel inductive.cpp:479 parity).
//
// This composes the VERIFIED kernel pillars over the real clean-kernel Expr:
//   - WHNF (cert/reduction.rs whnf_impl)        — VERIFIED, reused
//   - DEF_EQ (cert/expr_eq.rs def_eq_impl)      — VERIFIED, reused
//   - INFER_TYPE (tc/infer.rs infer_type)       — VERIFIED, reused
// plus the NEW gate machinery on top:
//   - infer_sort                       (tc/infer.rs:735 infer_sort / :765 infer_sort_inner)
//   - ctor_field_sort_levels           (tc/infer.rs:808) — per-field universe levels
//   - get_return_type                  (inductive/mod.rs:650) — Pi-telescope return type
//   - elim_only_at_universe_zero       (env/elim_analysis.rs:38) — THE GATE
//
// Crate name is load-bearing: it appears in the mangled symbols of the extern
// leaves the JIT binds, so it MUST stay `clean_elim_zero_slice`.
#![allow(dead_code)]
#![allow(clippy::all)]
#![allow(unused_variables)]

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
    // Public mirror of the real `Level::is_zero()` (level/mod.rs) the gate calls on
    // the inductive result sort and each field sort. Over this slice's Zero/Succ/Param
    // fragment, `is_zero` ⇔ the level is structurally `Zero` (Prop / Sort 0).
    pub fn is_zero_pub(l: &Level) -> bool { matches!(l, Level::Zero) }
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
    // Declared-type table — the FAITHFUL model of the real Environment, which
    // stores each constant's declared `type_` (tc/infer.rs:353 `env.get_const`).
    // `const_type` consults this FIRST (matching the real Const typing rule's
    // declared-type lookup), falling back to infer-from-unfold only when a const
    // has no declared type. This is what lets a Prop field's domain Const `P`
    // carry type `Sort 0` (so infer_sort(P)=0) and a Type field's domain Const
    // `Nat` carry type `Sort 1` (so infer_sort(Nat)=1) — exactly as in the kernel.
    decl_types: &'env [(Name, Expr)],
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
        // FAITHFUL: declared-type lookup first (real `env.get_const(name).type_`).
        let mut i: usize = 0;
        let n = self.decl_types.len();
        while i < n {
            let entry = &self.decl_types[i];
            if entry.0 == *name { return Some(entry.1.clone()); }
            i += 1;
        }
        // Fallback: infer-from-unfold for defs that carry only a value.
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

    // ══════════════════════════════════════════════════════════════════════
    // NEW GATE MACHINERY (large-elimination universe analysis)
    // ══════════════════════════════════════════════════════════════════════

    // ── infer_sort — VERBATIM tc/infer.rs:735 infer_sort / :765 infer_sort_inner.
    //
    // The real `infer_sort(e)` sets infer_only=false, then runs
    //   infer_sort_inner(e, 0): ty = infer_type(e); whnf(ty); match:
    //     Sort(l) => l ; SProp => 0 ; Pi(bd,arg,body) => imax(infer_sort(arg),
    //       infer_sort(open_bvar(body)))  (depth-capped) ; _ => ExpectedSort.
    //
    // MODELING BOUNDARY (documented): the real infer machinery threads an FVar
    // local-decl context (ctx_push / open_bvar / ctx_pop). This slice reuses the
    // VERIFIED BVar-indexed infer_type_core (ctx: Vec<Expr> of binder types) — the
    // SAME modeling boundary the verified infer rung already uses. The Pi sub-case
    // therefore pushes the domain type onto `ctx` and recurses on the body
    // DIRECTLY (no open_bvar; the body's BVar(0) resolves via the pushed type),
    // which is the de-Bruijn dual of `ctx_push + open_bvar`. SProp is not in this
    // slice's ExprKind (it lowers to the `_ => ExpectedSort` arm exactly as the
    // real code would never reach it on ordinary inductives). The depth cap
    // (INFER_SORT_MAX_DEPTH=64) is preserved as a hard SortDepthExceeded error —
    // the soundness-load-bearing guard that prevents a deep Pi from being
    // mis-reported as Prop (a Girard-paradox enabler, tc/infer.rs:776-784).
    const INFER_SORT_MAX_DEPTH: u32 = 64;

    fn infer_sort(&self, e: &Expr, ctx: &mut Vec<Expr>) -> Result<Level, TypeError> {
        self.infer_sort_inner(e, ctx, 0)
    }

    fn infer_sort_inner(&self, e: &Expr, ctx: &mut Vec<Expr>, depth: u32) -> Result<Level, TypeError> {
        let ty = self.infer_type_core(e, ctx)?;
        let ty_whnf = self.whnf_impl(&ty);
        match &ty_whnf.kind {
            ExprKind::Sort(l) => Ok(l.clone()),
            ExprKind::Pi(_bd, arg_type, body) => {
                if depth >= Self::INFER_SORT_MAX_DEPTH {
                    return Err(TypeError::SortDepthExceeded { depth });
                }
                let arg_level = self.infer_sort_inner(arg_type, ctx, depth + 1)?;
                ctx.push(arg_type.as_ref().clone());
                let body_level_result = self.infer_sort_inner(body, ctx, depth + 1);
                ctx.pop();
                let body_level = body_level_result?;
                Ok(Level::imax(arg_level, body_level))
            }
            _ => Err(TypeError::ExpectedSort { ty: Arc::new(ty) }),
        }
    }

    // ── ctor_field_sort_levels — VERBATIM tc/infer.rs:808.
    //
    // Walk the Pi binders of `ctor_type`; for each binder at depth >= num_params
    // (i.e. a constructor FIELD, not a shared parameter), infer the SORT of the
    // field's domain type (the universe the field's type inhabits) and record it.
    // Push the domain type as a local decl, descend into the body, repeat. On any
    // infer error, propagate it (the real code does `break Err(e)` with ctx_pop
    // cleanup; here `?` short-circuits and the explicit pop-loop at the end is the
    // BVar-ctx dual of the real per-binder ctx_pop cleanup).
    fn ctor_field_sort_levels(
        &self,
        ctor_type: &Expr,
        num_params: u32,
    ) -> Result<Vec<Level>, TypeError> {
        let mut current = ctor_type.clone();
        let mut depth = 0u32;
        let mut field_sorts: Vec<Level> = Vec::new();
        let mut ctx: Vec<Expr> = Vec::new();

        let result = loop {
            match current.kind() {
                ExprKind::Pi(_bd, domain, body) => {
                    if depth >= num_params {
                        match self.infer_sort(domain, &mut ctx) {
                            Ok(sort) => field_sorts.push(sort),
                            Err(e) => break Err(e),
                        }
                    }
                    // ctx_push(domain) + open_bvar(body) ≡ push domain type, descend
                    // into body directly (BVar-ctx form — the verified infer boundary).
                    ctx.push(domain.as_ref().clone());
                    current = body.as_ref().clone();
                    depth += 1;
                }
                _ => break Ok(field_sorts),
            }
        };

        // BVar-ctx dual of the real per-binder ctx_pop cleanup loop.
        let mut k = 0u32;
        while k < depth {
            ctx.pop();
            k += 1;
        }
        result
    }
}

// Slice TypeError: carries the offending Expr/Name directly (no format!/String).
// VERBATIM the infer slice's TypeError + the SortDepthExceeded variant the
// infer_sort depth cap raises (tc/infer.rs:784 — the soundness guard).
#[derive(Clone, Debug)]
pub enum TypeError {
    UnboundVariable(u32),
    UnknownConst(Name),
    TypeMismatch { expected: Arc<Expr>, inferred: Arc<Expr> },
    NotAPi { ty: Arc<Expr> },
    ExpectedSort { ty: Arc<Expr> },
    SortDepthExceeded { depth: u32 },
    Unsupported,
}

// ── get_return_type — VERBATIM inductive/mod.rs:650.
// Walk past all leading Pi binders to the constructor/inductive RETURN type.
fn get_return_type(expr: &Expr) -> &Expr {
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = &current.kind {
        current = body;
    }
    current
}

// Constructor — VERBATIM inductive/mod.rs:33 (the relevant field: `type_`). The
// real struct also carries `name: Name`; only `type_` is read by the gate.
#[derive(Clone, Debug)]
pub struct Constructor {
    pub name: Name,
    pub type_: Expr,
}

// ═══════════════════════════ THE GATE ═══════════════════════════════════════
// elim_only_at_universe_zero — VERBATIM env/elim_analysis.rs:38.
//
// Returns TRUE iff the (Prop-valued) inductive's recursor may eliminate ONLY into
// Prop (Sort 0) — i.e. large elimination is FORBIDDEN. Returning FALSE here when
// it should be TRUE = granting large elimination to a non-subsingleton Prop =
// UNSOUND (a proof of False). `allows_large_elim` = NOT this.
//
// Rules (Lean 4 inductive.cpp:479 parity):
//   - result sort not Prop (Sort u, u>0)  → false (Type-valued: always large-elim)
//   - mutual Prop predicates (num_types>1) → true  (#3238, inductive.cpp:486-489)
//   - >1 constructor (e.g. Or)             → true  (Prop-only)
//   - 0 constructors (e.g. False)          → false (large-elim allowed)
//   - exactly 1 constructor: each non-param FIELD must be either (1) in Prop
//     (its sort is zero) OR (2) appear DIRECTLY as a result-type index argument
//     (a bare BVar). Any field failing both → true (Prop-only, e.g. Nonempty).
pub fn elim_only_at_universe_zero(
    verifier: &CertVerifier,
    ind_type_expr: &Expr,
    constructors: &[Constructor],
    num_params: u32,
    num_types: usize,
) -> bool {
    // Check if inductive result sort is Prop (Sort 0).
    let result_sort = get_return_type(ind_type_expr);
    let is_prop = matches!(&result_sort.kind, ExprKind::Sort(level) if Level::is_zero_pub(level));
    if !is_prop {
        return false; // Not in Prop → large elimination allowed
    }

    // Mutual Prop predicates (num_types > 1) → Prop-only (#3238).
    if num_types > 1 {
        return true;
    }

    if constructors.len() > 1 {
        return true; // Multiple constructors → Prop-only
    }
    if constructors.is_empty() {
        return false; // Empty type (e.g. False) → large elimination
    }

    // Exactly one constructor. Check non-param fields using the verified infer.
    let ctor = &constructors[0];
    let field_sorts = match verifier.ctor_field_sort_levels(&ctor.type_, num_params) {
        Ok(sorts) => sorts,
        Err(_) => {
            // Type checking failed — conservatively restrict to Prop elimination
            // (SOUND: too-restrictive, never too-liberal). elim_analysis.rs:75-81.
            return true;
        }
    };

    // Find non-Prop field positions (0-indexed from first non-param field). The real
    // kernel collects these as u32; modeled as usize here (a representation choice —
    // the position is a non-negative index, used only for membership arithmetic).
    let mut non_prop_fields: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    let n = field_sorts.len();
    while i < n {
        if !Level::is_zero_pub(&field_sorts[i]) {
            non_prop_fields.push(i);
        }
        i += 1;
    }

    if non_prop_fields.is_empty() {
        return false; // All non-param fields in Prop → large elimination allowed
    }

    // Condition 2: non-Prop fields must appear DIRECTLY in return-type indices.
    // Navigate past all Pi binders to the return type.
    let mut cur = &ctor.type_;
    while let ExprKind::Pi(_, _, body) = &cur.kind {
        cur = body;
    }

    // Collect return-type arguments (App spine, innermost-first then reversed).
    let mut return_args: Vec<&Expr> = Vec::new();
    let mut ret = cur;
    while let ExprKind::App(func, arg) = &ret.kind {
        return_args.push(arg.as_ref());
        ret = func;
    }
    return_args.reverse();
    // index_args = return_args after the first num_params (the indices).
    let mut index_args: Vec<&Expr> = Vec::new();
    let mut j: usize = 0;
    let m = return_args.len();
    while j < m {
        if j >= num_params as usize {
            index_args.push(return_args[j]);
        }
        j += 1;
    }

    let total_fields = field_sorts.len();
    let mut fp: usize = 0;
    let nf = non_prop_fields.len();
    while fp < nf {
        let field_pos = non_prop_fields[fp];
        let bvar_idx = (total_fields - 1 - field_pos) as u32;
        // The non-Prop field must appear as a result-type argument DIRECTLY (a
        // bare BVar), not merely occur inside one (Int.NonNeg kernel-parity fix,
        // elim_analysis.rs:116-127).
        let mut found = false;
        let mut ai: usize = 0;
        let an = index_args.len();
        while ai < an {
            if let ExprKind::BVar(idx) = &index_args[ai].kind {
                if *idx == bvar_idx {
                    found = true;
                    break;
                }
            }
            ai += 1;
        }
        if !found {
            return true; // Field not a direct index arg → Prop-only elimination
        }
        fp += 1;
    }

    false // All non-Prop fields appear directly in indices → large elimination
}

// ───────────────────────── DECLARED-TYPE MODEL ──────────────────────────────
// Fixed const Names whose DECLARED TYPES the gate's infer pillar resolves. These
// are the field-type heads a constructor's Pi-domains reference. infer_sort(domain)
// reads the universe each inhabits straight off the declared type:
//   PROPP : Sort 0          ⇒ a Prop field   (infer_sort = 0  → subsingleton-ok)
//   NATTY : Sort 1          ⇒ a Type field   (infer_sort = 1  → NON-Prop)
//   FAMILY : Nat → Prop     ⇒ the indexed inductive head (for index-arg cases)
pub const PROPP: u32 = 800;   // a proposition P : Prop
pub const NATTY: u32 = 801;   // Nat : Type 0
pub const FAMILY: u32 = 802;  // the inductive family head I : Nat -> Prop

// build_decl_types — the modeled Environment's declared-type table.
fn build_decl_types() -> Vec<(Name, Expr)> {
    let bd = BinderData { info: 0, mult: 0 };
    let prop = Expr::sort0();                         // Sort 0
    let type0 = Expr::sort(Level::succ(Level::Zero)); // Sort 1
    vec![
        (Name(PROPP), prop.clone()),                  // P : Prop  (= Sort 0)
        (Name(NATTY), type0.clone()),                 // Nat : Type 0 (= Sort 1)
        // FAMILY : Nat -> Prop  (an indexed Prop family head)
        (Name(FAMILY), Expr::pi(bd, Expr::cnst(Name(NATTY)), prop)),
    ]
}

// ───────────────────────── MONO ROOT (#[no_mangle]) ─────────────────────────
// The single monomorphic, closure-free root the emitter picks with
// `--mir-emit-closure elim_only_root`. Forwards to elim_only_at_universe_zero over
// concrete args, returning a plain i32: 1 = Prop-ONLY (large elim FORBIDDEN),
// 0 = large elim ALLOWED. (`elim_only`, NOT `allows_large_elim`: 1 = "the gate
// restricts".) `ctor_count`: 0 = empty (False-like), 1 = one ctor, ≥2 = two ctors.
#[no_mangle]
pub extern "C" fn elim_only_root(
    ind_type: &Expr,
    ctor_type: &Expr,
    ctor_count: u32,
    num_params: u32,
    num_types: u32,
) -> i32 {
    let env: Vec<(Name, Option<Expr>)> = Vec::new();
    let ctors_tbl: Vec<(Name, u32)> = Vec::new();
    let decl_types = build_decl_types();
    let verifier = CertVerifier { env: &env, ctors: &ctors_tbl, decl_types: &decl_types };

    // Build the constructor list heap-backed (a Vec, like the env/ctor tables) so
    // the boundary stays a fat-pointer slice; push 0/1/2 ctors per ctor_count.
    let mut ctors: Vec<Constructor> = Vec::new();
    if ctor_count >= 1 {
        ctors.push(Constructor { name: Name(900), type_: ctor_type.clone() });
    }
    if ctor_count >= 2 {
        ctors.push(Constructor { name: Name(901), type_: ctor_type.clone() });
    }
    let only_zero = elim_only_at_universe_zero(
        &verifier,
        ind_type,
        &ctors,
        num_params,
        num_types as usize,
    );
    if only_zero { 1 } else { 0 }
}

fn main() {
    // Standalone re-emit validate harness: exercise the gate's structural +
    // field-sort branches end to end (all routed through elim_only_root).
    let bd = BinderData { info: 0, mult: 0 };
    let prop = Expr::sort0();                          // Sort 0 = Prop
    let type0 = Expr::sort(Level::succ(Level::Zero));  // Sort 1 = Type 0
    let pi = |t: Expr, b: Expr| Expr::pi(bd, t, b);
    let natty = || Expr::cnst(Name(NATTY));            // a Type-valued field domain
    let propp = || Expr::cnst(Name(PROPP));            // a Prop-valued field domain
    let ind_prop = prop.clone();                       // a Prop-valued inductive head

    // (0) False-like: 0 ctors, Prop  → large elim allowed → 0.
    let false_like = elim_only_root(&ind_prop, &prop, 0, 0, 1);
    // (1) Or-like: 2 ctors, Prop     → Prop-only → 1.
    let or_like = elim_only_root(&ind_prop, &prop, 2, 0, 1);
    // (2) Mutual Prop: num_types=2   → Prop-only → 1.
    let mutual = elim_only_root(&ind_prop, &prop, 1, 0, 2);
    // (3) Type-valued inductive head → large elim always → 0.
    let type_ind = elim_only_root(&type0, &type0, 1, 0, 1);
    // (4) And-like Prop: 1 ctor, two PROP fields  (mk : P -> P -> And) → all fields
    //     in Prop → large elim allowed → 0.  ctor type: Pi(P, Pi(P, ind_prop)).
    let and_like = elim_only_root(&ind_prop, &pi(propp(), pi(propp(), ind_prop.clone())), 1, 0, 1);
    // (5) Nonempty-like Prop: 1 ctor, ONE NON-PROP field, NOT an index
    //     (mk : Nat -> Nonempty) → Prop-only → 1.  THE UNSOUND case the gate STOPS:
    //     granting large elim here lets you project the Nat out of a proof.
    let nonempty = elim_only_root(&ind_prop, &pi(natty(), ind_prop.clone()), 1, 0, 1);

    println!(
        "false_like={false_like} or_like={or_like} mutual={mutual} type_ind={type_ind} and_like={and_like} nonempty={nonempty}"
    );
    let ok = false_like == 0
        && or_like == 1
        && mutual == 1
        && type_ind == 0
        && and_like == 0
        && nonempty == 1;
    std::process::exit((!ok) as i32);
}
