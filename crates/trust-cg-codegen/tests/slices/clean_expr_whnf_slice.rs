// Real-kernel WHNF reduction slice — the production `CertVerifier::whnf_impl`/
// `whnf_inner` (clean-kernel/src/cert/reduction.rs:34) lowered over the REAL `Expr`.
//
// This EXTENDS the verified instantiate slice (clean_expr_instantiate_slice.rs):
// the same VERBATIM Expr/ExprMeta/from_kind/compute_meta/mix_hash construction core,
// the verified READ (loose_bvar_range guard), WRITE (lift_at), and BETA
// (instantiate / instantiate_at). On top of those verified primitives it composes
// the kernel's reduction engine:
//
//   whnf_inner(e):
//     App(f,a)  -> whnf f; if Lam => BETA: whnf(body.instantiate(a))     [instantiate VERIFIED]
//                          else  => rebuild App via from_kind            [from_kind VERIFIED]
//                                   try_iota (DEFERRED -> None)
//                                   try_quot (DEFERRED -> None)
//     Let(..)   -> ZETA: whnf(body.instantiate(val))                     [instantiate VERIFIED]
//     Const(n)  -> DELTA: env.unfold(n).map_or(clone, |v| whnf(v))       [env MODELED slice-scan]
//     Proj(s,i) -> reduce_proj: whnf inner; get_app_fn; if Const ctor,
//                  get_constructor (MODELED), field-extract, whnf field;
//                  else rebuild Proj via from_kind                       [from_kind VERIFIED]
//     MData(_,inner) -> strip: whnf(inner)
//     _         -> e.clone()  (Sort/Lit/BVar/FVar leaves)
//
// MODELED / DEFERRED (reported honestly):
//   * env: the real `Environment` is a hashbrown Definition/constructor map. Here it
//     is a small in-module slice-scan: `unfold(name)` linear-scans `env: &[(Name,
//     Option<Expr>)]`, `get_constructor(name)` linear-scans `ctors: &[(Name, u32)]`
//     (num_params). SAME boundary the micro-checker whnf-core used (hashbrown deferred).
//   * try_iota_reduction / try_quot_reduction: DEFERRED, modeled as `-> None` (so the
//     App-stuck rebuild fires) — exactly as the micro-checker verified whnf-core
//     before adding the recursor. The recursor's verified separately (reduce_recursor
//     slice / native_arith iota rungs).
//   * MData metadata payload: modeled as a `u32` tag (the strip arm ignores it; the
//     real `MDataMap` hashbrown is out of scope). compute_meta uses the VERBATIM
//     `mk_wrapper_meta`.
//   * stack_safe: the production `whnf_impl` wraps `whnf_inner` in `stack_safe(||..)`
//     (an explicit-stack trampoline for deep terms). Here `whnf_impl` calls
//     `whnf_inner` directly (the trampoline is a recursion-depth concern, not a
//     semantic one; on test-sized terms it is a pure pass-through). REPORTED.

#![allow(dead_code)]

use std::hash::Hash;
use std::hash::Hasher;
use std::sync::Arc;

// ── Leaf payload models. ──

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Name(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct FVarId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Level {
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
    // ── Level def-eq (model of `Level::is_def_eq` for this slice's Level). ──
    //
    // The production `Level::is_def_eq` normalizes both sides (full universe
    // arithmetic over Max/IMax/Param + offsets) before comparing. The slice's
    // Level is the small {Zero, Succ, Param} core, so this is the structural
    // congruence: Zero==Zero, Succ-congruence, Param name-eq. DEFERRED: the
    // full universe-unification normalization (Max/IMax with offset folding,
    // metavariable assignment) — it needs machinery not in this Level model.
    fn is_def_eq(l1: &Level, l2: &Level) -> bool {
        match (l1, l2) {
            (Level::Zero, Level::Zero) => true,
            (Level::Succ(a), Level::Succ(b)) => Level::is_def_eq(a, b),
            (Level::Param(a), Level::Param(b)) => a.0 == b.0,
            _ => false,
        }
    }
}

type LevelVec = Vec<Level>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Literal {
    Nat(u64),
    Str(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct BinderData {
    pub info: u8,
    pub mult: u8,
}

// ── mix_hash (MurmurHash2-64A mixing step) — VERBATIM. ──
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

// ── KaniHasher (clean's cfg(kani) FxHash-style pure-arithmetic hasher) — VERBATIM. ──
struct KaniHasher {
    state: u64,
}
impl KaniHasher {
    fn new() -> Self {
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
fn hash_name(value: &Name) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}
#[inline]
fn hash_lit(value: &Literal) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}
#[inline]
fn hash_level(value: &Level) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[inline]
fn level_has_mvar(_l: &Level) -> bool {
    false
}

// ── ExprMeta (bit-packed u64 @ offset 32 of Expr) — VERBATIM. ──
#[derive(Clone, Copy, Debug)]
struct ExprMeta(u64);

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
            mix_hash(ty.hash() as u64, mix_hash(val.hash() as u64, body.hash() as u64)),
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
    // VERBATIM mk_wrapper_meta (MData metadata wrapper — clean expr/meta.rs:227).
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

#[derive(Clone, Debug)]
enum ExprKind {
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
    // MData metadata modeled as a u32 tag (real `MDataMap` hashbrown deferred). The
    // whnf strip arm ignores the payload; compute_meta uses VERBATIM mk_wrapper_meta.
    MData(u32, Arc<Expr>),
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
                let name_hash = hash_name(name);
                ExprMeta::pack(mix_hash(5, name_hash) as u32, 0, 0, false, false, false, false)
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
        }
    }
}

#[derive(Clone, Debug)]
struct Expr {
    kind: ExprKind,
    meta: ExprMeta,
}

impl Expr {
    fn from_kind(kind: ExprKind) -> Self {
        let meta = kind.compute_meta();
        Expr { kind, meta }
    }
    fn meta(&self) -> ExprMeta {
        self.meta
    }
    fn kind(&self) -> &ExprKind {
        &self.kind
    }
    fn loose_bvar_range(&self) -> u32 {
        self.meta.loose_bvar_range()
    }
    fn bvar(idx: u32) -> Self {
        Expr::from_kind(ExprKind::BVar(idx))
    }
    fn app(func: Expr, arg: Expr) -> Self {
        Expr::from_kind(ExprKind::App(Arc::new(func), Arc::new(arg)))
    }
    fn lam(bd: BinderData, ty: Expr, body: Expr) -> Self {
        Expr::from_kind(ExprKind::Lam(bd, Arc::new(ty), Arc::new(body)))
    }
    fn pi(bd: BinderData, ty: Expr, body: Expr) -> Self {
        Expr::from_kind(ExprKind::Pi(bd, Arc::new(ty), Arc::new(body)))
    }
    fn lett(name: Name, ty: Expr, val: Expr, body: Expr, nondep: bool) -> Self {
        Expr::from_kind(ExprKind::Let(
            name,
            Arc::new(ty),
            Arc::new(val),
            Arc::new(body),
            nondep,
        ))
    }
    fn proj(name: Name, idx: u32, e: Expr) -> Self {
        Expr::from_kind(ExprKind::Proj(name, idx, Arc::new(e)))
    }

    // ── VERBATIM lift_at (the verified de-Bruijn lift; WRITE primitive). ──
    fn lift_at(&self, start: u32, amount: u32) -> Expr {
        if amount == 0 {
            return self.clone();
        }
        if start >= self.loose_bvar_range() {
            return self.clone();
        }
        match &self.kind {
            ExprKind::BVar(idx) => {
                if *idx >= start {
                    Expr::bvar(idx.saturating_add(amount))
                } else {
                    self.clone()
                }
            }
            ExprKind::App(f, a) => Expr::app(f.lift_at(start, amount), a.lift_at(start, amount)),
            ExprKind::Lam(bd, ty, body) => Expr::lam(
                *bd,
                ty.lift_at(start, amount),
                body.lift_at(start.saturating_add(1), amount),
            ),
            ExprKind::Pi(bd, ty, body) => Expr::pi(
                *bd,
                ty.lift_at(start, amount),
                body.lift_at(start.saturating_add(1), amount),
            ),
            _ => self.clone(),
        }
    }

    // The real `Expr` exposes the lift under the name `lift_from`; eta-expansion
    // calls `b.lift_from(0, 1)`. Same verified body as `lift_at`.
    fn lift_from(&self, start: u32, amount: u32) -> Expr {
        self.lift_at(start, amount)
    }

    // ── VERBATIM instantiate / instantiate_at — THE BETA SUBSTITUTION PRIMITIVE. ──
    fn instantiate(&self, val: &Expr) -> Expr {
        self.instantiate_at(val, 0)
    }

    fn instantiate_at(&self, val: &Expr, depth: u32) -> Expr {
        if depth >= self.loose_bvar_range() {
            return self.clone();
        }
        match &self.kind {
            ExprKind::BVar(idx) => {
                if *idx == depth {
                    val.lift_at(0, depth)
                } else if *idx > depth {
                    Expr::bvar(idx.saturating_sub(1))
                } else {
                    self.clone()
                }
            }
            ExprKind::App(f, a) => {
                Expr::app(f.instantiate_at(val, depth), a.instantiate_at(val, depth))
            }
            ExprKind::Lam(bd, ty, body) => Expr::lam(
                *bd,
                ty.instantiate_at(val, depth),
                body.instantiate_at(val, depth.saturating_add(1)),
            ),
            ExprKind::Pi(bd, ty, body) => Expr::pi(
                *bd,
                ty.instantiate_at(val, depth),
                body.instantiate_at(val, depth.saturating_add(1)),
            ),
            ExprKind::Let(name, ty, val_e, body, nondep) => Expr::lett(
                *name,
                ty.instantiate_at(val, depth),
                val_e.instantiate_at(val, depth),
                body.instantiate_at(val, depth.saturating_add(1)),
                *nondep,
            ),
            ExprKind::Proj(name, idx, e) => {
                Expr::proj(*name, *idx, e.instantiate_at(val, depth))
            }
            _ => self.clone(),
        }
    }

    // ── App-spine walks (pure Expr; used by reduce_proj). VERBATIM semantics. ──
    //
    // get_app_fn: walk left through App to the head. Returns a CLONE here (the real
    // one returns `&Expr`; in a closure-emit driver returning by-value composes more
    // simply and is structurally identical — the head is read-only).
    fn get_app_fn(&self) -> Expr {
        let mut current = self.clone();
        loop {
            // pull the App head out without holding a borrow across the reassign.
            let next = match &current.kind {
                ExprKind::App(f, _) => f.as_ref().clone(),
                _ => return current,
            };
            current = next;
        }
    }

    // get_app_args: collect args in application (innermost-first) order, then reverse
    // to source order — the real `get_app_args` semantics (constructors.rs:273).
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

// ── Modeled environment (slice-scan; the real `Environment` hashbrown is DEFERRED). ──
//
// `env`: (Const name, optional unfolding body). `unfold_with_transparency` returns
// `Some(body)` for a modeled reducible Const, `None` otherwise — the DELTA boundary.
// `ctors`: (constructor name, num_params). `get_constructor` returns the num_params
// for reduce_proj's field offset; `None` if the head is not a modeled constructor.
struct CertVerifier<'env> {
    env: &'env [(Name, Option<Expr>)],
    ctors: &'env [(Name, u32)],
}

impl<'env> CertVerifier<'env> {
    // env.unfold_with_transparency(name, _, Default) — modeled as a linear scan.
    fn unfold_const(&self, name: &Name) -> Option<Expr> {
        let mut i: usize = 0;
        let n = self.env.len();
        while i < n {
            let entry = &self.env[i];
            if entry.0 == *name {
                return entry.1.clone();
            }
            i += 1;
        }
        None
    }

    // env.get_constructor(name) -> Option<num_params> — modeled as a linear scan.
    fn get_constructor_num_params(&self, name: &Name) -> Option<u32> {
        let mut i: usize = 0;
        let n = self.ctors.len();
        while i < n {
            let entry = &self.ctors[i];
            if entry.0 == *name {
                return Some(entry.1);
            }
            i += 1;
        }
        None
    }

    // try_iota_reduction / try_quot_reduction — DEFERRED: modeled as `-> None`, so the
    // App-stuck rebuild fires (exactly as the micro-checker verified whnf-core first).
    fn try_iota_reduction(&self, _e: &Expr) -> Option<Expr> {
        None
    }
    fn try_quot_reduction(&self, _e: &Expr) -> Option<Expr> {
        None
    }

    // ── whnf_impl / whnf_inner — VERBATIM clean reduction.rs:34 control flow. ──
    //
    // Production `whnf_impl` wraps `whnf_inner` in `stack_safe(|| ..)` (a trampoline
    // for deep terms). Here it calls `whnf_inner` directly (the trampoline is a
    // recursion-depth concern, semantically a pass-through on test terms). REPORTED.
    fn whnf_impl(&self, e: &Expr) -> Expr {
        self.whnf_inner(e)
    }

    fn whnf_inner(&self, e: &Expr) -> Expr {
        match &e.kind {
            ExprKind::App(f, a) => {
                let f_whnf = self.whnf_impl(f);
                match &f_whnf.kind {
                    // BETA: (λ x. body) arg → body[arg/x]
                    ExprKind::Lam(_, _, body) => {
                        let reduced = body.instantiate(a);
                        self.whnf_impl(&reduced)
                    }
                    _ => {
                        let app =
                            Expr::from_kind(ExprKind::App(Arc::new(f_whnf), a.clone()));
                        // IOTA (recursor) — DEFERRED (None).
                        if let Some(reduced) = self.try_iota_reduction(&app) {
                            return self.whnf_impl(&reduced);
                        }
                        // QUOT (Quot.lift) — DEFERRED (None).
                        if let Some(reduced) = self.try_quot_reduction(&app) {
                            return self.whnf_impl(&reduced);
                        }
                        app
                    }
                }
            }
            // ZETA: let x := val in body → body[val/x]
            ExprKind::Let(_, _, val, body, _) => {
                let reduced = body.instantiate(val);
                self.whnf_impl(&reduced)
            }
            // DELTA: unfold constants (modeled env).
            //
            // The production reduction.rs writes this as
            //   env.unfold_with_transparency(..).map_or_else(|| e.clone(), |v| whnf(v))
            // — two closures. `map_or_else` is BY DEFINITION
            //   match opt { Some(v) => f(v), None => default() }
            // so we desugar it to the equivalent `match` (no closure aggregate; the
            // DELTA control flow — clone-if-opaque vs whnf-the-unfolding — is identical).
            ExprKind::Const(name, _levels) => match self.unfold_const(name) {
                Some(val) => self.whnf_impl(&val),
                None => e.clone(),
            },
            // Projection (iota-proj).
            ExprKind::Proj(struct_name, idx, expr) => self.reduce_proj(struct_name, *idx, expr),
            // MData transparency: strip metadata wrappers.
            ExprKind::MData(_, inner) => self.whnf_impl(inner),
            _ => e.clone(),
        }
    }

    // ── reduce_proj — VERBATIM clean reduction.rs:87. ──
    //
    // WHNF the struct expr; if the head is a modeled constructor, extract the field
    // at `num_params + idx` and WHNF it. Otherwise rebuild Proj via from_kind.
    fn reduce_proj(&self, struct_name: &Name, idx: u32, expr: &Expr) -> Expr {
        let expr_whnf = self.whnf_impl(expr);
        let head = expr_whnf.get_app_fn();
        if let ExprKind::Const(ctor_name, _) = &head.kind {
            if let Some(num_params) = self.get_constructor_num_params(ctor_name) {
                let args = expr_whnf.get_app_args();
                let field_idx = num_params as usize + idx as usize;
                if field_idx < args.len() {
                    return self.whnf_impl(&args[field_idx]);
                }
            }
        }
        Expr::from_kind(ExprKind::Proj(
            *struct_name,
            idx,
            Arc::new(expr_whnf),
        ))
    }

    // ====================================================================
    // DEF-EQ pillar — VERBATIM cert/expr_eq.rs `CertExprEqContext`.
    //
    // The real engine is a trait with `whnf_for_eq` supplied by the verifier
    // (= our `whnf_impl`). Here it is inlined as inherent methods on the same
    // `CertVerifier`, composing the already-verified `whnf_impl`.
    // ====================================================================

    // Universe level equality via normalization (real: `Level::is_def_eq(l1,l2)`).
    fn level_eq(&self, l1: &Level, l2: &Level) -> bool {
        Level::is_def_eq(l1, l2)
    }

    // Const level-vector equality. The real engine writes this as
    //   ls1.len() == ls2.len() && ls1.iter().zip(ls2).all(|(l1,l2)| level_eq(l1,l2))
    // `.zip().all(|..|)` builds an iterator-closure aggregate (not yet lowerable);
    // this is the SAME element-wise compare as an explicit index loop (faithful —
    // the modeling boundary the slice already uses for env/ctor scans).
    fn level_vec_eq(&self, ls1: &[Level], ls2: &[Level]) -> bool {
        if ls1.len() != ls2.len() {
            return false;
        }
        let mut i: usize = 0;
        let n = ls1.len();
        while i < n {
            if !self.level_eq(&ls1[i], &ls2[i]) {
                return false;
            }
            i += 1;
        }
        true
    }

    // ── structural_eq_inner — the post-WHNF structural compare (cert/expr_eq.rs:213).
    //
    // VERBATIM for every ExprKind variant present in this slice. The real engine
    // also has Cubical*/SProp/ZFC*/Squash arms; those variants are not in this
    // slice's `ExprKind`, so a pair never reaches them (they would land in the
    // same `_ => false` catch-all). The CORE 11-variant compare is verbatim.
    fn structural_eq(&self, a: &Expr, b: &Expr) -> bool {
        match (&a.kind, &b.kind) {
            (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
            (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => self.level_eq(l1, l2),
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => {
                n1 == n2 && self.level_vec_eq(ls1, ls2)
            }
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.structural_eq(f1, f2) && self.structural_eq(a1, a2)
            }
            // Binder info is irrelevant for definitional equality in CIC.
            (ExprKind::Lam(_bi1, ty1, b1), ExprKind::Lam(_bi2, ty2, b2))
            | (ExprKind::Pi(_bi1, ty1, b1), ExprKind::Pi(_bi2, ty2, b2)) => {
                self.structural_eq(ty1, ty2) && self.structural_eq(b1, b2)
            }
            (ExprKind::Let(_, ty1, v1, b1, _), ExprKind::Let(_, ty2, v2, b2, _)) => {
                self.structural_eq(ty1, ty2)
                    && self.structural_eq(v1, v2)
                    && self.structural_eq(b1, b2)
            }
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
                n1 == n2 && i1 == i2 && self.structural_eq(e1, e2)
            }
            (ExprKind::MData(_, inner1), ExprKind::MData(_, inner2)) => {
                self.structural_eq(inner1, inner2)
            }
            _ => false,
        }
    }

    // ── is_def_eq / def_eq_impl / def_eq_inner — VERBATIM cert/expr_eq.rs:51.
    //
    // `is_def_eq` is the slice's `--mir-emit-closure` ROOT name (the real public
    // entry is `def_eq`; def_eq_impl is the internal recursion target). All three
    // route to `def_eq_inner`, matching the real `def_eq_impl -> stack_safe(||
    // def_eq_inner)` (stack_safe is a recursion-depth trampoline, a pass-through
    // on test terms — same reporting as whnf_impl/whnf_inner).
    fn is_def_eq(&self, a: &Expr, b: &Expr) -> bool {
        self.def_eq_inner(a, b)
    }
    fn def_eq_impl(&self, a: &Expr, b: &Expr) -> bool {
        self.def_eq_inner(a, b)
    }

    fn def_eq_inner(&self, a: &Expr, b: &Expr) -> bool {
        // Fast path: value equality after WHNF. (The real engine first does the
        // pre-WHNF `a == b` PartialEq fast path; `Expr` here doesn't derive
        // PartialEq — the verified compute_meta + structural recursion below
        // subsumes it. The post-WHNF fast path uses `structural_eq` over the
        // verified meta-hash + structure, EXERCISING compute_meta as the fast
        // path the real code gets from cached-hash `PartialEq`.)
        let a_whnf = self.whnf_impl(a);
        let b_whnf = self.whnf_impl(b);
        if a_whnf.meta.raw() == b_whnf.meta.raw() && self.structural_eq(&a_whnf, &b_whnf) {
            return true;
        }
        // Deep comparison: recurse with def_eq_impl on subterms so each level
        // gets WHNF + semantic equality, not just structural matching.
        let matched = match (&a_whnf.kind, &b_whnf.kind) {
            (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
            (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => self.level_eq(l1, l2),
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => {
                n1 == n2 && self.level_vec_eq(ls1, ls2)
            }
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.def_eq_impl(f1, f2) && self.def_eq_impl(a1, a2)
            }
            // Binder info is irrelevant for definitional equality in CIC.
            (ExprKind::Lam(_bi1, ty1, b1), ExprKind::Lam(_bi2, ty2, b2))
            | (ExprKind::Pi(_bi1, ty1, b1), ExprKind::Pi(_bi2, ty2, b2)) => {
                self.def_eq_impl(ty1, ty2) && self.def_eq_impl(b1, b2)
            }
            (ExprKind::Let(_, ty1, v1, b1, _), ExprKind::Let(_, ty2, v2, b2, _)) => {
                self.def_eq_impl(ty1, ty2) && self.def_eq_impl(v1, v2) && self.def_eq_impl(b1, b2)
            }
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
                n1 == n2 && i1 == i2 && self.def_eq_impl(e1, e2)
            }
            (ExprKind::MData(_, inner1), ExprKind::MData(_, inner2)) => {
                self.def_eq_impl(inner1, inner2)
            }
            _ => false,
        };
        if matched {
            return true;
        }
        // Eta expansion: (λ x : A. f x) ≡ f when x ∉ FV(f)
        self.try_eta_expansion(&a_whnf, &b_whnf)
    }

    // ── try_eta_expansion — VERBATIM cert/expr_eq.rs:189. ──
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
}

// ── Roots: keep whnf_impl + the composed primitives in the mono-item graph. ──
pub fn _root_whnf(
    env: &[(Name, Option<Expr>)],
    ctors: &[(Name, u32)],
    e: &Expr,
) -> Expr {
    let chk = CertVerifier { env, ctors };
    chk.whnf_impl(e)
}
pub fn _root_instantiate(e: &Expr, v: &Expr, d: u32) -> Expr {
    e.instantiate_at(v, d)
}
pub fn _root_lift(e: &Expr, s: u32, a: u32) -> Expr {
    e.lift_at(s, a)
}
pub fn _root_def_eq(
    env: &[(Name, Option<Expr>)],
    ctors: &[(Name, u32)],
    a: &Expr,
    b: &Expr,
) -> bool {
    let chk = CertVerifier { env, ctors };
    chk.is_def_eq(a, b)
}
