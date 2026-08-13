// clean_eta_ext_slice — STRUCTURE-ETA EXTENSIONS (thread T2), extending the
// already-verified structure-eta surface (clean_struct_eta_slice.rs, verified
// 2026-07-01) with the three handoff-listed extensions:
//
//   (a) params>0 structures — the verified slice's registry was all
//       `num_params: 0`; this slice adds PPAIR (1 param, 2 fields) and PBOX
//       (1 param, 1 field) so the `args.len() != num_params + num_fields`
//       saturation gate, the `args[num_params + i]` fieldwise offset, and
//       reduce_proj's `num_params + idx` projection offset are exercised with
//       nonzero params. Includes the Lean-parity behavior that ctor-app PARAMS
//       are counted but NEVER compared fieldwise (type correctness is assumed
//       upstream) — that behavior is part of the verified surface.
//   (b) proj-vs-proj nesting — cases where BOTH def-eq sides are projections
//       (the (Proj,Proj) structural arm), where a neutral's projections appear
//       as ctor-app fields (`S.mk s.1 s.2 =?= s`, the pure-eta case with an
//       OPAQUE neutral), and where structure-eta must RECURSE through def_eq
//       into an inner nested structure (`Rect.mk (Point.mk r.0.0 r.0.1) r.1
//       =?= r`), which requires the Proj TYPING rule (tc/infer_proj.rs) inside
//       try_structure_eta_core's `infer_type(s)`.
//   (c) tc/eta.rs's SEPARATE recursor-major structure-eta path —
//       `is_constructor_app` (eta.rs:89), `expand_eta_struct` (eta.rs:101,
//       Lean 4 inductive.cpp:98-111), `try_eta_struct` (eta.rs:141, Lean 4
//       inductive.h:60-73 to_cnstr_when_structure) and `try_eta_struct_core`
//       (eta.rs:166) — transcribed VERBATIM (modulo the boundaries below).
//       This path CONSTRUCTS the expansion `S.mk params.. (Proj 0 e) ..
//       (Proj n-1 e)`, so its differential compares the constructed Expr graph
//       structurally AND with the recomputed ExprMeta word bit-identical at
//       every node.
//
// REAL SOURCES TRANSCRIBED (clean @ $HOME/clean/crates/clean-kernel):
//   - tc/def_eq/structural.rs:158 try_structure_eta_expansion (verbatim)
//   - tc/def_eq/structural.rs:181 try_structure_eta_core (verbatim; the
//     `(0..num_fields).all(|i| ..)` closure is rewritten as a while loop —
//     semantics identical; established slice pattern)
//   - tc/eta.rs:81  is_structure_like (verbatim)
//   - tc/eta.rs:89  is_constructor_app (verbatim)
//   - tc/eta.rs:101 expand_eta_struct (verbatim; `for` loops -> while;
//     `type_args.get(i)?` -> explicit len check + index — same semantics)
//   - tc/eta.rs:141 try_eta_struct + tc/eta.rs:166 try_eta_struct_core
//     (verbatim; guard 4's `type_of_type.is_prop()` uses the real
//     expr/constructors.rs:204 is_prop = Sort(l) with l zero)
//   - tc/infer_proj.rs:73 infer_proj_type_from_impl — the Proj TYPING rule
//     (see boundary [B3]: cache modeled out, quick-path semantics)
//   - tc/infer_proj.rs:279 walk_prop_telescope_to_idx — the uncached telescope
//     walk (computes the identical domain sequence the batch cache fills)
//   - tc/infer_proj.rs:357 instantiate_params (verbatim; iterator -> indexed
//     while over the first `count` args)
//   - tc/infer.rs:62 pi_domain_body_quick (inlined at its two call sites:
//     syntactic-Pi fast path, else whnf then split — verbatim semantics)
//   - whnf/reduce_proj/def_eq/infer_type: the VERIFIED pillar shapes from the
//     prior slices (clean_expr_whnf_slice.rs / clean_struct_eta_slice.rs),
//     with def_eq_inner RESHAPED to mirror tc/def_eq/structural.rs's REAL
//     fallback placement (see [B5]) — that reshape is (re-)verified here.
//
// ── MODELED BOUNDARIES (each also reported in the thread report) ──
// [B1] Environment registries as slice-scans (established pattern): the real
//      `InductiveVal {name, level_params, type_, num_params, num_indices,
//      all_names, constructor_names, is_recursive, ..}` is modeled as
//      `InductiveInfo {name, num_ctors (= constructor_names.len()), ctor_name
//      (= constructor_names[0]), num_indices, is_recursive}`; the real
//      `ConstructorVal {name, inductive_name, level_params, type_, num_params,
//      num_fields, ..}` as `ConstructorInfo {ctor_name, inductive_name,
//      num_params, num_fields}` + a side table `ctor_types: &[(Name, Expr)]`
//      carrying ConstructorVal.type_ (keyed by ctor name). Name = u32 interner
//      handle (established).
// [B2] level_params modeled ABSENT (non-universe-polymorphic inductives), so
//      infer_proj's level-count gate (infer_proj.rs:150) degenerates to
//      "type head must carry no levels" and instantiate_level_params_direct is
//      never taken. expand_eta_struct's `levels.clone()` propagation (the type
//      head's levels onto the built ctor Const) IS exercised (scenario c2).
// [B3] tc caches modeled out: proj_type_cache's batch fill
//      (cache_projection_field_types_non_prop/_prop) is replaced by the
//      UNCACHED telescope walk (walk_prop_telescope_to_idx's loop, which
//      computes the identical domain sequence); `try_infer_type_quick(e)
//      .or_else(infer_type_infer_only(e).ok())` is modeled as the single
//      uncached infer_type (quick is a partial fast path whose fallback is
//      full inference — the composite's SEMANTICS equal full inference).
//      Prop-projection validation of the strict path is NOT exercised (the
//      def-eq/eta call sites use the quick-path semantics). Proj-typing
//      failure modes are collapsed onto TypeError::Unsupported/UnknownConst —
//      the eta gates only observe Ok vs Err (annotated per site).
// [B4] whnf models delta-unfolding eagerly via the env slice (the established
//      VERIFIED whnf pillar shape); heartbeats, reduction caches, equiv
//      manager, def-eq cache, lazy-delta ordering (def_eq/mod.rs phases 2-5),
//      proof-irrelevance, unit-like and string-lit phases (7-8) are modeled
//      out (verified separately in prior rungs / not composed here). Phase-3
//      Const/FVar comparison is subsumed by the structural Const/FVar arms.
// [B5] def_eq_inner mirrors tc/def_eq/structural.rs's is_def_eq_structural ARM
//      PLACEMENT faithfully: struct-eta fires ONLY from the App-vs-App failure
//      fallback (structural.rs:38) and the mixed-kind catchall
//      (structural.rs:68); same-kind non-App arms (Sort/Const/Proj/Lam/Pi/...)
//      return their result directly WITHOUT a struct-eta fallback, and
//      Lam-vs-non-Lam goes to function-eta. is_def_eq_app_spine's flattened
//      left-to-right compare is modeled as pairwise App recursion — same
//      boolean semantics (struct-eta additionally reachable on inner
//      partial-application pairs, where the saturation gate makes it
//      vacuously false). is_def_eq_binding's FVar opening is modeled as
//      pairwise BVar def_eq (established verified-pillar boundary).
// [B6] `for i in 0..n` loops -> while loops; `.get(i)?`/`.all(..)` -> explicit
//      len checks + indexed while (frontend Range/combinator limits;
//      semantics preserved). BinderData {info: u8, mult: u8} and
//      Literal::Str(u32) are the established models.
//
// Crate name is load-bearing (mangled into the extern-leaf symbols the JIT
// binds), so it MUST stay `clean_eta_ext_slice`.
//
// EMIT (two closures from this one slice):
//   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//   cd $HOME/trust-ir/frontend
//   env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//     $S/bin/cargo run --bin trust_ir_mir -- clean_eta_ext_slice.rs \
//       --crate-type=lib --mir-emit-closure eta_ext_root <out1.tir>
//   .. and the same with --mir-emit-closure expand_eta_root <out2.tir>
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

fn bd_default() -> BinderData { BinderData { info: 0, mult: 2 } }

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
    // VERBATIM Expr::has_loose_bvars (meta-cached O(1) read).
    fn has_loose_bvars(&self) -> bool { self.loose_bvar_range() > 0 }
    // VERBATIM expr/constructors.rs:204 is_prop: "Check if this is Prop (Sort 0)".
    fn is_prop(&self) -> bool {
        match &self.kind { ExprKind::Sort(l) => Level::is_zero(l), _ => false }
    }
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

    // VERBATIM lift_at (the VERIFIED construction pillar, reused).
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
    // VERBATIM instantiate / instantiate_at (the VERIFIED beta pillar, reused).
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

// ─────────────── InductiveInfo / ConstructorInfo (registry model [B1]) ───────

#[derive(Clone, Debug)]
pub struct InductiveInfo {
    pub name: Name,
    pub num_ctors: u32,   // models InductiveVal.constructor_names.len()
    pub ctor_name: Name,  // models InductiveVal.constructor_names[0]
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

// ───────────────────────── TypeError (unchanged from verified slice) ─────────
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
// Six slice-scan tables mirror the real Environment lookups [B1]:
//   env         — Const delta-unfolding value (whnf DELTA)
//   ctor_np     — a constructor's num_params (reduce_proj's field offset)
//   decl_types  — a Const's declared type (infer_type's Const rule)
//   ctor_types  — a constructor's declared TYPE (ConstructorVal.type_; the Pi
//                 telescope the Proj typing rule walks) — NEW in this slice
//   inductives  — the InductiveVal registry (is_structure_like's gate + the
//                 ctor_name/num_indices reads of expand/infer_proj)
//   ctors       — the ConstructorVal registry (try_structure_eta_core's fields)
pub struct CertVerifier<'env> {
    env: &'env [(Name, Option<Expr>)],
    ctor_np: &'env [(Name, u32)],
    decl_types: &'env [(Name, Expr)],
    ctor_types: &'env [(Name, Expr)],
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
    // ConstructorVal.type_ (modeled as a side table keyed by ctor name [B1]).
    fn ctor_declared_type(&self, name: &Name) -> Option<Expr> {
        let mut i: usize = 0;
        let n = self.ctor_types.len();
        while i < n {
            let entry = &self.ctor_types[i];
            if entry.0 == *name { return Some(entry.1.clone()); }
            i += 1;
        }
        None
    }
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

    // ── WHNF pillar (cert/reduction.rs whnf_impl) — VERIFIED shape, reused [B4]. ──
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
    // reduce_proj — the Proj arm of whnf (VERIFIED pillar, reused). Projects the
    // field out of a ctor-app (skipping num_params args), else re-forms neutral.
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

    // ── DEF-EQ pillar — RESHAPED to the REAL structural.rs arm placement [B5]. ──
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
    // def_eq_inner — whnf(+delta [B4]) both sides, meta+structural fast path,
    // then tc/def_eq/structural.rs's is_def_eq_structural ARMS with the REAL
    // fallback placement:
    //   * App-vs-App: spine compare (pairwise model [B5]); on failure fall back
    //     to try_structure_eta_expansion (structural.rs:38).
    //   * Lam-vs-non-Lam (either side): function-eta (structural.rs:47-56).
    //   * mixed-kind catchall: try_structure_eta_expansion (structural.rs:68).
    //   * same-kind non-App arms return their result DIRECTLY (no fallback),
    //     exactly like the real match.
    fn def_eq_inner(&self, a: &Expr, b: &Expr) -> bool {
        let a_whnf = self.whnf_impl(a);
        let b_whnf = self.whnf_impl(b);
        if a_whnf.meta.raw() == b_whnf.meta.raw() && self.structural_eq(&a_whnf, &b_whnf) {
            return true;
        }
        match (&a_whnf.kind, &b_whnf.kind) {
            (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
            (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => self.level_eq(l1, l2),
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => n1 == n2 && self.level_vec_eq(ls1, ls2),
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                // is_def_eq_app_spine modeled as pairwise recursion [B5]; on
                // failure fall back to struct-eta (structural.rs:33-38).
                if self.def_eq_impl(f1, f2) && self.def_eq_impl(a1, a2) {
                    return true;
                }
                self.try_structure_eta_expansion(&a_whnf, &b_whnf)
            }
            (ExprKind::Lam(_b1, ty1, b1), ExprKind::Lam(_b2, ty2, b2))
            | (ExprKind::Pi(_b1, ty1, b1), ExprKind::Pi(_b2, ty2, b2)) => self.def_eq_impl(ty1, ty2) && self.def_eq_impl(b1, b2),
            (ExprKind::Let(_, ty1, v1, b1, _), ExprKind::Let(_, ty2, v2, b2, _)) => self.def_eq_impl(ty1, ty2) && self.def_eq_impl(v1, v2) && self.def_eq_impl(b1, b2),
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => n1 == n2 && i1 == i2 && self.def_eq_impl(e1, e2),
            (ExprKind::MData(_, in1), ExprKind::MData(_, in2)) => self.def_eq_impl(in1, in2),
            (ExprKind::Lam(..), _) | (_, ExprKind::Lam(..)) => self.try_eta_expansion(&a_whnf, &b_whnf),
            _ => self.try_structure_eta_expansion(&a_whnf, &b_whnf),
        }
    }
    // function-eta (the VERIFIED cert eta template, unchanged boundary: no
    // other-side Pi type check — established verified-pillar shape).
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

    // ── INFER-TYPE pillar (tc/infer.rs) — VERIFIED shape + the NEW Proj rule. ──
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
            // NEW: the Proj TYPING rule (tc/infer_proj.rs), needed by the
            // nested structure-eta recursion where `s` is itself a projection.
            ExprKind::Proj(struct_name, idx, expr) => {
                let expr_type = self.infer_type_core(expr, ctx)?;
                self.infer_proj_type_from(struct_name, *idx, expr, &expr_type)
            }
            // FVar typing needs a local context we don't model here (the
            // verified infer pillar's established boundary: FVar was under
            // the prior slice's `_ => Unsupported` catchall).
            ExprKind::FVar(_) => Err(TypeError::Unsupported),
        }
    }

    // ── infer_proj_type_from — tc/infer_proj.rs:73 infer_proj_type_from_impl,
    //    quick-path semantics (validate_prop_projection = false), UNCACHED [B3].
    //    Failure modes collapsed onto Unsupported/UnknownConst [B3] — the real
    //    error variants are annotated per site.
    fn infer_proj_type_from(&self, struct_name: &Name, idx: u32, expr: &Expr, expr_type: &Expr) -> Result<Expr, TypeError> {
        // [proj_type_cache lookup modeled out — B3]
        let expr_type_whnf = self.whnf_impl(expr_type);
        // [is_prop cache-routing modeled out — B3: both the Prop and non-Prop
        //  quick paths compute the same domain sequence via the telescope walk]
        // Extract the inductive type name and universe levels.
        let (type_name, type_levels): (Name, LevelVec) = match &expr_type_whnf.get_app_fn().kind {
            ExprKind::Const(name, levels) => (*name, levels.clone()),
            _ => return Err(TypeError::Unsupported), // InvalidProjNotStruct
        };
        // Verify the type matches the struct name in the projection.
        if type_name != *struct_name {
            return Err(TypeError::Unsupported); // InvalidProjNotStruct
        }
        let type_args = expr_type_whnf.get_app_args();
        // Look up the inductive type.
        let ind = match self.get_inductive(struct_name) {
            Some(i) => i,
            None => return Err(TypeError::Unsupported), // UnknownInductive
        };
        // Structures must have exactly one constructor.
        if ind.num_ctors != 1 {
            return Err(TypeError::Unsupported); // InvalidProjNotUniqueConstructor
        }
        // Look up the constructor.
        let ctor_name = ind.ctor_name; // constructor_names[0] [B1]
        let ctor = match self.get_constructor(&ctor_name) {
            Some(c) => c,
            None => return Err(TypeError::UnknownConst(ctor_name)),
        };
        // Check index is in bounds.
        if idx >= ctor.num_fields {
            return Err(TypeError::Unsupported); // InvalidProjIndexOutOfBounds
        }
        // Level params modeled absent [B2]: the level-count gate
        // (infer_proj.rs:150) degenerates to requiring an unleveled type head;
        // instantiate_level_params_direct is never taken.
        if type_levels.len() != 0 {
            return Err(TypeError::Unsupported); // LevelCountMismatch
        }
        let ctor_type = match self.ctor_declared_type(&ctor_name) {
            Some(t) => t,
            None => return Err(TypeError::UnknownConst(ctor_name)),
        };
        // Require exactly num_params + num_indices type args (Lean 4
        // type_checker.cpp:237-238).
        let num_params = ctor.num_params as usize;
        let num_indices = ind.num_indices as usize;
        let expected_args = num_params + num_indices;
        if type_args.len() != expected_args {
            return Err(TypeError::Unsupported); // InvalidProjWrongArgCount
        }
        // Instantiate parameters with the first num_params type arguments.
        let instantiated_ctor_type = self.instantiate_params_prefix(&ctor_type, &type_args, num_params);
        // Walk the field telescope to the target index (the UNCACHED
        // walk_prop_telescope_to_idx loop [B3]; the batch cache fills compute
        // the identical domain sequence).
        self.walk_telescope_to_idx(struct_name, expr, &instantiated_ctor_type, idx, ctor.num_fields)
    }

    // instantiate_params (tc/infer_proj.rs:357) — iterator arg modeled as the
    // first `count` elements of `args` (exactly what the caller passes) [B6].
    fn instantiate_params_prefix(&self, ty: &Expr, args: &Vec<Expr>, count: usize) -> Expr {
        let mut result = ty.clone();
        let mut i: usize = 0;
        while i < count {
            let result_whnf = self.whnf_impl(&result);
            match &result_whnf.kind {
                ExprKind::Pi(_, _, body) => { result = body.instantiate(&args[i]); }
                _ => { return result; } // break
            }
            i += 1;
        }
        result
    }

    // walk_prop_telescope_to_idx (tc/infer_proj.rs:279) — the uncached
    // telescope walk. pi_domain_body_quick (tc/infer.rs:62) is inlined:
    // syntactic-Pi fast path, else whnf then split [B6].
    fn walk_telescope_to_idx(&self, struct_name: &Name, expr: &Expr, instantiated_ctor_type: &Expr, target_idx: u32, num_fields: u32) -> Result<Expr, TypeError> {
        let mut current_type = instantiated_ctor_type.clone();
        let mut field_idx: u32 = 0;
        while field_idx <= target_idx {
            // pi_domain_body_quick, inlined.
            let cur = match &current_type.kind {
                ExprKind::Pi(..) => current_type.clone(),
                _ => self.whnf_impl(&current_type),
            };
            let (domain, body): (Expr, Expr) = match &cur.kind {
                ExprKind::Pi(_, d, b) => (d.as_ref().clone(), b.as_ref().clone()),
                _ => return Err(TypeError::Unsupported), // InvalidProjIndexOutOfBounds
            };
            if field_idx == target_idx {
                return Ok(domain);
            }
            if body.has_loose_bvars() {
                // Dependent field: instantiate the body with `Proj field_idx expr`.
                let proj_field = Expr::proj(*struct_name, field_idx, expr.clone());
                current_type = body.instantiate(&proj_field);
            } else {
                current_type = body;
            }
            field_idx += 1;
        }
        Err(TypeError::Unsupported) // InvalidProjIndexOutOfBounds
    }

    // ══════════════════════════════════════════════════════════════════════
    // STRUCTURE-ETA (def-eq path) — VERBATIM (verified surface, extended here)
    // ══════════════════════════════════════════════════════════════════════

    // is_structure_like — VERBATIM tc/eta.rs:81.
    fn is_structure_like(&self, name: &Name) -> bool {
        let ind = match self.get_inductive(name) { Some(i) => i, None => return false };
        ind.num_ctors == 1 && ind.num_indices == 0 && !ind.is_recursive
    }

    // try_structure_eta_expansion — VERBATIM def_eq/structural.rs:158.
    fn try_structure_eta_expansion(&self, a_whnf: &Expr, b_whnf: &Expr) -> bool {
        self.try_structure_eta_core(a_whnf, b_whnf) || self.try_structure_eta_core(b_whnf, a_whnf)
    }

    // try_structure_eta_core — VERBATIM def_eq/structural.rs:181 (Lean 4
    // type_checker.cpp:786-811 try_eta_struct_core). `(0..num_fields).all`
    // rewritten as a while loop [B6].
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
        // `s`'s type must be the same structure. (tc-cache boundary [B3]:
        // try_infer_type_quick .or_else full — modeled as uncached infer_type.)
        let s_type = match self.infer_type(s) { Ok(ty) => ty, Err(_) => return false };
        let s_type_whnf = self.whnf_impl(&s_type);
        let s_ind = match &s_type_whnf.get_app_fn().kind {
            ExprKind::Const(s_ind, _) => *s_ind,
            _ => return false,
        };
        if s_ind != ctor.inductive_name {
            return false;
        }
        // Fieldwise: Proj i s =?= t.field_i (Lean 4 type_checker.cpp:805-809).
        // NOTE: params (args[0..num_params]) are counted but NEVER compared.
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

    // ══════════════════════════════════════════════════════════════════════
    // STRUCTURE-ETA (recursor-major path, tc/eta.rs) — extension (c)
    // ══════════════════════════════════════════════════════════════════════

    // is_constructor_app — VERBATIM tc/eta.rs:89.
    fn is_constructor_app(&self, e: &Expr) -> bool {
        let head = e.get_app_fn();
        if let ExprKind::Const(name, _) = &head.kind {
            return self.get_constructor(name).is_some();
        }
        false
    }

    // expand_eta_struct — VERBATIM tc/eta.rs:101 (Lean 4 inductive.cpp:98-111).
    // Expand e to constructor form: S.mk params.. (proj 0 e) .. (proj n-1 e).
    // `e_type` is the WHNF'd type of `e` (must be of form `S params...`).
    // `for` loops -> while; `type_args.get(i)?` -> len check + index [B6].
    fn expand_eta_struct(&self, e_type: &Expr, e: &Expr) -> Option<Expr> {
        // Get the inductive name - check head before collecting args.
        let type_head = e_type.get_app_fn();
        let (ind_name, levels): (Name, LevelVec) = match &type_head.kind {
            ExprKind::Const(n, ls) => (*n, ls.clone()),
            _ => return None,
        };
        // Now collect args (after confirming head is Const).
        let type_args = e_type.get_app_args();
        // Get the constructor.
        let ind = match self.get_inductive(&ind_name) { Some(i) => i, None => return None };
        if ind.num_ctors != 1 {
            // constructor_names.len() != 1 [B1]
            return None;
        }
        let ctor_name = ind.ctor_name; // constructor_names[0] [B1]
        let ctor = match self.get_constructor(&ctor_name) { Some(c) => c, None => return None };
        // Build: ctor params... (proj 0 e) (proj 1 e) ... (proj n e).
        // The type head's LEVELS are cloned onto the built ctor Const.
        let mut result = Expr::const_(ctor_name, levels);
        // Apply parameters (first num_params of type_args).
        let mut i: usize = 0;
        while i < ctor.num_params as usize {
            if i >= type_args.len() { return None; } // type_args.get(i)?
            result = Expr::app(result, type_args[i].clone());
            i += 1;
        }
        // Apply projections for each field.
        let mut field_idx: u32 = 0;
        while field_idx < ctor.num_fields {
            let proj = Expr::proj(ind_name, field_idx, e.clone());
            result = Expr::app(result, proj);
            field_idx += 1;
        }
        Some(result)
    }

    // try_eta_struct — VERBATIM tc/eta.rs:141 (Lean 4 inductive.h:60-73
    // to_cnstr_when_structure).
    fn try_eta_struct(&self, ind_name: &Name, e: &Expr) -> Option<Expr> {
        // Guard 1: Must be structure-like.
        if !self.is_structure_like(ind_name) {
            return None;
        }
        // Guard 2: Already a constructor application - no expansion needed.
        if self.is_constructor_app(e) {
            return None;
        }
        // Get the type of e (tc-cache boundary [B3]: quick .or_else full ->
        // modeled as the single uncached infer_type).
        let e_type_raw = match self.infer_type(e) { Ok(t) => t, Err(_) => return None };
        let e_type = self.whnf_impl(&e_type_raw);
        self.try_eta_struct_core(ind_name, e, &e_type)
    }

    // try_eta_struct_core — VERBATIM tc/eta.rs:166 (recursor-major conversion).
    fn try_eta_struct_core(&self, ind_name: &Name, e: &Expr, e_type_whnf: &Expr) -> Option<Expr> {
        // Guard 3: Type head must match the inductive.
        let type_head = e_type_whnf.get_app_fn();
        let type_name = match &type_head.kind {
            ExprKind::Const(n, _) => *n,
            _ => return None,
        };
        if type_name != *ind_name {
            return None;
        }
        // Guard 4: Not for Prop-typed structures (avoid duplicating proof
        // terms). (tc-cache boundary [B3] on the inner inference.)
        let type_of_type_raw = match self.infer_type(e_type_whnf) { Ok(t) => t, Err(_) => return None };
        let type_of_type = self.whnf_impl(&type_of_type_raw);
        if type_of_type.is_prop() {
            return None;
        }
        self.expand_eta_struct(e_type_whnf, e)
    }
}

// ───────────────────────── MODELED REGISTRY ──────────────────────────────
// Structures / inductives (see the scenario docs at the roots):
//   POINT    : paramless 2-field structure   Point.mk : Nat -> Nat -> Point
//   PPAIR    : 1-PARAM 2-field structure     PPair.mk : (A:Type) -> A -> A -> PPair A
//   RECT     : paramless 2-field NESTED      Rect.mk : Point -> Point -> Rect
//   PBOX     : 1-PARAM 1-field structure     PBox.mk : (A:Type) -> A -> PBox A
//   DSTRUCT  : paramless DEPENDENT 2-field   DStruct.mk : (T:Type) -> PBox T -> DStruct
//   BOOLLIKE : 2-ctor inductive (NOT structure-like)
//   LISTLIKE : single-ctor RECURSIVE (NOT structure-like)
//   VECLIKE  : single-ctor INDEXED (num_indices=1; NOT structure-like)
//   PROPS    : structure-like but PROPS : Prop (the tc/eta.rs guard-4 case)
pub const NATTY: u32 = 200;      // Nat : Type 0
pub const POINT: u32 = 100;      pub const POINT_MK: u32 = 101;    pub const P_VAL: u32 = 300;
pub const PPAIR: u32 = 110;      pub const PPAIR_MK: u32 = 111;    pub const PP_VAL: u32 = 310;
pub const RECT: u32 = 120;       pub const RECT_MK: u32 = 121;     pub const R_VAL: u32 = 320;
pub const PBOX: u32 = 130;       pub const PBOX_MK: u32 = 131;     pub const PB_VAL: u32 = 330;
pub const DSTRUCT: u32 = 140;    pub const DSTRUCT_MK: u32 = 141;  pub const D_VAL: u32 = 340;
pub const BOOLLIKE: u32 = 150;   pub const BOOLLIKE_T: u32 = 151;  pub const BOOLLIKE_F: u32 = 152; pub const B_VAL: u32 = 350;
pub const LISTLIKE: u32 = 160;   pub const LISTLIKE_MK: u32 = 161; pub const L_VAL: u32 = 360;
pub const VECLIKE: u32 = 170;    pub const VECLIKE_MK: u32 = 171;  pub const V_VAL: u32 = 370;
pub const PROPS: u32 = 180;      pub const PROPS_MK: u32 = 181;    pub const PR_VAL: u32 = 380;
pub const N0: u32 = 400;         pub const N1: u32 = 401;

// term builder shorthands (monomorphic free fns — no closures).
fn c(n: u32) -> Expr { Expr::cnst(Name(n)) }
fn ap(f: Expr, x: Expr) -> Expr { Expr::app(f, x) }
fn pj(s: u32, i: u32, e: Expr) -> Expr { Expr::proj(Name(s), i, e) }
fn sort1() -> Expr { Expr::sort(Level::succ(Level::Zero)) }
// the singleton level vec [Succ Zero] — built via Vec::new + push (NOT a
// vec![..] literal) so every Vec<Level> in the module shares one layout
// convention (the Vec::new/push/clone/deref leaf set).
fn lvl1() -> LevelVec {
    let mut v: LevelVec = Vec::new();
    v.push(Level::succ(Level::Zero));
    v
}

// Constructor TYPES (ConstructorVal.type_ [B1]) — real Pi telescopes:
fn point_mk_type() -> Expr {
    Expr::pi(bd_default(), c(NATTY), Expr::pi(bd_default(), c(NATTY), c(POINT)))
}
fn ppair_mk_type() -> Expr {
    // (A : Type 0) -> A -> A -> PPair A
    Expr::pi(bd_default(), sort1(),
        Expr::pi(bd_default(), Expr::bvar(0),
            Expr::pi(bd_default(), Expr::bvar(1), ap(c(PPAIR), Expr::bvar(2)))))
}
fn rect_mk_type() -> Expr {
    Expr::pi(bd_default(), c(POINT), Expr::pi(bd_default(), c(POINT), c(RECT)))
}
fn pbox_mk_type() -> Expr {
    // (A : Type 0) -> A -> PBox A
    Expr::pi(bd_default(), sort1(), Expr::pi(bd_default(), Expr::bvar(0), ap(c(PBOX), Expr::bvar(1))))
}
fn dstruct_mk_type() -> Expr {
    // (T : Type 0) -> PBox T -> DStruct   (field 1's type DEPENDS on field 0)
    Expr::pi(bd_default(), sort1(), Expr::pi(bd_default(), ap(c(PBOX), Expr::bvar(0)), c(DSTRUCT)))
}
fn listlike_mk_type() -> Expr { Expr::pi(bd_default(), c(LISTLIKE), c(LISTLIKE)) }
fn veclike_mk_type() -> Expr { Expr::pi(bd_default(), c(NATTY), ap(c(VECLIKE), Expr::bvar(0))) }
fn props_mk_type() -> Expr { Expr::pi(bd_default(), c(NATTY), c(PROPS)) }

fn build_inductives() -> Vec<InductiveInfo> {
    vec![
        InductiveInfo { name: Name(POINT),    num_ctors: 1, ctor_name: Name(POINT_MK),    num_indices: 0, is_recursive: false },
        InductiveInfo { name: Name(PPAIR),    num_ctors: 1, ctor_name: Name(PPAIR_MK),    num_indices: 0, is_recursive: false },
        InductiveInfo { name: Name(RECT),     num_ctors: 1, ctor_name: Name(RECT_MK),     num_indices: 0, is_recursive: false },
        InductiveInfo { name: Name(PBOX),     num_ctors: 1, ctor_name: Name(PBOX_MK),     num_indices: 0, is_recursive: false },
        InductiveInfo { name: Name(DSTRUCT),  num_ctors: 1, ctor_name: Name(DSTRUCT_MK),  num_indices: 0, is_recursive: false },
        InductiveInfo { name: Name(BOOLLIKE), num_ctors: 2, ctor_name: Name(BOOLLIKE_T),  num_indices: 0, is_recursive: false }, // 2 ctors -> NOT
        InductiveInfo { name: Name(LISTLIKE), num_ctors: 1, ctor_name: Name(LISTLIKE_MK), num_indices: 0, is_recursive: true  }, // recursive -> NOT
        InductiveInfo { name: Name(VECLIKE),  num_ctors: 1, ctor_name: Name(VECLIKE_MK),  num_indices: 1, is_recursive: false }, // indexed -> NOT
        InductiveInfo { name: Name(PROPS),    num_ctors: 1, ctor_name: Name(PROPS_MK),    num_indices: 0, is_recursive: false }, // structure-like, but : Prop
    ]
}

fn build_ctors() -> Vec<ConstructorInfo> {
    vec![
        ConstructorInfo { ctor_name: Name(POINT_MK),    inductive_name: Name(POINT),    num_params: 0, num_fields: 2 },
        ConstructorInfo { ctor_name: Name(PPAIR_MK),    inductive_name: Name(PPAIR),    num_params: 1, num_fields: 2 },
        ConstructorInfo { ctor_name: Name(RECT_MK),     inductive_name: Name(RECT),     num_params: 0, num_fields: 2 },
        ConstructorInfo { ctor_name: Name(PBOX_MK),     inductive_name: Name(PBOX),     num_params: 1, num_fields: 1 },
        ConstructorInfo { ctor_name: Name(DSTRUCT_MK),  inductive_name: Name(DSTRUCT),  num_params: 0, num_fields: 2 },
        ConstructorInfo { ctor_name: Name(BOOLLIKE_T),  inductive_name: Name(BOOLLIKE), num_params: 0, num_fields: 0 },
        ConstructorInfo { ctor_name: Name(BOOLLIKE_F),  inductive_name: Name(BOOLLIKE), num_params: 0, num_fields: 0 },
        ConstructorInfo { ctor_name: Name(LISTLIKE_MK), inductive_name: Name(LISTLIKE), num_params: 0, num_fields: 1 },
        ConstructorInfo { ctor_name: Name(VECLIKE_MK),  inductive_name: Name(VECLIKE),  num_params: 0, num_fields: 1 },
        ConstructorInfo { ctor_name: Name(PROPS_MK),    inductive_name: Name(PROPS),    num_params: 0, num_fields: 1 },
    ]
}

// ctor num_params table (reduce_proj) — MUST mirror build_ctors' num_params
// (the real env has one source of truth; two consistent tables here [B1]).
fn build_ctor_np() -> Vec<(Name, u32)> {
    vec![
        (Name(POINT_MK), 0),
        (Name(PPAIR_MK), 1),
        (Name(RECT_MK), 0),
        (Name(PBOX_MK), 1),
        (Name(DSTRUCT_MK), 0),
        (Name(BOOLLIKE_T), 0),
        (Name(BOOLLIKE_F), 0),
        (Name(LISTLIKE_MK), 0),
        (Name(VECLIKE_MK), 0),
        (Name(PROPS_MK), 0),
    ]
}

// ConstructorVal.type_ side table [B1].
fn build_ctor_types() -> Vec<(Name, Expr)> {
    vec![
        (Name(POINT_MK), point_mk_type()),
        (Name(PPAIR_MK), ppair_mk_type()),
        (Name(RECT_MK), rect_mk_type()),
        (Name(PBOX_MK), pbox_mk_type()),
        (Name(DSTRUCT_MK), dstruct_mk_type()),
        (Name(LISTLIKE_MK), listlike_mk_type()),
        (Name(VECLIKE_MK), veclike_mk_type()),
        (Name(PROPS_MK), props_mk_type()),
    ]
}

// Declared types (infer_type's Const rule). Neutrals are opaque Consts of the
// structure types; note PB_VAL's type head carries a LEVEL (scenario c2) and
// PROPS : Prop (= Sort 0, the guard-4 case).
fn build_decl_types() -> Vec<(Name, Expr)> {
    vec![
        (Name(NATTY), sort1()),                                   // Nat : Type 0
        (Name(POINT), sort1()),
        (Name(RECT), sort1()),
        (Name(DSTRUCT), sort1()),
        (Name(BOOLLIKE), sort1()),
        (Name(LISTLIKE), sort1()),
        (Name(PROPS), Expr::sort(Level::Zero)),                   // PROPS : Prop
        (Name(PPAIR), Expr::pi(bd_default(), sort1(), sort1())),  // PPair : Type -> Type
        (Name(PBOX), Expr::pi(bd_default(), sort1(), sort1())),   // PBox : Type -> Type
        (Name(VECLIKE), Expr::pi(bd_default(), c(NATTY), sort1())), // VecLike : Nat -> Type
        (Name(P_VAL), c(POINT)),                                  // p : Point
        (Name(PP_VAL), ap(c(PPAIR), c(NATTY))),                   // pp : PPair Nat
        (Name(R_VAL), c(RECT)),                                   // r : Rect
        (Name(PB_VAL), ap(Expr::const_(Name(PBOX), lvl1()), c(NATTY))), // pb : PBox.{1} Nat (leveled head)
        (Name(D_VAL), c(DSTRUCT)),                                // d : DStruct
        (Name(B_VAL), c(BOOLLIKE)),
        (Name(L_VAL), c(LISTLIKE)),
        (Name(V_VAL), ap(c(VECLIKE), c(N0))),
        (Name(PR_VAL), c(PROPS)),                                 // pr : PROPS
        (Name(N0), c(NATTY)),
        (Name(N1), c(NATTY)),
        // ctor consts (so infer types ctor-apps, e.g. of the unfolded canon):
        (Name(POINT_MK), point_mk_type()),
        (Name(PPAIR_MK), ppair_mk_type()),
        (Name(RECT_MK), rect_mk_type()),
        (Name(PBOX_MK), pbox_mk_type()),
        (Name(DSTRUCT_MK), dstruct_mk_type()),
    ]
}

// The canonical delta-unfolding for PP_VAL in the unfold scenarios:
// pp := PPair.mk Nat a b.
fn ppair_canon() -> Expr {
    ap(ap(ap(c(PPAIR_MK), c(NATTY)), c(N0)), c(N1))
}

// ───────────────────────── MONO ROOT 1 (#[no_mangle]) ────────────────────────
// eta_ext_root — extensions (a) params>0 and (b) proj-vs-proj nesting, driven
// through TWO entries (both real kernel call shapes):
//   entry == 0: v.is_def_eq(t, s)  — the FULL def-eq pillar with struct-eta
//               wired at the REAL structural.rs fallback sites (integration).
//   entry == 1: v.try_structure_eta_expansion(t, s) — the direct rule call, on
//               the terms as built (t is a whnf ctor-app; s the neutral,
//               deliberately NOT unfolded — eta bridges without unfolding s).
// Returns 1 iff def-eq / the rule proves them equal.
//
// scenario | t                                                       | s (env)                | expect
// ---------+---------------------------------------------------------+------------------------+-------
//    0     | PPair.mk Nat a b                                        | pp (unfolds to canon)  | 1  (a: params>0 TRUE)
//    1     | PPair.mk Nat a a                                        | pp (unfolds)           | 0  (a: field mismatch)
//    2     | PPair.mk Nat a           (UNSATURATED: 2 of 3 args)     | pp (unfolds)           | 0  (a: arity gate)
//    3     | (PPair.mk Nat a b) c     (OVERSATURATED: 4 args)        | pp (unfolds)           | 0  (a: arity gate)
//    4     | PPair.mk Point a b       (WRONG PARAM, fields match)    | pp (unfolds)           | 1  (a: params counted, NOT compared — Lean parity)
//    5     | PPair.mk Nat pp.0 pp.1                                  | pp OPAQUE              | 1  (a+b: params>0 + proj fields, pure eta)
//    6     | Rect.mk r.0 r.1                                         | r OPAQUE               | 1  (b: proj-vs-proj, pure eta)
//    7     | Rect.mk (Point.mk r.0.0 r.0.1) r.1                      | r OPAQUE               | 1  (b: NESTED inner eta + Proj TYPING rule)
//    8     | Rect.mk (Point.mk r.0.1 r.0.1) r.1  (inner idx wrong)   | r OPAQUE               | 0  (b: nested mismatch)
//    9     | DStruct.mk d.0 (PBox.mk d.0 (Proj PBOX 0 d.1))          | d OPAQUE               | 1  (b: DEPENDENT telescope + params>0 inner)
//   10     | DStruct.mk d.0 (PBox.mk d.0 (Proj PBOX 0 d.0))          | d OPAQUE               | 0  (b: dependent-case mismatch)
//   11     | ListLike.mk a                                           | l OPAQUE               | 0  (gate: recursive)
//   12     | VecLike.mk a                                            | v OPAQUE               | 0  (gate: indexed)
//   13     | BoolLike.t (bare Const, 0 fields)                       | b OPAQUE               | 0  (gate: 2-ctor; Const-Const arm has NO eta fallback)
#[no_mangle]
pub extern "C" fn eta_ext_root(scenario: u32, entry: u32) -> i32 {
    let ctor_np = build_ctor_np();
    let decl_types = build_decl_types();
    let ctor_types = build_ctor_types();
    let inductives = build_inductives();
    let ctors = build_ctors();

    let t: Expr;
    let neutral: u32;
    let mut unfold: Option<Expr> = None;
    if scenario == 0 {
        t = ap(ap(ap(c(PPAIR_MK), c(NATTY)), c(N0)), c(N1));
        neutral = PP_VAL;
        unfold = Some(ppair_canon());
    } else if scenario == 1 {
        t = ap(ap(ap(c(PPAIR_MK), c(NATTY)), c(N0)), c(N0));
        neutral = PP_VAL;
        unfold = Some(ppair_canon());
    } else if scenario == 2 {
        t = ap(ap(c(PPAIR_MK), c(NATTY)), c(N0));
        neutral = PP_VAL;
        unfold = Some(ppair_canon());
    } else if scenario == 3 {
        t = ap(ppair_canon(), c(N0));
        neutral = PP_VAL;
        unfold = Some(ppair_canon());
    } else if scenario == 4 {
        t = ap(ap(ap(c(PPAIR_MK), c(POINT)), c(N0)), c(N1));
        neutral = PP_VAL;
        unfold = Some(ppair_canon());
    } else if scenario == 5 {
        t = ap(ap(ap(c(PPAIR_MK), c(NATTY)), pj(PPAIR, 0, c(PP_VAL))), pj(PPAIR, 1, c(PP_VAL)));
        neutral = PP_VAL;
    } else if scenario == 6 {
        t = ap(ap(c(RECT_MK), pj(RECT, 0, c(R_VAL))), pj(RECT, 1, c(R_VAL)));
        neutral = R_VAL;
    } else if scenario == 7 {
        let inner = ap(
            ap(c(POINT_MK), pj(POINT, 0, pj(RECT, 0, c(R_VAL)))),
            pj(POINT, 1, pj(RECT, 0, c(R_VAL))),
        );
        t = ap(ap(c(RECT_MK), inner), pj(RECT, 1, c(R_VAL)));
        neutral = R_VAL;
    } else if scenario == 8 {
        let inner = ap(
            ap(c(POINT_MK), pj(POINT, 1, pj(RECT, 0, c(R_VAL)))),
            pj(POINT, 1, pj(RECT, 0, c(R_VAL))),
        );
        t = ap(ap(c(RECT_MK), inner), pj(RECT, 1, c(R_VAL)));
        neutral = R_VAL;
    } else if scenario == 9 {
        let inner = ap(ap(c(PBOX_MK), pj(DSTRUCT, 0, c(D_VAL))), pj(PBOX, 0, pj(DSTRUCT, 1, c(D_VAL))));
        t = ap(ap(c(DSTRUCT_MK), pj(DSTRUCT, 0, c(D_VAL))), inner);
        neutral = D_VAL;
    } else if scenario == 10 {
        let inner = ap(ap(c(PBOX_MK), pj(DSTRUCT, 0, c(D_VAL))), pj(PBOX, 0, pj(DSTRUCT, 0, c(D_VAL))));
        t = ap(ap(c(DSTRUCT_MK), pj(DSTRUCT, 0, c(D_VAL))), inner);
        neutral = D_VAL;
    } else if scenario == 11 {
        t = ap(c(LISTLIKE_MK), c(N0));
        neutral = L_VAL;
    } else if scenario == 12 {
        t = ap(c(VECLIKE_MK), c(N0));
        neutral = V_VAL;
    } else {
        t = c(BOOLLIKE_T);
        neutral = B_VAL;
    }

    let env: Vec<(Name, Option<Expr>)> = vec![(Name(neutral), unfold)];
    let v = CertVerifier {
        env: &env,
        ctor_np: &ctor_np,
        decl_types: &decl_types,
        ctor_types: &ctor_types,
        inductives: &inductives,
        ctors: &ctors,
    };
    let s = Expr::cnst(Name(neutral));

    let r = if entry == 0 {
        v.is_def_eq(&t, &s)
    } else {
        v.try_structure_eta_expansion(&t, &s)
    };
    if r { 1 } else { 0 }
}

// ───────────────────────── MONO ROOT 2 (#[no_mangle]) ────────────────────────
// expand_eta_root — extension (c): the tc/eta.rs recursor-major path
// try_eta_struct -> try_eta_struct_core -> expand_eta_struct. On Some, the
// CONSTRUCTED expansion is written through `out` (deep-compared native == JIT,
// meta word bit-identical at every node) and 1 is returned; on None returns 0
// (out untouched).
//
// scenario | (ind_name, e)                       | expect
// ---------+-------------------------------------+---------------------------------------------
//    0     | (POINT, p)                          | Some: Point.mk p.0 p.1        (paramless)
//    1     | (PPAIR, pp)                         | Some: PPair.mk Nat pp.0 pp.1  (PARAM applied from type_args)
//    2     | (PBOX, pb : PBox.{1} Nat)           | Some: PBox.mk{1} Nat pb.0     (LEVELS cloned onto ctor Const)
//    3     | (POINT, Point.mk a b)               | None (guard 2: already a ctor-app)
//    4     | (BOOLLIKE, b)                       | None (guard 1: 2 ctors -> not structure-like)
//    5     | (POINT, r : Rect)                   | None (guard 3: type head != inductive)
//    6     | (PROPS, pr : PROPS : Prop)          | None (guard 4: Prop-typed structure)
//    7     | (DSTRUCT, d)                        | Some: DStruct.mk d.0 d.1      (dependent struct: Proj list, no dep instantiation on this path)
//    8     | (LISTLIKE, l)                       | None (guard 1: recursive)
#[no_mangle]
pub extern "C" fn expand_eta_root(out: *mut Expr, scenario: u32) -> i32 {
    let ctor_np = build_ctor_np();
    let decl_types = build_decl_types();
    let ctor_types = build_ctor_types();
    let inductives = build_inductives();
    let ctors = build_ctors();
    // All neutrals OPAQUE on this path (delta plays no role in the expansion).
    let env: Vec<(Name, Option<Expr>)> = vec![(Name(0), None)];
    let v = CertVerifier {
        env: &env,
        ctor_np: &ctor_np,
        decl_types: &decl_types,
        ctor_types: &ctor_types,
        inductives: &inductives,
        ctors: &ctors,
    };

    let ind_name: u32;
    let e: Expr;
    if scenario == 0 {
        ind_name = POINT; e = c(P_VAL);
    } else if scenario == 1 {
        ind_name = PPAIR; e = c(PP_VAL);
    } else if scenario == 2 {
        ind_name = PBOX; e = c(PB_VAL);
    } else if scenario == 3 {
        ind_name = POINT; e = ap(ap(c(POINT_MK), c(N0)), c(N1));
    } else if scenario == 4 {
        ind_name = BOOLLIKE; e = c(B_VAL);
    } else if scenario == 5 {
        ind_name = POINT; e = c(R_VAL);
    } else if scenario == 6 {
        ind_name = PROPS; e = c(PR_VAL);
    } else if scenario == 7 {
        ind_name = DSTRUCT; e = c(D_VAL);
    } else {
        ind_name = LISTLIKE; e = c(L_VAL);
    }

    match v.try_eta_struct(&Name(ind_name), &e) {
        Some(expansion) => {
            unsafe { std::ptr::write(out, expansion); }
            1
        }
        None => 0,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Standalone self-check harness (native): exercises every scenario through both
// roots and both entries, verifying the expected results and (for the expand
// path) the expected constructed shapes.
// ════════════════════════════════════════════════════════════════════════════

fn deep_eq(a: &Expr, b: &Expr) -> bool {
    if a.meta.raw() != b.meta.raw() { return false; }
    match (&a.kind, &b.kind) {
        (ExprKind::BVar(x), ExprKind::BVar(y)) => x == y,
        (ExprKind::FVar(x), ExprKind::FVar(y)) => x == y,
        (ExprKind::Sort(x), ExprKind::Sort(y)) => x == y,
        (ExprKind::Const(n1, l1), ExprKind::Const(n2, l2)) => n1 == n2 && l1 == l2,
        (ExprKind::Lit(x), ExprKind::Lit(y)) => x == y,
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => deep_eq(f1, f2) && deep_eq(a1, a2),
        (ExprKind::Lam(b1, t1, y1), ExprKind::Lam(b2, t2, y2)) => b1 == b2 && deep_eq(t1, t2) && deep_eq(y1, y2),
        (ExprKind::Pi(b1, t1, y1), ExprKind::Pi(b2, t2, y2)) => b1 == b2 && deep_eq(t1, t2) && deep_eq(y1, y2),
        (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => n1 == n2 && i1 == i2 && deep_eq(e1, e2),
        (ExprKind::MData(m1, e1), ExprKind::MData(m2, e2)) => m1 == m2 && deep_eq(e1, e2),
        _ => false,
    }
}

fn expand_via_root(scenario: u32) -> Option<Expr> {
    let mut slot = std::mem::MaybeUninit::<Expr>::uninit();
    let got = expand_eta_root(slot.as_mut_ptr(), scenario);
    if got == 1 { Some(unsafe { slot.assume_init() }) } else { None }
}

fn main() {
    // eta_ext_root expectations (identical for entry 0 = full def_eq and
    // entry 1 = direct rule).
    let expects: [i32; 14] = [1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0];
    let mut ok = true;
    let mut s: u32 = 0;
    while s < 14 {
        let via_defeq = eta_ext_root(s, 0);
        let via_direct = eta_ext_root(s, 1);
        let e = expects[s as usize];
        if via_defeq != e || via_direct != e {
            println!("scenario {s}: def_eq={via_defeq} direct={via_direct} expect={e}  <-- MISMATCH");
            ok = false;
        } else {
            println!("scenario {s}: def_eq={via_defeq} direct={via_direct} expect={e}");
        }
        s += 1;
    }

    // expand_eta_root: Some shapes.
    let exp0 = expand_via_root(0);
    let want0 = ap(ap(c(POINT_MK), pj(POINT, 0, c(P_VAL))), pj(POINT, 1, c(P_VAL)));
    let exp1 = expand_via_root(1);
    let want1 = ap(ap(ap(c(PPAIR_MK), c(NATTY)), pj(PPAIR, 0, c(PP_VAL))), pj(PPAIR, 1, c(PP_VAL)));
    let exp2 = expand_via_root(2);
    let want2 = ap(
        ap(Expr::const_(Name(PBOX_MK), lvl1()), c(NATTY)),
        pj(PBOX, 0, c(PB_VAL)),
    );
    let exp7 = expand_via_root(7);
    let want7 = ap(ap(c(DSTRUCT_MK), pj(DSTRUCT, 0, c(D_VAL))), pj(DSTRUCT, 1, c(D_VAL)));
    let some_ok = match (&exp0, &exp1, &exp2, &exp7) {
        (Some(e0), Some(e1), Some(e2), Some(e7)) => {
            deep_eq(e0, &want0) && deep_eq(e1, &want1) && deep_eq(e2, &want2) && deep_eq(e7, &want7)
        }
        _ => false,
    };
    if !some_ok { println!("expand Some-shapes MISMATCH"); ok = false; } else { println!("expand Some-shapes OK (incl. params + levels propagation)"); }
    // None guards.
    let none_ok = expand_via_root(3).is_none()
        && expand_via_root(4).is_none()
        && expand_via_root(5).is_none()
        && expand_via_root(6).is_none()
        && expand_via_root(8).is_none();
    if !none_ok { println!("expand None-guards MISMATCH"); ok = false; } else { println!("expand None-guards OK (ctor-app / 2-ctor / head-mismatch / Prop / recursive)"); }

    std::process::exit((!ok) as i32);
}
