// clean_tc_stitch_slice — TC/ CACHED-PATH STITCHING (thread R2-C), de-modeling
// the two skeptic-flagged boundaries from the round-1 handoff:
//
//   (1) infer_proj's is_prop ERR-PROPAGATION GATE: the real
//       infer_proj_type_from_impl (tc/infer_proj.rs:73) computes
//       `let is_prop_type = self.is_prop(&expr_type_whnf)?;` (line 95) and the
//       inference Err PROPAGATES (#2208 — pre-fix behavior swallowed it as
//       "not Prop"). The round-1 eta slice (clean_eta_ext_slice.rs [B3])
//       dropped that gate; HERE it is transcribed VERBATIM, together with the
//       full is_prop (tc/infer_proj.rs:382), the strict Prop-validating batch
//       fill `cache_projection_field_types_prop` (tc/infer_proj.rs:315, whose
//       per-field `if !self.is_prop(&domain)?` is a SECOND real propagation
//       site), the non-Prop batch fill `cache_projection_field_types_non_prop`
//       (tc/infer_proj.rs:243), the quick-path `walk_prop_telescope_to_idx`
//       (tc/infer_proj.rs:279), and the strict/quick entry pair
//       `infer_proj_type_from` / `infer_proj_type_from_quick`
//       (tc/infer_proj.rs:47/62). Round-1's [B3] "proj_type_cache modeled out"
//       is DE-MODELED: the batch fills and the top-of-impl cache consult run
//       against a modeled-but-REAL cache (see [C3]).
//
//   (2) the cached whnf_core ROUTING: the tc/ whnf stack transcribed with its
//       REAL cache routing —
//         whnf            (tc/whnf.rs:121  — entry, no extra stack_safe)
//         whnf_impl       (tc/whnf.rs:131  — the already-in-WHNF kind gate
//                          that returns BEFORE any cache consult: Sort / Pi /
//                          Lam / Lit / BVar, and non-let FVar)
//         whnf_inner      (tc/whnf.rs:199  — whnf_cache hit -> return cached;
//                          miss -> whnf_outer_loop; ALWAYS record incl.
//                          identity results (#1584); return)
//         whnf_outer_loop (tc/whnf_proj.rs:161 — Lean 4 type_checker.cpp:659
//                          loop: whnf_core(NoDeltaFullProj) -> reduce_native
//                          -> reduce_nat -> try_monad_reduce -> unfold ->
//                          repeat, INCLUDING the beyond-Lean-4 mid-loop
//                          whnf_cache consult on the delta-unfolded
//                          intermediate (#3210) and the cache RECORD on the
//                          native/nat early returns)
//         whnf_core_inner (tc/whnf.rs:341  — the #20 iterative trampoline)
//         beta_or_iota_step (tc/whnf.rs:536 — multi-arg beta via
//                          instantiate_rev + the stuck-App iota/quot/nat/int/
//                          native dispatch)
//         whnf_recurse    (tc/whnf_proj.rs:38 — Full -> whnf_impl (cached);
//                          NoDelta* -> whnf_core_cache consult (#1768) with
//                          the store-only-on-FullProj discipline)
//         whnf_core_no_delta (tc/whnf.rs:272 — unconditional cache READ,
//                          cheap_proj-gated WRITE: Lean 4 `!cheap_rec &&
//                          !cheap_proj` m_whnf_core guard)
//         whnf_reduce_proj / reduce_proj_with_mode (tc/whnf_proj.rs:22/73 —
//                          incl. the CRITICAL cross-mode escalation: cheap_proj
//                          =false projections re-enter FULL cached whnf_impl on
//                          the struct expression)
//         try_unfold_definition (tc/whnf_proj.rs:223 — head-const delta with
//                          flat arg re-application)
//         unfold_definition_cached (tc/whnf_proj.rs:272 — the m_unfold cache:
//                          hit -> return; miss -> env unfold; ONLY successful
//                          unfolds recorded)
//       The CACHES stay modeled ([C3] below) but every consult/record and its
//       ORDER is the real routing, and the cache KEY discipline is the real
//       Expr::eq (expr/mod.rs:363): full meta-word pre-filter, then derived
//       structural kind equality — transcribed here as expr_eq/kind_eq.
//
// REAL SOURCES TRANSCRIBED (clean @ $HOME/clean/crates/clean-kernel):
//   - tc/infer_proj.rs:47/62/73/243/279/315/357/382 (see above; instantiate_
//     params iterator arg -> prefix-index model, established)
//   - tc/infer.rs:63 pi_domain_body_quick (syntactic-Pi fast path, else whnf
//     then split — transcribed as a method, VERBATIM semantics)
//   - tc/whnf.rs:121/131/199/256(272)/341/536 + tc/whnf_proj.rs:22/38/73/161/
//     223/272 (see above)
//   - expr/mod.rs:363 Expr::PartialEq + expr/kind.rs derived ExprKind
//     PartialEq (expr_eq/kind_eq — the cache-key discipline; ExprMeta::eq is
//     the raw-u64 compare, expr/meta.rs:246)
//   - expr/subst.rs:462 instantiate_rev (multi-arg simultaneous substitution;
//     the MultiInstantiator folder realized as the direct structural recursion
//     it computes — FoldMemo affects sharing, never values)
//   - infer_type / def_eq / instantiate / lift / get_app_fn / get_app_args /
//     construction (from_kind -> compute_meta): the VERIFIED pillar shapes
//     from the prior slices (clean_expr_whnf_slice.rs, clean_expr_infer_
//     slice.rs, clean_eta_ext_slice.rs), retained verbatim.
//
// ── MODELED BOUNDARIES (each also reported in the thread report) ──
// [C1] Environment registries as slice-scans (established [B1]): InductiveVal
//      -> InductiveInfo {name, num_ctors, ctor_name, num_indices,
//      is_recursive}; ConstructorVal -> ConstructorInfo + ctor_types side
//      table; Name = u32 interner handle; delta values in env:
//      &[(Name, Option<Expr>)].
// [C2] level_params modeled ABSENT (established [B2]): infer_proj's
//      level-count gate (infer_proj.rs:150) degenerates to "type head must
//      carry no levels"; env unfolding does no level instantiation.
// [C3] THE CACHES ARE MODELED (the de-modeling target is the ROUTING, not the
//      container): TcHashMap/SlidingCache internals (KaniHasher bucketing, the
//      two-generation current/previous promotion, trim_if_needed eviction,
//      stats) are replaced by an append-only Vec<(Expr, Expr)> scanned
//      linearly. get() compares keys with the REAL Expr::eq (transcribed
//      expr_eq) and returns a clone of the value exactly like
//      SlidingCache::get; insert() appends. Promotion/eviction affect only
//      WHICH entries survive, never the value returned for a present key;
//      trim_if_needed(max_cache_entries) is modeled out (no eviction). The
//      hash is a pure pre-filter in the real map (collisions resolved by eq),
//      so scan-with-eq returns identical values. RefCell interior mutability
//      is threaded as an explicit `&mut TcCaches` parameter — each real
//      borrow_mut() is a confined get/insert, and the threading preserves the
//      exact SEQUENCE of cache operations.
// [C4] heartbeats (inc_heartbeat / heartbeat_exhausted / tick_heartbeat),
//      reduction-stats and debug-whnf idempotency checks modeled out (cfg'd
//      or off in production; the heartbeat-exhausted early bails are
//      unreachable with heartbeats off).
// [C5] stack_safe = identity (stacker growth only); the #20 trampoline's
//      borrow-confined `t_owned`/`&Expr` rebinding transcribed as owned
//      rebinding (same fixpoint); SmallVec<[Expr; 8]> -> Vec<Expr>;
//      checked_add_u32 -> saturating_add (established no-panic model).
// [C6] Reducers modeled inert-None with their call sites (the ROUTING) kept
//      verbatim: reduce_nat / reduce_native / reduce_int / try_monad_reduce
//      (no Nat/Int/native/monad heads in the modeled registry — native_arith
//      verified in the micro rung), try_iota_reduction / try_quot_reduction
//      (no recursors/quotients in the modeled registry — iota/quot verified in
//      prior rounds), the cubical Glue/interval/Sigma/directed consults
//      (CleanMode fixed Classical: the real `mode.has_cubical_layer()` gate is
//      false, the same short-circuit the real hot path takes), the string-lit
//      Proj expansion (Literal::Str is the established u32-interned model —
//      nothing projects out of a string literal here).
// [C7] WhnfMode::WithTransparency + whnf_with_transparency modeled out
//      (elaborator-only entries; the kernel tc path composed here never uses
//      them); LocalContext modeled ABSENT — all FVars non-let (whnf_impl's
//      FVar early return takes the non-let branch; whnf_core_inner's FVar arm
//      sees val_opt = None).
// [C8] the tc quick/full inference pair (try_infer_type_quick /
//      infer_type_infer_only) collapsed to the single modeled inference
//      (established composite [B3]); infer_only's skip-arg-checks distinction
//      is inert on the harness registry (all decl types well-typed). The `?`
//      Err-propagation of is_prop (#2208) is REAL and is the surface under
//      test.
// [C9] TypeError payloads: Box<Expr> payloads dropped (Box::new frontend gap),
//      usize count payloads narrowed to u32; variant IDENTITY and scalar
//      payloads (Name / indices) preserved and differentially compared.
// [C10] def_eq here is the SUPPORTING pillar for infer's App-arg checks
//      (exercised only on Sort/Const pairs by this harness); the eta/
//      struct-eta composition is verified in round-1/T2 and NOT re-verified
//      here (its fallback arms are omitted from this def_eq shape). def-eq's
//      structural_eq deliberately ignores BinderData (kernel def-eq
//      semantics) — DISTINCT from expr_eq (cache-key equality) which compares
//      BinderData and the meta word like the real derived PartialEq.
// [C11] `for` loops -> while; let-else / matches! / `?`-on-Option -> match
//      (established B6 frontend-surface rewrites; semantics preserved).
//
// Crate name is load-bearing (mangled into the extern-leaf symbols the JIT
// binds), so it MUST stay `clean_tc_stitch_slice`.
//
// EMIT (two closures from this one slice):
//   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//   cd $HOME/trust-ir/frontend
//   env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//     $S/bin/cargo run --bin trust_ir_mir -- clean_tc_stitch_slice.rs \
//       --crate-type=lib --mir-emit-closure tc_proj_root <out1.tir>
//   .. and the same with --mir-emit-closure tc_whnf_route_root <out2.tir>
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
    pub fn succ(l: Level) -> Level { Level::Succ(Box::new(l)) }
    pub fn imax(u: Level, v: Level) -> Level {
        if Level::is_zero(&v) { return Level::Zero; }
        Level::max(u, v)
    }
    pub fn is_zero(l: &Level) -> bool { matches!(l, Level::Zero) }
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

pub struct KaniHasher { pub state: u64 }
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
pub struct ExprMeta(pub u64);

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
    pub fn raw(self) -> u64 { self.0 }
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
pub struct Expr { pub kind: ExprKind, pub meta: ExprMeta }

impl Expr {
    fn from_kind(kind: ExprKind) -> Self { let meta = kind.compute_meta(); Expr { kind, meta } }
    fn meta(&self) -> ExprMeta { self.meta }
    fn kind(&self) -> &ExprKind { &self.kind }
    fn loose_bvar_range(&self) -> u32 { self.meta.loose_bvar_range() }
    // VERBATIM Expr::has_loose_bvars (meta-cached O(1) read).
    fn has_loose_bvars(&self) -> bool { self.loose_bvar_range() > 0 }
    // VERBATIM expr/constructors.rs:218/228 is_app / is_lam.
    fn is_app(&self) -> bool { matches!(&self.kind, ExprKind::App(..)) }
    fn is_lam(&self) -> bool { matches!(&self.kind, ExprKind::Lam(..)) }
    pub fn bvar(idx: u32) -> Self { Expr::from_kind(ExprKind::BVar(idx)) }
    pub fn cnst(name: Name) -> Self { Expr::from_kind(ExprKind::Const(name, Vec::new())) }
    pub fn const_(name: Name, levels: LevelVec) -> Self { Expr::from_kind(ExprKind::Const(name, levels)) }
    pub fn sort0() -> Self { Expr::from_kind(ExprKind::Sort(Level::Zero)) }
    pub fn sort(l: Level) -> Self { Expr::from_kind(ExprKind::Sort(l)) }
    pub fn nat(n: u64) -> Self { Expr::from_kind(ExprKind::Lit(Literal::Nat(n))) }
    pub fn app(func: Expr, arg: Expr) -> Self { Expr::from_kind(ExprKind::App(Arc::new(func), Arc::new(arg))) }
    pub fn lam(bd: BinderData, ty: Expr, body: Expr) -> Self { Expr::from_kind(ExprKind::Lam(bd, Arc::new(ty), Arc::new(body))) }
    pub fn pi(bd: BinderData, ty: Expr, body: Expr) -> Self { Expr::from_kind(ExprKind::Pi(bd, Arc::new(ty), Arc::new(body))) }
    pub fn lett(name: Name, ty: Expr, val: Expr, body: Expr, nondep: bool) -> Self { Expr::from_kind(ExprKind::Let(name, Arc::new(ty), Arc::new(val), Arc::new(body), nondep)) }
    pub fn proj(name: Name, idx: u32, e: Expr) -> Self { Expr::from_kind(ExprKind::Proj(name, idx, Arc::new(e))) }
    pub fn mdata(tag: u32, e: Expr) -> Self { Expr::from_kind(ExprKind::MData(tag, Arc::new(e))) }

    // VERBATIM lift_at (the VERIFIED construction pillar, reused; established
    // arm set — Let/Proj wrapped values never lifted on harness inputs).
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
    // instantiate_rev — VERBATIM expr/subst.rs:462: substitute BVar(0)..
    // BVar(n-1) with vals[0]..vals[n-1] simultaneously (vals[i] lifted by the
    // binder depth; BVars >= depth+n shifted down by n). The MultiInstantiator
    // folder (subst.rs:131) is realized as the direct structural recursion it
    // computes: FoldMemo memoization affects SHARING, never values [C5]; the
    // should_descend gate `depth < loose_bvar_range()` is the top early
    // return; checked_add_u32 -> saturating_add [C5]. Arm set mirrors the
    // established instantiate_at pillar.
    fn instantiate_rev(&self, vals: &[Expr]) -> Expr {
        if vals.is_empty() { return self.clone(); }
        if vals.len() == 1 { return self.instantiate(&vals[0]); }
        self.instantiate_rev_at(vals, 0)
    }
    fn instantiate_rev_at(&self, vals: &[Expr], depth: u32) -> Expr {
        if depth >= self.loose_bvar_range() { return self.clone(); }
        let n = vals.len() as u32;
        match &self.kind {
            ExprKind::BVar(idx) => {
                if *idx >= depth && *idx < depth.saturating_add(n) {
                    // BVar(depth+i) -> vals[i], lifted by depth
                    let i = (*idx - depth) as usize;
                    vals[i].lift_at(0, depth)
                } else if *idx >= depth.saturating_add(n) {
                    // BVar above the substituted range: shift down by n
                    Expr::bvar(*idx - n)
                } else {
                    // BVar below depth: unchanged
                    self.clone()
                }
            }
            ExprKind::App(f, a) => Expr::app(f.instantiate_rev_at(vals, depth), a.instantiate_rev_at(vals, depth)),
            ExprKind::Lam(bd, ty, body) => Expr::lam(*bd, ty.instantiate_rev_at(vals, depth), body.instantiate_rev_at(vals, depth.saturating_add(1))),
            ExprKind::Pi(bd, ty, body) => Expr::pi(*bd, ty.instantiate_rev_at(vals, depth), body.instantiate_rev_at(vals, depth.saturating_add(1))),
            ExprKind::Let(name, ty, val_e, body, nondep) => Expr::lett(*name, ty.instantiate_rev_at(vals, depth), val_e.instantiate_rev_at(vals, depth), body.instantiate_rev_at(vals, depth.saturating_add(1)), *nondep),
            ExprKind::Proj(name, idx, e) => Expr::proj(*name, *idx, e.instantiate_rev_at(vals, depth)),
            _ => self.clone(),
        }
    }
    // VERBATIM get_app_fn / get_app_args (the VERIFIED App-spine pillar).
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

// ─────────────── expr_eq — the REAL Expr::eq (the cache-KEY discipline) ─────
// VERBATIM expr/mod.rs:363: full meta-word pre-filter (ExprMeta::eq is the
// raw u64 compare, expr/meta.rs:246), then structural kind equality — the
// derived ExprKind PartialEq (expr/kind.rs:117), which recurses through
// Arc<Expr> -> Expr::eq at EVERY node (so the meta filter applies at every
// level) and compares BinderData / Name / levels / literals / the MData tag.
// This is the equality the real TcHashMap resolves hash buckets with; the
// modeled cache scans with it directly [C3].

pub fn expr_eq(a: &Expr, b: &Expr) -> bool {
    // Metadata pre-filter: reject mismatches in O(1) using the full cached
    // metadata word (hash/depth/flags/loose_bvar_range).
    if a.meta.raw() != b.meta.raw() {
        return false;
    }
    // Fall back to structural equality (required for correctness since
    // hash collisions are possible with 32-bit hash)
    kind_eq(&a.kind, &b.kind)
}

fn level_seq(a: &Level, b: &Level) -> bool {
    // derived Level PartialEq, written out (in-module leaf set).
    match (a, b) {
        (Level::Zero, Level::Zero) => true,
        (Level::Succ(x), Level::Succ(y)) => level_seq(x, y),
        (Level::Param(x), Level::Param(y)) => x.0 == y.0,
        _ => false,
    }
}

fn level_vec_seq(a: &[Level], b: &[Level]) -> bool {
    if a.len() != b.len() { return false; }
    let mut i: usize = 0;
    let n = a.len();
    while i < n { if !level_seq(&a[i], &b[i]) { return false; } i += 1; }
    true
}

fn lit_seq(a: &Literal, b: &Literal) -> bool {
    match (a, b) {
        (Literal::Nat(x), Literal::Nat(y)) => x == y,
        (Literal::Str(x), Literal::Str(y)) => x == y,
        _ => false,
    }
}

fn kind_eq(a: &ExprKind, b: &ExprKind) -> bool {
    match (a, b) {
        (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
        (ExprKind::FVar(i), ExprKind::FVar(j)) => i.0 == j.0,
        (ExprKind::Sort(l1), ExprKind::Sort(l2)) => level_seq(l1, l2),
        (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => n1.0 == n2.0 && level_vec_seq(ls1, ls2),
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => expr_eq(f1, f2) && expr_eq(a1, a2),
        (ExprKind::Lam(b1, t1, y1), ExprKind::Lam(b2, t2, y2)) => b1.info == b2.info && b1.mult == b2.mult && expr_eq(t1, t2) && expr_eq(y1, y2),
        (ExprKind::Pi(b1, t1, y1), ExprKind::Pi(b2, t2, y2)) => b1.info == b2.info && b1.mult == b2.mult && expr_eq(t1, t2) && expr_eq(y1, y2),
        (ExprKind::Let(n1, t1, v1, y1, d1), ExprKind::Let(n2, t2, v2, y2, d2)) => n1.0 == n2.0 && expr_eq(t1, t2) && expr_eq(v1, v2) && expr_eq(y1, y2) && d1 == d2,
        (ExprKind::Lit(l1), ExprKind::Lit(l2)) => lit_seq(l1, l2),
        (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => n1.0 == n2.0 && i1 == i2 && expr_eq(e1, e2),
        (ExprKind::MData(m1, e1), ExprKind::MData(m2, e2)) => m1 == m2 && expr_eq(e1, e2),
        _ => false,
    }
}

// ─────────────── TcCaches — the modeled tc caches [C3] ──────────────────────
// One field per real TypeChecker cache composed here:
//   whnf   — tc/mod.rs:323  whnf_cache      (Lean 4 m_whnf)
//   core   — tc/mod.rs:337  whnf_core_cache (Lean 4 m_whnf_core)
//   unfold — tc/mod.rs      unfold_cache    (Lean 4 m_unfold)
//   proj   — tc/mod.rs:439  proj_type_cache
// Append-only Vec<(key, value)>; get scans with the REAL expr_eq and clones
// the value (exactly SlidingCache::get's return); insert appends;
// trim_if_needed modeled out [C3].
// BOUNDARY NUANCE [C3]: the model is APPEND-ONLY with FIRST-MATCH-WINS reads
// (no key-overwrite semantics of the real SlidingCache::insert) — so a buggy
// EXTRA write is observable via entry COUNT (packed lens) or a scan for a key
// no other site writes, never via read-back of an already-present key.

pub struct TcCaches {
    pub whnf: Vec<(Expr, Expr)>,
    pub core: Vec<(Expr, Expr)>,
    pub unfold: Vec<(Expr, Expr)>,
    pub proj: Vec<(Expr, Expr)>,
}

pub fn caches_new() -> TcCaches {
    TcCaches { whnf: Vec::new(), core: Vec::new(), unfold: Vec::new(), proj: Vec::new() }
}

pub fn cache_get(cache: &Vec<(Expr, Expr)>, key: &Expr) -> Option<Expr> {
    let mut i: usize = 0;
    let n = cache.len();
    while i < n {
        let entry = &cache[i];
        if expr_eq(&entry.0, key) { return Some(entry.1.clone()); }
        i += 1;
    }
    None
}

pub fn cache_insert(cache: &mut Vec<(Expr, Expr)>, key: Expr, value: Expr) {
    cache.push((key, value));
}

fn pack_lens(caches: &TcCaches) -> u64 {
    let p = caches.proj.len() as u64;
    let w = caches.whnf.len() as u64;
    let c = caches.core.len() as u64;
    let u = caches.unfold.len() as u64;
    (p << 48) | (w << 32) | (c << 16) | u
}

// ─────────────── WhnfMode / WhnfStepResult (tc/whnf.rs:36/59) ────────────────
// WithTransparency modeled out [C7] — elaborator-only entry.

#[derive(Clone, Copy)]
pub enum WhnfMode {
    /// Full delta at Default transparency. Projection recursion goes through
    /// `whnf_impl` (cached). Previously: `whnf_core`.
    Full,
    /// No delta reduction with cheap projection recursion.
    /// Used by `is_def_eq_core` Phase 1 and `lazy_delta_reduction`.
    NoDeltaCheapProj,
    /// No delta reduction with full no-delta projection recursion.
    /// Used by `is_def_eq_core` Phase 5.
    NoDeltaFullProj,
}

impl WhnfMode {
    // VERBATIM tc/whnf.rs:83 — all current modes use full whnf on the
    // recursor major premise / quot lift argument (#1484 parity analysis).
    fn use_delta_for_iota(self) -> bool {
        true
    }
}

enum WhnfStepResult {
    /// Term is in weak-head normal form; stop and return it.
    Done(Expr),
    /// Term head-reduced; continue the trampoline on this new term.
    Continue(Expr),
}

// ───────────────────────── TypeError [C9] ────────────────────────────────────

#[derive(Clone, Debug)]
pub enum TypeError {
    UnboundVariable(u32),
    UnknownConst(Name),
    TypeMismatch { expected: Arc<Expr>, inferred: Arc<Expr> },
    NotAPi { ty: Arc<Expr> },
    ExpectedSort { ty: Arc<Expr> },
    /// real: InvalidProjNotStruct(Box<Expr>) — Box payload dropped [C9]
    InvalidProjNotStruct,
    UnknownInductive(Name),
    InvalidProjNotUniqueConstructor(Name),
    InvalidProjIndexOutOfBounds(u32, u32),
    /// real: LevelCountMismatch {name, expected, got} — counts dropped [C9]
    LevelCountMismatch(Name),
    /// real: InvalidProjWrongArgCount {got, expected, num_params, num_indices}
    /// — narrowed to (got, expected) as u32 [C9]
    InvalidProjWrongArgCount(u32, u32),
    InvalidProjFromProp(u32),
    Unsupported,
}

pub fn err_code(e: &TypeError) -> i32 {
    match e {
        TypeError::UnboundVariable(_) => -1,
        TypeError::UnknownConst(_) => -2,
        TypeError::TypeMismatch { .. } => -3,
        TypeError::NotAPi { .. } => -4,
        TypeError::ExpectedSort { .. } => -5,
        TypeError::InvalidProjNotStruct => -6,
        TypeError::UnknownInductive(_) => -7,
        TypeError::InvalidProjNotUniqueConstructor(_) => -8,
        TypeError::InvalidProjIndexOutOfBounds(_, _) => -9,
        TypeError::LevelCountMismatch(_) => -10,
        TypeError::InvalidProjWrongArgCount(_, _) => -11,
        TypeError::InvalidProjFromProp(_) => -12,
        TypeError::Unsupported => -13,
    }
}

pub fn err_payload(e: &TypeError) -> u64 {
    match e {
        TypeError::UnboundVariable(i) => *i as u64,
        TypeError::UnknownConst(n) => n.0 as u64,
        TypeError::UnknownInductive(n) => n.0 as u64,
        TypeError::InvalidProjNotUniqueConstructor(n) => n.0 as u64,
        TypeError::InvalidProjIndexOutOfBounds(i, n) => ((*i as u64) << 32) | (*n as u64),
        TypeError::LevelCountMismatch(n) => n.0 as u64,
        TypeError::InvalidProjWrongArgCount(got, expected) => ((*got as u64) << 32) | (*expected as u64),
        TypeError::InvalidProjFromProp(i) => *i as u64,
        _ => 0,
    }
}

// ─────────────── InductiveInfo / ConstructorInfo (registry model [C1]) ───────

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

// ═══════════════════════ CertVerifier (the modeled Environment) ═════════════

pub struct CertVerifier<'env> {
    pub env: &'env [(Name, Option<Expr>)],
    pub ctor_np: &'env [(Name, u32)],
    pub decl_types: &'env [(Name, Expr)],
    pub ctor_types: &'env [(Name, Expr)],
    pub inductives: &'env [InductiveInfo],
    pub ctors: &'env [ConstructorInfo],
}

impl<'env> CertVerifier<'env> {
    // ── registry lookups (slice-scan model of Environment.get_*) [C1] ──
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
        None
    }
    // ConstructorVal.type_ (modeled as a side table keyed by ctor name [C1]).
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

    // ── inert reducers [C6] — call sites (the ROUTING) kept verbatim ──
    fn reduce_nat(&self, _e: &Expr) -> Option<Expr> { None }
    fn reduce_native(&self, _e: &Expr) -> Option<Expr> { None }
    fn reduce_int(&self, _e: &Expr) -> Option<Expr> { None }
    fn try_monad_reduce(&self, _e: &Expr) -> Option<Expr> { None }
    fn try_iota_reduction(&self, _e: &Expr, _use_delta: bool) -> Option<Expr> { None }
    fn try_quot_reduction(&self, _e: &Expr, _use_delta: bool) -> Option<Expr> { None }

    // ══════════════════════════════════════════════════════════════════════
    // THE CACHED WHNF STACK (target 2) — transcribed routing
    // ══════════════════════════════════════════════════════════════════════

    // whnf — VERBATIM tc/whnf.rs:121. No stack_safe here — whnf_impl already
    // wraps its inner call, and all recursive paths go through whnf_impl [C5].
    pub fn whnf(&self, e: &Expr, caches: &mut TcCaches) -> Expr {
        self.whnf_impl(e, caches)
    }

    // whnf_impl — VERBATIM tc/whnf.rs:131. Lean 4 parity: skip cache /
    // whnf_core ENTIRELY for kinds already in WHNF (type_checker.cpp:639-656):
    // BVar, Sort, Pi, Lit, Lam, and non-let FVar return BEFORE the cache is
    // consulted (#3210). Heartbeat tick + exhausted early-bail modeled out
    // [C4]; LocalContext modeled absent => every FVar is non-let [C7];
    // stack_safe = identity [C5].
    pub fn whnf_impl(&self, e: &Expr, caches: &mut TcCaches) -> Expr {
        match &e.kind {
            ExprKind::Sort(_)
            | ExprKind::Pi(..)
            | ExprKind::Lam(..)
            | ExprKind::Lit(_)
            | ExprKind::BVar(_) => return e.clone(),
            ExprKind::FVar(_) => {
                // Only skip for non-let FVars — ctx modeled absent [C7], so
                // is_let = false and the early return is taken.
                return e.clone();
            }
            _ => {}
        }
        // [inc_heartbeat + heartbeat_exhausted early bail modeled out — C4]
        self.whnf_inner(e, caches)
    }

    // whnf_inner — VERBATIM tc/whnf.rs:199: the whnf_cache routing.
    // hit -> return cached; miss -> whnf_outer_loop; ALWAYS record the result
    // including identity results (#1584); sliding-window trim modeled out [C3].
    fn whnf_inner(&self, e: &Expr, caches: &mut TcCaches) -> Expr {
        // Check cache first (borrow_mut for SlidingCache promotion on hit)
        if let Some(cached) = cache_get(&caches.whnf, e) {
            return cached;
        }
        let result = self.whnf_outer_loop(e, caches);
        // [debug-whnf idempotency check cfg'd out — C4]
        // Cache all WHNF results including identity — prevents O(n^2+)
        // re-traversal on stuck app chains (axiom/opaque head). Matches
        // Lean 4. See #1584.
        cache_insert(&mut caches.whnf, e.clone(), result.clone());
        result
    }

    // whnf_outer_loop — VERBATIM tc/whnf_proj.rs:161 (Lean 4
    // type_checker.cpp:659-681): whnf_core(no-delta) -> reduce_native ->
    // reduce_nat -> try_monad_reduce -> unfold_definition -> repeat, with the
    // beyond-Lean-4 mid-loop whnf_cache consult on the delta-unfolded
    // intermediate (#3210). heartbeat_exhausted bail + inc_heartbeat modeled
    // out [C4]; the reducers are inert-None [C6] (their record-and-return
    // branches are transcribed and compiled, dead on this registry).
    fn whnf_outer_loop(&self, e: &Expr, caches: &mut TcCaches) -> Expr {
        let mut t = e.clone();
        loop {
            let t1 = self.whnf_core_inner(&t, WhnfMode::NoDeltaFullProj, caches);

            if let Some(reduced) = self.reduce_native(&t1) {
                cache_insert(&mut caches.whnf, e.clone(), reduced.clone());
                return reduced;
            }

            if let Some(reduced) = self.reduce_nat(&t1) {
                cache_insert(&mut caches.whnf, e.clone(), reduced.clone());
                return reduced;
            }

            // Lazy monadic reduction (#3401) [C6 inert].
            if let Some(reduced) = self.try_monad_reduce(&t1) {
                if expr_eq(&reduced, &t1) {
                    return reduced;
                }
                if let Some(cached) = cache_get(&caches.whnf, &reduced) {
                    return cached;
                }
                t = reduced;
                continue;
            }

            if let Some(unfolded) = self.try_unfold_definition(&t1, caches) {
                // [inc_heartbeat modeled out — C4]
                // Check whnf_cache for the intermediate expression after delta
                // unfolding. If this expression was already fully WHNF'd in a
                // prior call, skip the remaining loop iterations entirely.
                // Optimization beyond Lean 4 (#3210).
                if let Some(cached) = cache_get(&caches.whnf, &unfolded) {
                    return cached;
                }
                t = unfolded;
                continue;
            }

            return t1;
        }
    }

    // whnf_core_no_delta — VERBATIM tc/whnf.rs:272. Cache READ is
    // unconditional (cheap-mode calls reuse full-mode results — strictly more
    // reduced, safe; #1768). Cache WRITE only when cheap_proj = false —
    // Lean 4's `!cheap_rec && !cheap_proj` m_whnf_core guard (clean always
    // has cheap_rec = false). stack_safe = identity [C5].
    pub fn whnf_core_no_delta(&self, e: &Expr, cheap_proj: bool, caches: &mut TcCaches) -> Expr {
        if let Some(cached) = cache_get(&caches.core, e) {
            return cached;
        }
        let mode = if cheap_proj { WhnfMode::NoDeltaCheapProj } else { WhnfMode::NoDeltaFullProj };
        let result = self.whnf_core_inner(e, mode, caches);
        if !cheap_proj {
            cache_insert(&mut caches.core, e.clone(), result.clone());
        }
        result
    }

    // whnf_core_inner — VERBATIM tc/whnf.rs:341: the #20 iterative WHNF
    // trampoline (tail head-reduction continuations rebind and loop instead of
    // native recursion — transcribed as owned rebinding [C5]; identical
    // fixpoint). Cubical/glue consults short-circuit on Classical mode [C6];
    // WithTransparency arm modeled out [C7]; FVar arm sees no let-value [C7].
    fn whnf_core_inner(&self, e: &Expr, mode: WhnfMode, caches: &mut TcCaches) -> Expr {
        let mut t: Expr = e.clone();
        loop {
            let step: WhnfStepResult = match &t.kind {
                ExprKind::App(..) => {
                    // Pre-check: try Nat/native reduction on the full
                    // expression BEFORE delta-unfolding the function head
                    // (#3134). Only when the head is a visible Const.
                    let f0 = t.get_app_fn();
                    let head_is_const = matches!(&f0.kind, ExprKind::Const(_, _));
                    if head_is_const {
                        // [cubical Glue/interval/Sigma/directed consults
                        //  modeled out — Classical mode short-circuits the
                        //  has_cubical_layer() gate, C6]
                        if let Some(reduced) = self.reduce_nat(&t) {
                            WhnfStepResult::Continue(reduced)
                        } else if let Some(reduced) = self.reduce_native(&t) {
                            WhnfStepResult::Continue(reduced)
                        } else {
                            self.beta_or_iota_step(&t, &f0, mode, caches)
                        }
                    } else {
                        self.beta_or_iota_step(&t, &f0, mode, caches)
                    }
                }
                ExprKind::Let(_, _, val, body, _) => {
                    WhnfStepResult::Continue(body.instantiate(val))
                }
                ExprKind::Const(_name, _levels) => {
                    // Delta-unfold the head constant, then loop (tail
                    // continuation) without growing the native stack.
                    match mode {
                        WhnfMode::NoDeltaCheapProj | WhnfMode::NoDeltaFullProj => {
                            WhnfStepResult::Done(t.clone())
                        }
                        WhnfMode::Full => match self.unfold_definition_cached(&t, caches) {
                            Some(val) => WhnfStepResult::Continue(val),
                            None => WhnfStepResult::Done(t.clone()),
                        },
                        // WithTransparency arm modeled out [C7]
                    }
                }
                ExprKind::FVar(_) => {
                    // [ctx modeled absent => val_opt = None — C7]
                    WhnfStepResult::Done(t.clone())
                }
                ExprKind::Proj(struct_name, idx, expr) => {
                    WhnfStepResult::Done(self.whnf_reduce_proj(struct_name, *idx, expr, mode, caches))
                }
                ExprKind::MData(_, inner) => WhnfStepResult::Continue(inner.as_ref().clone()),
                // [Cubical PathApp/Coe/Transp/HComp arms absent — no cubical
                //  variants in the modeled ExprKind, C6]
                _ => WhnfStepResult::Done(t.clone()),
            };
            match step {
                WhnfStepResult::Done(result) => return result,
                WhnfStepResult::Continue(next) => {
                    t = next;
                }
            }
        }
    }

    // beta_or_iota_step — VERBATIM tc/whnf.rs:536: multi-argument beta
    // (Lean 4 type_checker.cpp:443-471, #3210) via instantiate_rev, else the
    // stuck-App iota/quot/nat/int/native dispatch. SmallVec -> Vec [C5];
    // `f == *f0` is the REAL Expr::eq (expr_eq).
    fn beta_or_iota_step(&self, e: &Expr, f0: &Expr, mode: WhnfMode, caches: &mut TcCaches) -> WhnfStepResult {
        let f = self.whnf_recurse(f0, mode, caches);
        if f.is_lam() {
            // Collect the spine args only in the branches that consume them.
            let args = e.get_app_args();
            // Count how many nested lambdas we can consume
            let num_args = args.len();
            let mut body: Expr = f.clone();
            let mut m: usize = 0;
            loop {
                let body_is_lam = matches!(&body.kind, ExprKind::Lam(..));
                if !body_is_lam { break; }
                m += 1;
                if m >= num_args { break; }
                let next = match &body.kind {
                    ExprKind::Lam(_, _, inner) => inner.as_ref().clone(),
                    _ => break,
                };
                body = next;
            }
            // body is now the innermost consumed lambda; extract its body.
            // (The non-Lam fallback "shouldn't happen but handle gracefully"
            // branch of the real code.)
            let inner_body: Expr = match &body.kind {
                ExprKind::Lam(_, _, b) => b.as_ref().clone(),
                _ => body.clone(),
            };

            // vals[i] = args[m-1-i]: BVar(0) = last consumed arg (innermost).
            let mut vals: Vec<Expr> = Vec::new();
            let mut i: usize = 0;
            while i < m {
                vals.push(args[m - 1 - i].clone());
                i += 1;
            }

            let mut reduced = inner_body.instantiate_rev(&vals);

            // Apply remaining args (if any) that weren't consumed by lambdas
            let mut j: usize = m;
            while j < num_args {
                reduced = Expr::app(reduced, args[j].clone());
                j += 1;
            }

            WhnfStepResult::Continue(reduced)
        } else {
            // Head didn't reduce to a lambda — rebuild App and try
            // iota/quot/nat/int/native
            let app_with_whnf = if expr_eq(&f, f0) {
                e.clone()
            } else {
                // Rebuild application with reduced head (args needed only here).
                let args = e.get_app_args();
                let mut result = f;
                let mut i: usize = 0;
                while i < args.len() {
                    result = Expr::app(result, args[i].clone());
                    i += 1;
                }
                result
            };
            let use_delta = mode.use_delta_for_iota();
            if let Some(reduced) = self.try_iota_reduction(&app_with_whnf, use_delta) {
                WhnfStepResult::Continue(reduced)
            } else if let Some(reduced) = self.try_quot_reduction(&app_with_whnf, use_delta) {
                WhnfStepResult::Continue(reduced)
            } else if let Some(reduced) = self.reduce_nat(&app_with_whnf) {
                WhnfStepResult::Continue(reduced)
            } else if let Some(reduced) = self.reduce_int(&app_with_whnf) {
                WhnfStepResult::Continue(reduced)
            } else if let Some(reduced) = self.reduce_native(&app_with_whnf) {
                WhnfStepResult::Continue(reduced)
            } else {
                WhnfStepResult::Done(app_with_whnf)
            }
        }
    }

    // whnf_recurse — VERBATIM tc/whnf_proj.rs:38: mode-dispatched recursive
    // WHNF. Full -> whnf_impl (the CACHED layer); NoDelta* -> whnf_core_cache
    // consult (#1768) then compute, store only in full-proj mode (Lean 4:
    // !cheap_rec && !cheap_proj). WithTransparency modeled out [C7].
    fn whnf_recurse(&self, e: &Expr, mode: WhnfMode, caches: &mut TcCaches) -> Expr {
        match mode {
            WhnfMode::Full => self.whnf_impl(e, caches),
            WhnfMode::NoDeltaCheapProj | WhnfMode::NoDeltaFullProj => {
                if let Some(cached) = cache_get(&caches.core, e) {
                    return cached;
                }
                let result = self.whnf_core_inner(e, mode, caches);
                let store = matches!(mode, WhnfMode::NoDeltaFullProj);
                if store {
                    cache_insert(&mut caches.core, e.clone(), result.clone());
                }
                result
            }
        }
    }

    // whnf_reduce_proj / reduce_proj_with_mode — VERBATIM tc/whnf_proj.rs:22/73
    // (Lean 4 reduce_proj, type_checker.cpp:375-386): cheap_proj=true recurses
    // no-delta; cheap_proj=false and Full use FULL cached whnf_impl on the
    // struct expression (the critical cross-mode escalation — instance
    // constants must delta-unfold to constructor form). The string-literal
    // expansion arm is modeled out [C6]. Lean 4 parity (#3209): the ctor's
    // inductive is NOT checked against the Proj's struct name — only
    // is_constructor and field bounds.
    fn whnf_reduce_proj(&self, struct_name: &Name, idx: u32, expr: &Expr, mode: WhnfMode, caches: &mut TcCaches) -> Expr {
        self.reduce_proj_with_mode(struct_name, idx, expr, mode, caches)
    }
    fn reduce_proj_with_mode(&self, struct_name: &Name, idx: u32, expr: &Expr, mode: WhnfMode, caches: &mut TcCaches) -> Expr {
        let proj_whnf = match mode {
            WhnfMode::NoDeltaCheapProj => {
                // Cheap projection: no delta on inner expression
                self.whnf_recurse(expr, mode, caches)
            }
            WhnfMode::NoDeltaFullProj | WhnfMode::Full => {
                // Full projection: full WHNF (including delta) on the inner
                // expression — matches Lean 4's `whnf(proj_expr(e))` for
                // cheap_proj=false
                self.whnf_impl(expr, caches)
            }
        };

        // [string-literal -> constructor expansion arm modeled out — C6]

        let head = proj_whnf.get_app_fn();
        if let ExprKind::Const(ctor_name, _) = &head.kind {
            if let Some(num_params) = self.get_constructor_num_params(ctor_name) {
                let field_idx = (num_params as usize).saturating_add(idx as usize);
                let args = proj_whnf.get_app_args();
                if field_idx < args.len() {
                    // Re-enter WHNF on the extracted field
                    return self.whnf_recurse(&args[field_idx], mode, caches);
                }
            }
        }

        Expr::proj(*struct_name, idx, proj_whnf)
    }

    // try_unfold_definition — VERBATIM tc/whnf_proj.rs:223 (Lean 4
    // unfold_definition_core, type_checker.cpp:521-532). The CubicalPathApp
    // arm is absent [C6]; `?` on Option -> match [C11]; `for` -> while [C11].
    fn try_unfold_definition(&self, e: &Expr, caches: &mut TcCaches) -> Option<Expr> {
        let head = e.get_app_fn();
        let head_is_const = matches!(&head.kind, ExprKind::Const(_, _));
        if head_is_const {
            let value = match self.unfold_definition_cached(&head, caches) {
                Some(v) => v,
                None => return None,
            };
            if e.is_app() {
                let args = e.get_app_args();
                let mut result = value;
                let mut i: usize = 0;
                while i < args.len() {
                    result = Expr::app(result, args[i].clone());
                    i += 1;
                }
                Some(result)
            } else {
                Some(value)
            }
        } else {
            None
        }
    }

    // unfold_definition_cached — VERBATIM tc/whnf_proj.rs:272 (Lean 4 m_unfold,
    // type_checker.h:31): hit -> return cached; miss -> env unfold + record.
    // ONLY successful unfolds are cached (axioms/opaque consts are not — the
    // env lookup is cheap). Level instantiation modeled absent [C2]; let-else
    // -> match [C11].
    fn unfold_definition_cached(&self, const_expr: &Expr, caches: &mut TcCaches) -> Option<Expr> {
        if let Some(cached) = cache_get(&caches.unfold, const_expr) {
            return Some(cached);
        }

        let name: Name = match &const_expr.kind {
            ExprKind::Const(name, _levels) => *name,
            _ => return None,
        };

        let value = match self.unfold_const(&name) {
            Some(v) => v,
            None => return None,
        };

        cache_insert(&mut caches.unfold, const_expr.clone(), value.clone());

        Some(value)
    }

    // ══════════════════════════════════════════════════════════════════════
    // DEF-EQ pillar [C10] — supporting shape for infer's App-arg checks.
    // The VERIFIED structural def_eq from the prior slices, now running over
    // the CACHED whnf. Eta/struct-eta fallback arms omitted (verified in
    // round-1/T2; unreachable on this harness's Sort/Const comparisons).
    // ══════════════════════════════════════════════════════════════════════
    fn level_eq(&self, l1: &Level, l2: &Level) -> bool { level_seq(l1, l2) }
    fn level_vec_eq(&self, ls1: &[Level], ls2: &[Level]) -> bool { level_vec_seq(ls1, ls2) }
    fn structural_eq(&self, a: &Expr, b: &Expr) -> bool {
        // def-eq's structural compare: BinderData deliberately NOT compared
        // (kernel def-eq semantics) — distinct from expr_eq [C10].
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
    fn is_def_eq(&self, a: &Expr, b: &Expr, caches: &mut TcCaches) -> bool { self.def_eq_inner(a, b, caches) }
    fn def_eq_impl(&self, a: &Expr, b: &Expr, caches: &mut TcCaches) -> bool { self.def_eq_inner(a, b, caches) }
    fn def_eq_inner(&self, a: &Expr, b: &Expr, caches: &mut TcCaches) -> bool {
        let a_whnf = self.whnf_impl(a, caches);
        let b_whnf = self.whnf_impl(b, caches);
        if a_whnf.meta.raw() == b_whnf.meta.raw() && self.structural_eq(&a_whnf, &b_whnf) {
            return true;
        }
        match (&a_whnf.kind, &b_whnf.kind) {
            (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
            (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => self.level_eq(l1, l2),
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => n1 == n2 && self.level_vec_eq(ls1, ls2),
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => self.def_eq_impl(f1, f2, caches) && self.def_eq_impl(a1, a2, caches),
            (ExprKind::Lam(_b1, ty1, b1), ExprKind::Lam(_b2, ty2, b2))
            | (ExprKind::Pi(_b1, ty1, b1), ExprKind::Pi(_b2, ty2, b2)) => self.def_eq_impl(ty1, ty2, caches) && self.def_eq_impl(b1, b2, caches),
            (ExprKind::Let(_, ty1, v1, b1, _), ExprKind::Let(_, ty2, v2, b2, _)) => self.def_eq_impl(ty1, ty2, caches) && self.def_eq_impl(v1, v2, caches) && self.def_eq_impl(b1, b2, caches),
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => n1 == n2 && i1 == i2 && self.def_eq_impl(e1, e2, caches),
            (ExprKind::MData(_, in1), ExprKind::MData(_, in2)) => self.def_eq_impl(in1, in2, caches),
            (ExprKind::Lam(..), _) | (_, ExprKind::Lam(..)) => self.try_eta_expansion(&a_whnf, &b_whnf, caches),
            _ => false,
        }
    }
    // function-eta (the VERIFIED cert eta template — established boundary).
    fn try_eta_expansion(&self, a: &Expr, b: &Expr, caches: &mut TcCaches) -> bool {
        match (&a.kind, &b.kind) {
            (ExprKind::Lam(_, _ty, body), _) => {
                let other_lifted = b.lift_from(0, 1);
                let other_applied = Expr::app(other_lifted, Expr::bvar(0));
                self.def_eq_impl(body, &other_applied, caches)
            }
            (_, ExprKind::Lam(_, _ty, body)) => {
                let other_lifted = a.lift_from(0, 1);
                let other_applied = Expr::app(other_lifted, Expr::bvar(0));
                self.def_eq_impl(body, &other_applied, caches)
            }
            _ => false,
        }
    }

    // ══════════════════════════════════════════════════════════════════════
    // INFER-TYPE pillar (tc/infer.rs) — VERIFIED shape, over the CACHED whnf.
    // ══════════════════════════════════════════════════════════════════════
    pub fn infer_type(&self, e: &Expr, caches: &mut TcCaches) -> Result<Expr, TypeError> {
        let mut ctx: Vec<Expr> = Vec::new();
        self.infer_type_core(e, &mut ctx, caches)
    }
    fn infer_type_core(&self, e: &Expr, ctx: &mut Vec<Expr>, caches: &mut TcCaches) -> Result<Expr, TypeError> {
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
                let f_type = self.infer_type_core(f, ctx, caches)?;
                let f_type_whnf = self.whnf_impl(&f_type, caches);
                match &f_type_whnf.kind {
                    ExprKind::Pi(_, expected_arg_type, result_type) => {
                        let arg_type = self.infer_type_core(a, ctx, caches)?;
                        if !self.is_def_eq(&arg_type, expected_arg_type, caches) {
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
                let arg_sort = self.infer_type_core(arg_type, ctx, caches)?;
                let arg_sort_whnf = self.whnf_impl(&arg_sort, caches);
                match &arg_sort_whnf.kind { ExprKind::Sort(_) => {} _ => return Err(TypeError::ExpectedSort { ty: Arc::new(arg_sort) }) }
                ctx.push(arg_type.as_ref().clone());
                let body_type = self.infer_type_core(body, ctx, caches);
                ctx.pop();
                let body_type = body_type?;
                Ok(Expr::pi(*bi, arg_type.as_ref().clone(), body_type))
            }
            ExprKind::Pi(_bi, arg_type, body) => {
                let arg_sort = self.infer_type_core(arg_type, ctx, caches)?;
                let arg_sort_whnf = self.whnf_impl(&arg_sort, caches);
                let l1 = match &arg_sort_whnf.kind { ExprKind::Sort(l) => l.clone(), _ => return Err(TypeError::ExpectedSort { ty: Arc::new(arg_sort) }) };
                ctx.push(arg_type.as_ref().clone());
                let body_sort = self.infer_type_core(body, ctx, caches);
                ctx.pop();
                let body_sort = body_sort?;
                let body_sort_whnf = self.whnf_impl(&body_sort, caches);
                let l2 = match &body_sort_whnf.kind { ExprKind::Sort(l) => l.clone(), _ => return Err(TypeError::ExpectedSort { ty: Arc::new(body_sort) }) };
                Ok(Expr::sort(Level::imax(l1, l2)))
            }
            ExprKind::Let(_name, ty, val, body, _nondep) => {
                let ty_sort = self.infer_type_core(ty, ctx, caches)?;
                let ty_sort_whnf = self.whnf_impl(&ty_sort, caches);
                match &ty_sort_whnf.kind { ExprKind::Sort(_) => {} _ => return Err(TypeError::ExpectedSort { ty: Arc::new(ty_sort) }) }
                let val_type = self.infer_type_core(val, ctx, caches)?;
                if !self.is_def_eq(&val_type, ty, caches) {
                    return Err(TypeError::TypeMismatch { expected: Arc::new(ty.as_ref().clone()), inferred: Arc::new(val_type) });
                }
                ctx.push(ty.as_ref().clone());
                let body_type = self.infer_type_core(body, ctx, caches);
                ctx.pop();
                let body_type = body_type?;
                Ok(body_type.instantiate(val))
            }
            ExprKind::Lit(lit) => Ok(match lit {
                Literal::Nat(_) => Expr::cnst(Name(0xFFFF_0001)),
                Literal::Str(_) => Expr::cnst(Name(0xFFFF_0002)),
            }),
            ExprKind::MData(_, inner) => self.infer_type_core(inner, ctx, caches),
            // the Proj TYPING rule (tc/infer.rs:617 release path: infer the
            // struct expr's type, then infer_proj_type_from).
            ExprKind::Proj(struct_name, idx, expr) => {
                let expr_type = self.infer_type_core(expr, ctx, caches)?;
                self.infer_proj_type_from(struct_name, *idx, expr, &expr_type, caches)
            }
            // FVar typing needs a local context we don't model here [C7].
            ExprKind::FVar(_) => Err(TypeError::Unsupported),
        }
    }

    // pi_domain_body_quick — VERBATIM tc/infer.rs:63: syntactic-Pi fast path
    // (skips whnf entirely, #1516), else whnf then split.
    fn pi_domain_body_quick(&self, ty: &Expr, caches: &mut TcCaches) -> Option<(Expr, Expr)> {
        match &ty.kind {
            ExprKind::Pi(_, domain, body) => {
                return Some((domain.as_ref().clone(), body.as_ref().clone()));
            }
            _ => {}
        }

        let ty_whnf = self.whnf_impl(ty, caches);
        match &ty_whnf.kind {
            ExprKind::Pi(_, domain, body) => Some((domain.as_ref().clone(), body.as_ref().clone())),
            _ => None,
        }
    }

    // ══════════════════════════════════════════════════════════════════════
    // THE PROJECTION TYPING SURFACE (target 1) — tc/infer_proj.rs, WITH the
    // is_prop Err-propagation gate and the proj_type_cache routing.
    // ══════════════════════════════════════════════════════════════════════

    // infer_proj_type_from — VERBATIM tc/infer_proj.rs:47 (strict path).
    pub fn infer_proj_type_from(&self, struct_name: &Name, idx: u32, expr: &Expr, expr_type: &Expr, caches: &mut TcCaches) -> Result<Expr, TypeError> {
        self.infer_proj_type_from_impl(struct_name, idx, expr, expr_type, true, caches)
    }

    // infer_proj_type_from_quick — VERBATIM tc/infer_proj.rs:62: same impl,
    // skips Prop-only projection validation; Err SWALLOWED BY DESIGN (.ok()).
    pub fn infer_proj_type_from_quick(&self, struct_name: &Name, idx: u32, expr: &Expr, expr_type: &Expr, caches: &mut TcCaches) -> Option<Expr> {
        match self.infer_proj_type_from_impl(struct_name, idx, expr, expr_type, false, caches) {
            Ok(v) => Some(v),
            Err(_) => None,
        }
    }

    // infer_proj_type_from_impl — VERBATIM tc/infer_proj.rs:73, INCLUDING:
    //   * the top-of-impl proj_type_cache consult (line 82)
    //   * THE GATE (line 95): `let is_prop_type = self.is_prop(&expr_type_whnf)?;`
    //     — inference errors PROPAGATE (#2208), they are NOT "not Prop"
    //   * the level-count gate (line 150) — degenerate under [C2]
    //   * the non-Prop batch fill + cache re-consult (lines 187-201)
    //   * the quick Prop path (walk_prop_telescope_to_idx, line 216-224)
    //   * the strict Prop batch fill + cache re-consult (lines 228-240)
    // Failure arms carry their REAL variants [C9].
    fn infer_proj_type_from_impl(
        &self,
        struct_name: &Name,
        idx: u32,
        expr: &Expr,
        expr_type: &Expr,
        validate_prop_projection: bool,
        caches: &mut TcCaches,
    ) -> Result<Expr, TypeError> {
        let proj_expr = Expr::proj(*struct_name, idx, expr.clone());
        if let Some(cached) = cache_get(&caches.proj, &proj_expr) {
            return Ok(cached);
        }

        // Use whnf_impl since we're called from _impl functions (avoid
        // redundant stack_safe re-entry)
        let expr_type_whnf = self.whnf_impl(expr_type, caches);

        // Per Lean 4 (type_checker.cpp:248), check if struct type is in Prop.
        // Propagate inference errors — if we can't determine Prop status,
        // we can't safely type-check the projection (#2208).
        let is_prop_type = self.is_prop(&expr_type_whnf, caches)?;

        // Extract the inductive type name and universe levels
        // Per Lean 4 (type_checker.cpp:241): const_levels(I) instantiate the
        // constructor's universe level parameters.
        let (type_name, type_levels): (Name, LevelVec) = match &expr_type_whnf.get_app_fn().kind {
            ExprKind::Const(name, levels) => (*name, levels.clone()),
            _ => return Err(TypeError::InvalidProjNotStruct),
        };

        // Verify the type matches the struct name in the projection
        if type_name != *struct_name {
            return Err(TypeError::InvalidProjNotStruct);
        }

        let type_args = expr_type_whnf.get_app_args();

        // 3. Look up the inductive type
        let ind_val = match self.get_inductive(struct_name) {
            Some(i) => i,
            None => return Err(TypeError::UnknownInductive(*struct_name)),
        };

        // Structures must have exactly one constructor
        if ind_val.num_ctors != 1 {
            return Err(TypeError::InvalidProjNotUniqueConstructor(*struct_name));
        }

        // 4. Look up the constructor
        let ctor_name = ind_val.ctor_name; // constructor_names[0] [C1]
        let ctor_val = match self.get_constructor(&ctor_name) {
            Some(c) => c,
            None => return Err(TypeError::UnknownConst(ctor_name)),
        };

        // Check index is in bounds
        if idx >= ctor_val.num_fields {
            return Err(TypeError::InvalidProjIndexOutOfBounds(idx, ctor_val.num_fields));
        }

        // Level params modeled absent [C2]: the level-count gate
        // (infer_proj.rs:150) degenerates to requiring an unleveled type head;
        // instantiate_level_params_direct is never taken.
        if type_levels.len() != 0 {
            return Err(TypeError::LevelCountMismatch(*struct_name));
        }
        let ctor_type = match self.ctor_declared_type(&ctor_name) {
            Some(t) => t,
            None => return Err(TypeError::UnknownConst(ctor_name)),
        };

        // Per Lean 4 (type_checker.cpp:237-238): require exactly
        // num_params + num_indices type arguments.
        let num_params = ctor_val.num_params as usize;
        let num_indices = ind_val.num_indices as usize;
        let expected_args = num_params + num_indices;
        if type_args.len() != expected_args {
            return Err(TypeError::InvalidProjWrongArgCount(type_args.len() as u32, expected_args as u32));
        }
        // Instantiate parameters with the first num_params type arguments.
        let instantiated_ctor_type = self.instantiate_params_prefix(&ctor_type, &type_args, num_params, caches);

        // Precompute and cache all projection field types in one telescope
        // walk when the type is NOT in Prop (#1516: O(n^2) -> O(n); both
        // strict and quick paths use this batch cache).
        if !is_prop_type {
            self.cache_projection_field_types_non_prop(struct_name, expr, &instantiated_ctor_type, ctor_val.num_fields, caches)?;
            if let Some(cached) = cache_get(&caches.proj, &proj_expr) {
                return Ok(cached);
            }
            return Err(TypeError::InvalidProjIndexOutOfBounds(idx, ctor_val.num_fields));
        }

        // Prop-typed structure. Quick path (validate_prop_projection=false):
        // skip Prop validation AND caching (avoid poisoning the strict path's
        // cache with unvalidated fields); walk to the target field directly.
        if !validate_prop_projection {
            return self.walk_prop_telescope_to_idx(struct_name, expr, &instantiated_ctor_type, idx, ctor_val.num_fields, caches);
        }

        // Strict path: batch-fill the projection cache for all fields with
        // Prop validation (#1420).
        self.cache_projection_field_types_prop(struct_name, expr, &instantiated_ctor_type, ctor_val.num_fields, caches)?;
        if let Some(cached) = cache_get(&caches.proj, &proj_expr) {
            return Ok(cached);
        }
        Err(TypeError::InvalidProjIndexOutOfBounds(idx, ctor_val.num_fields))
    }

    // cache_projection_field_types_non_prop — VERBATIM tc/infer_proj.rs:243:
    // one telescope walk filling the proj cache for ALL fields (the built
    // Proj node is used to instantiate the dependent body, then moved into
    // the cache as its key). trim_if_needed modeled out [C3]; for -> while
    // [C11].
    fn cache_projection_field_types_non_prop(
        &self,
        struct_name: &Name,
        expr: &Expr,
        instantiated_ctor_type: &Expr,
        num_fields: u32,
        caches: &mut TcCaches,
    ) -> Result<(), TypeError> {
        let mut current_type = instantiated_ctor_type.clone();
        let mut field_idx: u32 = 0;
        while field_idx < num_fields {
            let (domain, body): (Expr, Expr) = match self.pi_domain_body_quick(&current_type, caches) {
                Some(db) => db,
                None => return Err(TypeError::InvalidProjIndexOutOfBounds(num_fields.saturating_sub(1), field_idx)),
            };
            let proj_expr = Expr::proj(*struct_name, field_idx, expr.clone());
            if field_idx + 1 < num_fields {
                if body.has_loose_bvars() {
                    current_type = body.instantiate(&proj_expr);
                } else {
                    current_type = body;
                }
            }
            cache_insert(&mut caches.proj, proj_expr, domain);
            field_idx += 1;
        }
        Ok(())
    }

    // walk_prop_telescope_to_idx — VERBATIM tc/infer_proj.rs:279: the quick
    // path's UNCACHED walk of a Prop-typed telescope (no cache writes — the
    // strict path's cache must not see unvalidated fields).
    fn walk_prop_telescope_to_idx(
        &self,
        struct_name: &Name,
        expr: &Expr,
        instantiated_ctor_type: &Expr,
        target_idx: u32,
        num_fields: u32,
        caches: &mut TcCaches,
    ) -> Result<Expr, TypeError> {
        let mut current_type = instantiated_ctor_type.clone();
        let mut field_idx: u32 = 0;
        while field_idx <= target_idx {
            let (domain, body): (Expr, Expr) = match self.pi_domain_body_quick(&current_type, caches) {
                Some(db) => db,
                None => return Err(TypeError::InvalidProjIndexOutOfBounds(num_fields.saturating_sub(1), field_idx)),
            };
            if field_idx == target_idx {
                return Ok(domain);
            }
            if body.has_loose_bvars() {
                let proj_field = Expr::proj(*struct_name, field_idx, expr.clone());
                current_type = body.instantiate(&proj_field);
            } else {
                current_type = body;
            }
            field_idx += 1;
        }
        Err(TypeError::InvalidProjIndexOutOfBounds(target_idx, num_fields))
    }

    // cache_projection_field_types_prop — VERBATIM tc/infer_proj.rs:315:
    // mirrors the non-Prop batch fill but VALIDATES each field's domain is in
    // Prop (Lean 4 type_checker.cpp:252-263) — `if !self.is_prop(&domain)?`
    // is a SECOND real is_prop Err-propagation site.
    fn cache_projection_field_types_prop(
        &self,
        struct_name: &Name,
        expr: &Expr,
        instantiated_ctor_type: &Expr,
        num_fields: u32,
        caches: &mut TcCaches,
    ) -> Result<(), TypeError> {
        let mut current_type = instantiated_ctor_type.clone();
        let mut field_idx: u32 = 0;
        while field_idx < num_fields {
            let (domain, body): (Expr, Expr) = match self.pi_domain_body_quick(&current_type, caches) {
                Some(db) => db,
                None => return Err(TypeError::InvalidProjIndexOutOfBounds(num_fields.saturating_sub(1), field_idx)),
            };

            // Per Lean 4 (type_checker.cpp:263): projected field type must be
            // in Prop. Inference Err PROPAGATES (#2208).
            if !self.is_prop(&domain, caches)? {
                return Err(TypeError::InvalidProjFromProp(field_idx));
            }

            let proj_expr = Expr::proj(*struct_name, field_idx, expr.clone());
            if field_idx + 1 < num_fields {
                if body.has_loose_bvars() {
                    current_type = body.instantiate(&proj_expr);
                } else {
                    current_type = body;
                }
            }
            cache_insert(&mut caches.proj, proj_expr, domain);
            field_idx += 1;
        }
        Ok(())
    }

    // instantiate_params — VERBATIM tc/infer_proj.rs:357 (iterator arg
    // modeled as the first `count` elements of `args`, established).
    fn instantiate_params_prefix(&self, ty: &Expr, args: &Vec<Expr>, count: usize, caches: &mut TcCaches) -> Expr {
        let mut result = ty.clone();
        let mut i: usize = 0;
        while i < count {
            // Use whnf_impl since we're called from _impl functions
            let result_whnf = self.whnf_impl(&result, caches);
            match &result_whnf.kind {
                ExprKind::Pi(_, _, body) => { result = body.instantiate(&args[i]); }
                _ => { return result; } // break
            }
            i += 1;
        }
        result
    }

    // is_prop — VERBATIM tc/infer_proj.rs:382 (Lean 4 type_checker.cpp:327:
    // `whnf(infer_type(e)) == mk_Prop()`). Returns Ok(true)/Ok(false)/Err —
    // callers MUST handle the Err explicitly rather than treating inference
    // failure as "not Prop" (#2208). The try_infer_type_quick /
    // infer_type_infer_only pair is collapsed to the single modeled inference
    // [C8]; the `?` propagation is REAL.
    pub fn is_prop(&self, ty: &Expr, caches: &mut TcCaches) -> Result<bool, TypeError> {
        let ty_whnf = self.whnf_impl(ty, caches);
        let ty_of_ty = self.infer_type(&ty_whnf, caches)?;
        let ty_of_ty_whnf = self.whnf_impl(&ty_of_ty, caches);
        let res = match &ty_of_ty_whnf.kind {
            ExprKind::Sort(l) => Level::is_zero(l),
            _ => false,
        };
        Ok(res)
    }
}

// ───────────────────────── MODELED REGISTRY (root 1) ────────────────────────
// Structures / inductives (see the scenario docs at the root):
//   POINT    : paramless 2-field non-Prop structure  Point.mk : Nat -> Nat -> Point
//   PPAIR    : 1-PARAM 2-field non-Prop structure    PPair.mk : (A:Type) -> A -> A -> PPair A
//   DSTRUCT  : paramless DEPENDENT 2-field           DStruct.mk : (T:Type) -> PBox T -> DStruct
//   PROPS    : Prop structure, both fields : PROPQ (: Prop)
//   BADPROP  : Prop structure, field 0 : NATTY (: Type) — strict must reject
//   BADPROP2 : Prop structure, field 0 : GHOSTQ (UNDECLARED) — strict must ERR
//   GHOST    : registered structure whose TYPE is UNDECLARED — the is_prop
//              GATE must Err(UnknownConst(GHOST)); a gate-swallowing checker
//              would succeed and return the field type
//   BOOLLIKE : 2-ctor inductive (not unique-ctor)
//   FAKE     : declared type-former with NO inductive entry
//   CTORLESS : inductive whose ctor is missing from the ctor registry
//   PBOXL    : 1-param structure reached through a LEVELED type head (the
//              degenerate [C2] level-count gate)
pub const NATTY: u32 = 200;
pub const POINT: u32 = 100;     pub const POINT_MK: u32 = 101;    pub const P_VAL: u32 = 300;
pub const PPAIR: u32 = 110;     pub const PPAIR_MK: u32 = 111;    pub const PP_VAL: u32 = 310;  pub const PP0_VAL: u32 = 311;
pub const PBOX: u32 = 130;
pub const DSTRUCT: u32 = 140;   pub const DSTRUCT_MK: u32 = 141;  pub const D_VAL: u32 = 340;
pub const PROPS: u32 = 180;     pub const PROPS_MK: u32 = 181;    pub const PR_VAL: u32 = 380;  pub const PROPQ: u32 = 182;
pub const BADPROP: u32 = 190;   pub const BADPROP_MK: u32 = 191;  pub const BP_VAL: u32 = 390;
pub const BADPROP2: u32 = 192;  pub const BADPROP2_MK: u32 = 193; pub const BP2_VAL: u32 = 392; pub const GHOSTQ: u32 = 194;
pub const GHOST: u32 = 500;     pub const GHOST_MK: u32 = 501;    pub const G_VAL: u32 = 502;
pub const BOOLLIKE: u32 = 150;  pub const BOOLLIKE_T: u32 = 151;  pub const BOOLLIKE_F: u32 = 152; pub const B_VAL: u32 = 350;
pub const FAKE: u32 = 160;      pub const F_VAL: u32 = 360;
pub const CTORLESS: u32 = 170;  pub const CTORLESS_MK: u32 = 171; pub const CL_VAL: u32 = 370;
pub const PBOXL: u32 = 175;     pub const PBOXL_MK: u32 = 176;    pub const PBL_VAL: u32 = 375;
pub const X_VAL: u32 = 395;
pub const N0: u32 = 400;        pub const N1: u32 = 401;
pub const POISON: u32 = 600;    pub const SENT: u32 = 601;
pub const FF: u32 = 510;        pub const GG: u32 = 511;          pub const HH: u32 = 512;      pub const PV: u32 = 513;

// term builder shorthands (monomorphic free fns — no closures).
pub fn c(n: u32) -> Expr { Expr::cnst(Name(n)) }
pub fn ap(f: Expr, x: Expr) -> Expr { Expr::app(f, x) }
pub fn pj(s: u32, i: u32, e: Expr) -> Expr { Expr::proj(Name(s), i, e) }
pub fn sort1() -> Expr { Expr::sort(Level::succ(Level::Zero)) }
// the singleton level vec [Succ Zero] — built via Vec::new + push (NOT a
// vec![..] literal), the established layout convention.
pub fn lvl1() -> LevelVec {
    let mut v: LevelVec = Vec::new();
    v.push(Level::succ(Level::Zero));
    v
}

// Constructor TYPES (ConstructorVal.type_ [C1]) — real Pi telescopes:
fn point_mk_type() -> Expr {
    Expr::pi(bd_default(), c(NATTY), Expr::pi(bd_default(), c(NATTY), c(POINT)))
}
fn ppair_mk_type() -> Expr {
    // (A : Type 0) -> A -> A -> PPair A
    Expr::pi(bd_default(), sort1(),
        Expr::pi(bd_default(), Expr::bvar(0),
            Expr::pi(bd_default(), Expr::bvar(1), ap(c(PPAIR), Expr::bvar(2)))))
}
fn dstruct_mk_type() -> Expr {
    // (T : Type 0) -> PBox T -> DStruct   (field 1's type DEPENDS on field 0)
    Expr::pi(bd_default(), sort1(), Expr::pi(bd_default(), ap(c(PBOX), Expr::bvar(0)), c(DSTRUCT)))
}
fn props_mk_type() -> Expr {
    Expr::pi(bd_default(), c(PROPQ), Expr::pi(bd_default(), c(PROPQ), c(PROPS)))
}
fn badprop_mk_type() -> Expr { Expr::pi(bd_default(), c(NATTY), c(BADPROP)) }
fn badprop2_mk_type() -> Expr { Expr::pi(bd_default(), c(GHOSTQ), c(BADPROP2)) }
fn ghost_mk_type() -> Expr { Expr::pi(bd_default(), c(NATTY), c(GHOST)) }
fn pboxl_mk_type() -> Expr {
    // (A : Type 0) -> A -> PBoxL A
    Expr::pi(bd_default(), sort1(), Expr::pi(bd_default(), Expr::bvar(0), ap(c(PBOXL), Expr::bvar(1))))
}

fn build_inductives() -> Vec<InductiveInfo> {
    vec![
        InductiveInfo { name: Name(POINT),    num_ctors: 1, ctor_name: Name(POINT_MK),    num_indices: 0, is_recursive: false },
        InductiveInfo { name: Name(PPAIR),    num_ctors: 1, ctor_name: Name(PPAIR_MK),    num_indices: 0, is_recursive: false },
        InductiveInfo { name: Name(DSTRUCT),  num_ctors: 1, ctor_name: Name(DSTRUCT_MK),  num_indices: 0, is_recursive: false },
        InductiveInfo { name: Name(PROPS),    num_ctors: 1, ctor_name: Name(PROPS_MK),    num_indices: 0, is_recursive: false },
        InductiveInfo { name: Name(BADPROP),  num_ctors: 1, ctor_name: Name(BADPROP_MK),  num_indices: 0, is_recursive: false },
        InductiveInfo { name: Name(BADPROP2), num_ctors: 1, ctor_name: Name(BADPROP2_MK), num_indices: 0, is_recursive: false },
        InductiveInfo { name: Name(GHOST),    num_ctors: 1, ctor_name: Name(GHOST_MK),    num_indices: 0, is_recursive: false },
        InductiveInfo { name: Name(BOOLLIKE), num_ctors: 2, ctor_name: Name(BOOLLIKE_T),  num_indices: 0, is_recursive: false },
        InductiveInfo { name: Name(CTORLESS), num_ctors: 1, ctor_name: Name(CTORLESS_MK), num_indices: 0, is_recursive: false },
        InductiveInfo { name: Name(PBOXL),    num_ctors: 1, ctor_name: Name(PBOXL_MK),    num_indices: 0, is_recursive: false },
    ]
}

fn build_ctors() -> Vec<ConstructorInfo> {
    vec![
        ConstructorInfo { ctor_name: Name(POINT_MK),    inductive_name: Name(POINT),    num_params: 0, num_fields: 2 },
        ConstructorInfo { ctor_name: Name(PPAIR_MK),    inductive_name: Name(PPAIR),    num_params: 1, num_fields: 2 },
        ConstructorInfo { ctor_name: Name(DSTRUCT_MK),  inductive_name: Name(DSTRUCT),  num_params: 0, num_fields: 2 },
        ConstructorInfo { ctor_name: Name(PROPS_MK),    inductive_name: Name(PROPS),    num_params: 0, num_fields: 2 },
        ConstructorInfo { ctor_name: Name(BADPROP_MK),  inductive_name: Name(BADPROP),  num_params: 0, num_fields: 1 },
        ConstructorInfo { ctor_name: Name(BADPROP2_MK), inductive_name: Name(BADPROP2), num_params: 0, num_fields: 1 },
        ConstructorInfo { ctor_name: Name(GHOST_MK),    inductive_name: Name(GHOST),    num_params: 0, num_fields: 1 },
        ConstructorInfo { ctor_name: Name(BOOLLIKE_T),  inductive_name: Name(BOOLLIKE), num_params: 0, num_fields: 0 },
        // CTORLESS_MK deliberately ABSENT (the UnknownConst(ctor) arm).
        ConstructorInfo { ctor_name: Name(PBOXL_MK),    inductive_name: Name(PBOXL),    num_params: 1, num_fields: 1 },
    ]
}

// ctor num_params table (whnf reduce_proj) — mirrors build_ctors [C1].
fn build_ctor_np() -> Vec<(Name, u32)> {
    vec![
        (Name(POINT_MK), 0),
        (Name(PPAIR_MK), 1),
        (Name(DSTRUCT_MK), 0),
        (Name(PROPS_MK), 0),
        (Name(BADPROP_MK), 0),
        (Name(BADPROP2_MK), 0),
        (Name(GHOST_MK), 0),
        (Name(BOOLLIKE_T), 0),
        (Name(PBOXL_MK), 1),
    ]
}

// ConstructorVal.type_ side table [C1].
fn build_ctor_types() -> Vec<(Name, Expr)> {
    vec![
        (Name(POINT_MK), point_mk_type()),
        (Name(PPAIR_MK), ppair_mk_type()),
        (Name(DSTRUCT_MK), dstruct_mk_type()),
        (Name(PROPS_MK), props_mk_type()),
        (Name(BADPROP_MK), badprop_mk_type()),
        (Name(BADPROP2_MK), badprop2_mk_type()),
        (Name(GHOST_MK), ghost_mk_type()),
        (Name(PBOXL_MK), pboxl_mk_type()),
    ]
}

// Declared types (infer_type's Const rule). GHOST and GHOSTQ are deliberately
// ABSENT (the is_prop gate must ERR on them — #2208), as is GHOST from env.
fn build_decl_types() -> Vec<(Name, Expr)> {
    vec![
        (Name(NATTY), sort1()),                                   // Nat : Type 0
        (Name(POINT), sort1()),
        (Name(DSTRUCT), sort1()),
        (Name(BOOLLIKE), sort1()),
        (Name(FAKE), sort1()),
        (Name(CTORLESS), sort1()),
        (Name(PROPS), Expr::sort(Level::Zero)),                   // PROPS : Prop
        (Name(PROPQ), Expr::sort(Level::Zero)),                   // PROPQ : Prop
        (Name(BADPROP), Expr::sort(Level::Zero)),                 // BADPROP : Prop
        (Name(BADPROP2), Expr::sort(Level::Zero)),                // BADPROP2 : Prop
        (Name(PPAIR), Expr::pi(bd_default(), sort1(), sort1())),  // PPair : Type -> Type
        (Name(PBOX), Expr::pi(bd_default(), sort1(), sort1())),   // PBox : Type -> Type
        (Name(PBOXL), Expr::pi(bd_default(), sort1(), sort1())),  // PBoxL : Type -> Type
        (Name(P_VAL), c(POINT)),                                  // p : Point
        (Name(PP_VAL), ap(c(PPAIR), c(NATTY))),                   // pp : PPair Nat
        (Name(PP0_VAL), c(PPAIR)),                                // pp0 : PPair (UNAPPLIED — arg-count gate)
        (Name(D_VAL), c(DSTRUCT)),                                // d : DStruct
        (Name(PR_VAL), c(PROPS)),                                 // pr : PROPS
        (Name(BP_VAL), c(BADPROP)),
        (Name(BP2_VAL), c(BADPROP2)),
        (Name(G_VAL), c(GHOST)),                                  // g : GHOST (GHOST itself undeclared!)
        (Name(B_VAL), c(BOOLLIKE)),
        (Name(F_VAL), c(FAKE)),
        (Name(CL_VAL), c(CTORLESS)),
        (Name(PBL_VAL), ap(Expr::const_(Name(PBOXL), lvl1()), c(NATTY))), // pbl : PBoxL.{1} Nat (leveled head)
        (Name(X_VAL), Expr::sort(Level::Zero)),                   // x : Prop (type head is a Sort, not a Const)
        (Name(N0), c(NATTY)),
        (Name(N1), c(NATTY)),
    ]
}

// ───────────────────────── MONO ROOT 1 (#[no_mangle]) ────────────────────────
// tc_proj_root — target (1): the projection-typing surface with the REAL
// is_prop Err-propagation gate + the proj_type_cache routing, over the CACHED
// whnf. entry 0 = strict (infer_proj_type_from), entry 1 = quick
// (infer_proj_type_from_quick). The struct expr's type is computed by the
// verified infer pillar first (the real infer.rs:617 call shape).
//
// Returns: 1 = Ok (result Expr written through `out`); 0 = quick-path None;
// negative = err_code (payload via `err_payload`). `lens` always receives the
// packed cache lengths (proj<<48 | whnf<<32 | core<<16 | unfold).
//
// scenario | (struct, idx, value)        | strict (entry 0)          | quick (entry 1)
// ---------+-----------------------------+---------------------------+----------------
//    0     | (POINT, 0, p)               | Ok NATTY (non-Prop batch) | Ok NATTY
//    1     | (POINT, 1, p)               | Ok NATTY                  | Ok NATTY
//    2     | (POINT, 5, p)               | Err OOB(5,2)      -9      | None
//    3     | (GHOST, 0, g)  [THE GATE]   | Err UnknownConst(GHOST) -2| None
//    4     | (PROPS, 1, pr)              | Ok PROPQ (Prop batch)     | Ok PROPQ (uncached walk)
//    5     | (BADPROP, 0, bp)            | Err FromProp(0)  -12      | Ok NATTY   <- REAL strict/quick divergence
//    6     | (DSTRUCT, 0, p:POINT)       | Err NotStruct    -6       | None       (name mismatch)
//    7     | (DSTRUCT, 1, d)             | Ok PBox (Proj DSTRUCT 0 d)| same       (dependent telescope)
//    8     | (PPAIR, 1, pp)              | Ok NATTY (params>0)       | same
//    9     | (POINT, 0, x : Prop)        | Err NotStruct    -6       | None       (head is Sort, not Const)
//   10     | (BADPROP2, 0, bp2) [GATE 2] | Err UnknownConst(GHOSTQ)-2| Ok GHOSTQ  <- gate inside the Prop batch
//   11     | (POINT, 0, p) + POISONED proj cache | Ok POISON         | Ok POISON  (top-of-impl consult observed)
//   12     | (PPAIR, 0, pp0)             | Err WrongArgCount(0,1) -11| None
//   13     | (FAKE, 0, f)                | Err UnknownInductive -7   | None
//   14     | (BOOLLIKE, 0, b)            | Err NotUnique    -8       | None
//   15     | (CTORLESS, 0, cl)           | Err UnknownConst(CTORLESS_MK) -2 | None
//   16     | (PBOXL, 0, pbl)             | Err LevelCountMismatch -10| None       (leveled head, [C2] gate)
#[no_mangle]
pub extern "C" fn tc_proj_root(out: *mut Expr, err_payload_out: *mut u64, lens: *mut u64, scenario: u32, entry: u32) -> i32 {
    let ctor_np = build_ctor_np();
    let decl_types = build_decl_types();
    let ctor_types = build_ctor_types();
    let inductives = build_inductives();
    let ctors = build_ctors();
    let env: Vec<(Name, Option<Expr>)> = Vec::new(); // all neutrals opaque here

    let struct_name: u32;
    let idx: u32;
    let val_name: u32;
    if scenario == 0 { struct_name = POINT; idx = 0; val_name = P_VAL; }
    else if scenario == 1 { struct_name = POINT; idx = 1; val_name = P_VAL; }
    else if scenario == 2 { struct_name = POINT; idx = 5; val_name = P_VAL; }
    else if scenario == 3 { struct_name = GHOST; idx = 0; val_name = G_VAL; }
    else if scenario == 4 { struct_name = PROPS; idx = 1; val_name = PR_VAL; }
    else if scenario == 5 { struct_name = BADPROP; idx = 0; val_name = BP_VAL; }
    else if scenario == 6 { struct_name = DSTRUCT; idx = 0; val_name = P_VAL; }
    else if scenario == 7 { struct_name = DSTRUCT; idx = 1; val_name = D_VAL; }
    else if scenario == 8 { struct_name = PPAIR; idx = 1; val_name = PP_VAL; }
    else if scenario == 9 { struct_name = POINT; idx = 0; val_name = X_VAL; }
    else if scenario == 10 { struct_name = BADPROP2; idx = 0; val_name = BP2_VAL; }
    else if scenario == 11 { struct_name = POINT; idx = 0; val_name = P_VAL; }
    else if scenario == 12 { struct_name = PPAIR; idx = 0; val_name = PP0_VAL; }
    else if scenario == 13 { struct_name = FAKE; idx = 0; val_name = F_VAL; }
    else if scenario == 14 { struct_name = BOOLLIKE; idx = 0; val_name = B_VAL; }
    else if scenario == 15 { struct_name = CTORLESS; idx = 0; val_name = CL_VAL; }
    else { struct_name = PBOXL; idx = 0; val_name = PBL_VAL; }

    let expr = Expr::cnst(Name(val_name));
    let mut caches = caches_new();

    if scenario == 11 {
        // POISON the proj cache for the exact key the impl will build: if the
        // JIT'd code genuinely consults the cache, it MUST return the poison.
        let key = Expr::proj(Name(POINT), 0, expr.clone());
        cache_insert(&mut caches.proj, key, Expr::cnst(Name(POISON)));
    }

    let v = CertVerifier {
        env: &env,
        ctor_np: &ctor_np,
        decl_types: &decl_types,
        ctor_types: &ctor_types,
        inductives: &inductives,
        ctors: &ctors,
    };

    // The real call shape (tc/infer.rs:617): infer the struct expr's type,
    // then hand it to the projection-typing rule.
    let expr_type = match v.infer_type(&expr, &mut caches) {
        Ok(t) => t,
        Err(e) => {
            unsafe { *err_payload_out = err_payload(&e); }
            unsafe { *lens = pack_lens(&caches); }
            return err_code(&e);
        }
    };

    let ret: i32;
    if entry == 0 {
        match v.infer_proj_type_from(&Name(struct_name), idx, &expr, &expr_type, &mut caches) {
            Ok(res) => {
                unsafe { std::ptr::write(out, res); }
                unsafe { *err_payload_out = 0; }
                ret = 1;
            }
            Err(e) => {
                unsafe { *err_payload_out = err_payload(&e); }
                ret = err_code(&e);
            }
        }
    } else {
        match v.infer_proj_type_from_quick(&Name(struct_name), idx, &expr, &expr_type, &mut caches) {
            Some(res) => {
                unsafe { std::ptr::write(out, res); }
                unsafe { *err_payload_out = 0; }
                ret = 1;
            }
            None => {
                unsafe { *err_payload_out = 0; }
                ret = 0;
            }
        }
    }
    unsafe { *lens = pack_lens(&caches); }
    ret
}

// ───────────────────────── MONO ROOT 2 (#[no_mangle]) ────────────────────────
// tc_whnf_route_root — target (2): the cached whnf_core routing, observed via
// cold / warm / poisoned runs. The result Expr goes through `out`; `lens`
// receives the packed cache lengths (proj<<48 | whnf<<32 | core<<16 |
// unfold) so RECORD effects are differentially visible; ret is 1 (or, for
// the double-call scenarios, 1 iff both calls agreed, else 2; for s9, 2 iff
// the lam-head key was wrongly appended to the core cache).
//
// scenario | term / cache prep                          | what it proves
// ---------+--------------------------------------------+----------------------------------------
//    0     | (λx:Nat. x) n0, cold                       | miss -> compute + RECORD (whnf & core lens grow)
//    1     | same, called TWICE                         | warm hit: same result, NO cache growth
//    2     | same, whnf cache POISONED at the root key  | hit -> returns the poison (consult observed)
//    3     | Const F (F ↦ G), cache poisoned AT G       | the mid-outer-loop consult on the delta
//          |                                            | intermediate (#3210) + miss-path RECORD
//    4     | Pi(Nat, Nat), whnf cache POISONED at key   | already-normal kinds return BEFORE the
//          |                                            | cache: poison NOT observed (kind gate)
//    5     | beta term: core_no_delta cheap THEN full   | cheap_proj=true does NOT write the core
//          |                                            | cache; full-proj DOES (Lean 4 guard)
//    6     | beta term, core cache POISONED, cheap read | core read is UNCONDITIONAL (#1768)
//    7     | Const F (F↦G, G↦H): whnf(F) then whnf(G)   | m_unfold: second unfold of G HITS (no
//          |                                            | unfold-len growth); only successes cached
//    8     | Proj(POINT, 0, PV) with PV ↦ Point.mk n0 n1| reduce_proj's cross-mode escalation into
//          |                                            | FULL cached whnf + field re-entry
//    9     | beta term: core_no_delta CHEAP only, cold  | whnf_recurse write-gate POLARITY: cheap
//          |                                            | mode writes NOTHING (core stays EMPTY;
//          |                                            | ret 2 iff the lam-head key was appended)
#[no_mangle]
pub extern "C" fn tc_whnf_route_root(out: *mut Expr, lens: *mut u64, scenario: u32) -> i32 {
    let empty_decl: Vec<(Name, Expr)> = Vec::new();
    let empty_ctypes: Vec<(Name, Expr)> = Vec::new();
    let inductives: Vec<InductiveInfo> = Vec::new();
    let ctors: Vec<ConstructorInfo> = Vec::new();
    let ctor_np = build_ctor_np();

    let beta_term = ap(Expr::lam(bd_default(), c(NATTY), Expr::bvar(0)), c(N0));

    let e: Expr;
    let env: Vec<(Name, Option<Expr>)>;
    if scenario == 3 {
        e = c(FF);
        env = vec![(Name(FF), Some(c(GG)))];
    } else if scenario == 7 {
        e = c(FF);
        env = vec![(Name(FF), Some(c(GG))), (Name(GG), Some(c(HH)))];
    } else if scenario == 8 {
        e = pj(POINT, 0, c(PV));
        env = vec![(Name(PV), Some(ap(ap(c(POINT_MK), c(N0)), c(N1))))];
    } else if scenario == 4 {
        e = Expr::pi(bd_default(), c(NATTY), c(NATTY));
        env = Vec::new();
    } else {
        e = beta_term.clone();
        env = Vec::new();
    }

    let mut caches = caches_new();
    if scenario == 2 || scenario == 4 {
        cache_insert(&mut caches.whnf, e.clone(), c(POISON));
    }
    if scenario == 3 {
        // poison the DELTA INTERMEDIATE (Const G), not the root key.
        cache_insert(&mut caches.whnf, c(GG), c(SENT));
    }
    if scenario == 6 {
        cache_insert(&mut caches.core, e.clone(), c(POISON));
    }

    let v = CertVerifier {
        env: &env,
        ctor_np: &ctor_np,
        decl_types: &empty_decl,
        ctor_types: &empty_ctypes,
        inductives: &inductives,
        ctors: &ctors,
    };

    let mut ret: i32 = 1;
    let result: Expr;
    if scenario == 1 {
        let r1 = v.whnf(&e, &mut caches);
        let r2 = v.whnf(&e, &mut caches);
        ret = if expr_eq(&r1, &r2) { 1 } else { 2 };
        result = r2;
    } else if scenario == 5 {
        let r1 = v.whnf_core_no_delta(&e, true, &mut caches);
        let r2 = v.whnf_core_no_delta(&e, false, &mut caches);
        ret = if expr_eq(&r1, &r2) { 1 } else { 2 };
        result = r2;
    } else if scenario == 6 {
        result = v.whnf_core_no_delta(&e, true, &mut caches);
    } else if scenario == 9 {
        // CHEAP-ONLY probe (the whnf_recurse WRITE-GATE POLARITY, #1768): one
        // whnf_core_no_delta(beta, cheap_proj=true) over a COLD core cache. In
        // NoDeltaCheapProj mode NEITHER write site may fire — the outer
        // whnf_core_no_delta gate skips the beta-term key and the inner
        // whnf_recurse gate (Lean 4 `!cheap_rec && !cheap_proj`) skips the
        // lam-head key — so the core cache must stay EMPTY (packed lens 0x0).
        // ret additionally SCANS for the lam-head key, the entry ONLY a
        // write-on-cheap bug at the whnf_recurse site would append (no other
        // site ever writes that key in this scenario): 2 = present (the bug),
        // 1 = absent (the discipline). An unconditional outer write is the
        // distinct signature (ret 1, core len 1).
        let r = v.whnf_core_no_delta(&e, true, &mut caches);
        let lam_head = Expr::lam(bd_default(), c(NATTY), Expr::bvar(0));
        ret = match cache_get(&caches.core, &lam_head) { Some(_) => 2, None => 1 };
        result = r;
    } else if scenario == 7 {
        let r1 = v.whnf(&e, &mut caches);
        let e2 = c(GG);
        let r2 = v.whnf(&e2, &mut caches);
        ret = if expr_eq(&r1, &r2) { 1 } else { 2 };
        result = r2;
    } else {
        result = v.whnf(&e, &mut caches);
    }

    unsafe { std::ptr::write(out, result); }
    unsafe { *lens = pack_lens(&caches); }
    ret
}

// ════════════════════════════════════════════════════════════════════════════
// Standalone self-check harness (native): exercises every scenario through
// both roots, verifying the expected codes and routing observations.
// ════════════════════════════════════════════════════════════════════════════

pub fn deep_eq(a: &Expr, b: &Expr) -> bool {
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

fn run_proj(scenario: u32, entry: u32) -> (i32, u64, u64, Option<Expr>) {
    let mut slot = std::mem::MaybeUninit::<Expr>::uninit();
    let mut payload: u64 = 0xDEAD;
    let mut lens: u64 = 0;
    let code = tc_proj_root(slot.as_mut_ptr(), &mut payload, &mut lens, scenario, entry);
    let e = if code == 1 { Some(unsafe { slot.assume_init() }) } else { None };
    (code, payload, lens, e)
}

fn run_whnf(scenario: u32) -> (i32, u64, Expr) {
    let mut slot = std::mem::MaybeUninit::<Expr>::uninit();
    let mut lens: u64 = 0;
    let ret = tc_whnf_route_root(slot.as_mut_ptr(), &mut lens, scenario);
    (ret, lens, unsafe { slot.assume_init() })
}

fn main() {
    let mut ok = true;

    // root 1 expectations: (strict code, quick code).
    let expects: [(i32, i32); 17] = [
        (1, 1), (1, 1), (-9, 0), (-2, 0), (1, 1), (-12, 1), (-6, 0), (1, 1), (1, 1),
        (-6, 0), (-2, 1), (1, 1), (-11, 0), (-7, 0), (-8, 0), (-2, 0), (-10, 0),
    ];
    let mut s: u32 = 0;
    while s < 17 {
        let (cs, ps, _ls, _es) = run_proj(s, 0);
        let (cq, _pq, _lq, _eq) = run_proj(s, 1);
        let (ws, wq) = expects[s as usize];
        if cs != ws || cq != wq {
            println!("proj scenario {s}: strict={cs} (want {ws}) quick={cq} (want {wq})  <-- MISMATCH");
            ok = false;
        } else {
            println!("proj scenario {s}: strict={cs} quick={cq} payload={ps:#x}");
        }
        s += 1;
    }
    // gate payloads: scenario 3 must carry GHOST, 10 must carry GHOSTQ.
    let (c3, p3, _, _) = run_proj(3, 0);
    if !(c3 == -2 && p3 == GHOST as u64) { println!("gate payload wrong: {c3} {p3}"); ok = false; }
    let (c10, p10, _, _) = run_proj(10, 0);
    if !(c10 == -2 && p10 == GHOSTQ as u64) { println!("prop-batch gate payload wrong: {c10} {p10}"); ok = false; }
    // poison observation: scenario 11 must return the POISON const.
    let (c11, _, _, e11) = run_proj(11, 0);
    let poison_seen = match &e11 { Some(e) => deep_eq(e, &c(POISON)), None => false };
    if !(c11 == 1 && poison_seen) { println!("proj-cache poison NOT observed"); ok = false; }
    // dependent result shape: scenario 7 = PBox (Proj DSTRUCT 0 d).
    let (c7, _, _, e7) = run_proj(7, 0);
    let want7 = ap(c(PBOX), pj(DSTRUCT, 0, c(D_VAL)));
    let dep_ok = match &e7 { Some(e) => deep_eq(e, &want7), None => false };
    if !(c7 == 1 && dep_ok) { println!("dependent proj type shape wrong"); ok = false; }

    // root 2: routing observations.
    let (r0, l0, e0) = run_whnf(0);
    let cold_ok = r0 == 1 && deep_eq(&e0, &c(N0)) && l0 == ((1u64) << 32 | (1u64) << 16);
    if !cold_ok { println!("whnf s0 cold: ret={r0} lens={l0:#x}"); ok = false; }
    let (r1, l1, e1) = run_whnf(1);
    if !(r1 == 1 && deep_eq(&e1, &c(N0)) && l1 == l0) { println!("whnf s1 warm: ret={r1} lens={l1:#x}"); ok = false; }
    let (r2, l2, e2) = run_whnf(2);
    if !(r2 == 1 && deep_eq(&e2, &c(POISON))) { println!("whnf s2 poison NOT observed"); ok = false; }
    if deep_eq(&e2, &e0) { println!("whnf s2 poison indistinguishable from cold"); ok = false; }
    let _ = l2;
    let (r3, l3, e3) = run_whnf(3);
    if !(r3 == 1 && deep_eq(&e3, &c(SENT)) && l3 == ((2u64) << 32 | 1u64)) { println!("whnf s3 mid-loop consult: ret={r3} lens={l3:#x}"); ok = false; }
    let (r4, _l4, e4) = run_whnf(4);
    let pi_term = Expr::pi(bd_default(), c(NATTY), c(NATTY));
    if !(r4 == 1 && deep_eq(&e4, &pi_term)) { println!("whnf s4 kind-gate: poison leaked through the early return"); ok = false; }
    let (r5, l5, e5) = run_whnf(5);
    if !(r5 == 1 && deep_eq(&e5, &c(N0)) && l5 == ((2u64) << 16)) { println!("whnf s5 core write discipline: ret={r5} lens={l5:#x}"); ok = false; }
    let (r6, l6, e6) = run_whnf(6);
    if !(r6 == 1 && deep_eq(&e6, &c(POISON)) && l6 == ((1u64) << 16)) { println!("whnf s6 core poison: ret={r6} lens={l6:#x}"); ok = false; }
    let (r7, l7, e7b) = run_whnf(7);
    if !(r7 == 1 && deep_eq(&e7b, &c(HH)) && l7 == ((2u64) << 32 | 2u64)) { println!("whnf s7 unfold cache: ret={r7} lens={l7:#x}"); ok = false; }
    let (r8, l8, e8) = run_whnf(8);
    if !(r8 == 1 && deep_eq(&e8, &c(N0)) && l8 == ((2u64) << 32 | (2u64) << 16 | 1u64)) { println!("whnf s8 proj chain: ret={r8} lens={l8:#x}"); ok = false; }

    if ok { println!("ALL SELF-CHECKS PASS"); }
    std::process::exit((!ok) as i32);
}
