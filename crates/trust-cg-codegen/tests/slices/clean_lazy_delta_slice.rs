// R11 — THE LAZY-DELTA LOOP + QUICK_IS_DEF_EQ COMPLETION: def_eq now decides
// Const-vs-Const pairs by HINT-ORDERED UNFOLDING at the production phase
// position, not by the pillar's eager full-delta whnf. The R10-landed
// configuration (clean_binding_defeq_slice.rs — binding-aware, context-aware,
// EAGER-whnf def_eq, verified native==JIT) is kept VERBATIM as the blind
// control. Production facts transcribed (all verified against
// $HOME/clean/crates/clean-kernel/src, read in full this round):
//
//   * THE LAZY-DELTA LOOP (tc/def_eq/delta.rs:57-168 lazy_delta_reduction):
//     MAX_LAZY_DELTA_ITERATIONS = 10_000, overrun => conservative Ok(false)
//     (termination cap #1773); loop-top hooks IN ORDER: (1) is_def_eq_offset
//     (Nat succ peeling — reduction/nat.rs:60-69 over is_nat_zero_expr
//     :20-26 / is_nat_succ_expr :35-51), (2) reduce_nat under the
//     `(!t.has_fvar_quick() && !s.has_fvar_quick()) || eager_reduce` guard
//     (delta.rs:94), (3) reduce_native (NO fvar guard, delta.rs:103-112),
//     (4) try_monad_reduce with the `reduced != side` progress gate
//     (delta.rs:125-134); then ONE lazy_delta_reduction_step; status map
//     Continue->loop, DefEqual->Ok(true), DefUnknown->Err((t,s)) (the FINAL
//     partially-reduced pair returned to the caller — Lean 4 updates
//     t_n/s_n in place, type_checker.cpp:1094), DefDiff->Ok(false).
//   * THE STEP (delta.rs:170-331): dispatch on (get_delta_const(t),
//     get_delta_const(s)):
//       (Some,Some) -> lazy_delta_step_both: Reducibility::compare — Less =>
//         unfold t first (fallback s), Greater => unfold s first (fallback
//         t), Equal => lazy_delta_step_equal: same name + Regular hint =>
//         the args-only shortcut (args_failed_before / is_def_eq_args_only /
//         cache_args_failure — Lean type_checker.cpp:924-930), then unfold
//         BOTH (t_changed || s_changed => Continue else DefUnknown);
//       (Some,None) -> step_left_only: FIRST try_unfold_proj_app(s) (the rhs
//         proj-headed reconvergence, delta_helpers.rs:221-230 — full-proj
//         whnf_core), THEN unfold t; (None,Some) symmetric;
//       (None,None) -> DefUnknown IMMEDIATELY (NO proj attempt — #3134,
//         delta.rs:300-308).
//     After a Continue: finish_lazy_delta_reduction_step (delta.rs:321-331):
//     t == s (syntactic) => DefEqual; quick_is_def_eq Some(true)/Some(false)
//     => DefEqual/DefDiff; None => Continue. NO proof-irrel inside the loop
//     (#3229 — checked once BEFORE the loop and via the recursive
//     is_def_eq calls after it).
//   * THE ENV CONSULT (delta_helpers.rs:113-156 get_delta_const): a Const
//     head is delta-reducible iff its ConstantInfo has `value.is_some() &&
//     kind != ConstantKind::Opaque && reducibility != Reducibility::Opaque
//     && levels.len() == level_params.len()` (#1277 arity gate). THE HINT IS
//     `Reducibility` (env/types.rs:50-133): Reducible(abbrev, rank 0) >
//     Regular(u32 HEIGHT, rank 1; height = 1 + max height of referenced
//     consts, TALLER UNFOLDS FIRST via h2.cmp(h1)) > Irreducible(rank 2 —
//     note: PARTICIPATES in kernel lazy delta; only elaboration
//     transparency blocks it) > Opaque(rank 3 — theorems (#3305: pulling
//     Eq.trans-style theorem bodies into delta caused unbounded cycles) and
//     ConstantKind::Opaque NEVER delta-unfold). try_unfold_const_in_place
//     (delta_helpers.rs:55-79): unfold_definition (kernel rule — NO
//     transparency, env/unfold.rs:176-192: kind-Opaque blocked, arity
//     checked) then whnf_core_no_delta(replace_head_const(..), CHEAP) in
//     place.
//   * QUICK_IS_DEF_EQ COMPLETION (tc/def_eq/mod.rs:493-524) — the FULL
//     reachable-arm set transcribed: equiv-manager consult (:495-497,
//     [C-cache2] cache layer), (Lam,Lam)|(Pi,Pi) -> is_def_eq_binding
//     (R10), (Sort,Sort) -> levels_eq (= Level::is_def_eq — config.rs:353,
//     override None in the kernel), (MData,MData) sym + the two #3134
//     asymmetric strip arms, (Squash,Squash) — STRUCTURALLY ABSENT (B5:
//     no Squash variant in the modeled core; declared dead), (Lit,Lit) ->
//     PartialEq (incl. the fast Some(false) on unequal literals), catch-all
//     None. clean's kernel ExprKind has NO MVar variant at all — there are
//     no mvar arms to transcribe (the "mvar arms dead in kernel" question
//     resolves to: they do not exist in clean; Lean 4's m_lctx/mvar quick
//     arms have no clean counterpart). There is NO FVar quick arm —
//     FVar==FVar is decided at Phase 3 (mod.rs:423-429).
//   * THE PHASE ORDERING (mod.rs:200-481 is_def_eq_inner + is_def_eq_core),
//     [C-pillar] REPLACED by the production ordering this round — the
//     composed def_eq now COVERS, at their production positions:
//       P0  the `a == b` syntactic fast path (:218, Expr::PartialEq =
//           expr_syntactic_eq);
//       quick_is_def_eq at core entry (:300-304);
//       P1  whnf_core_no_delta(_, cheap_proj=true) both sides (:329-333,
//           = Lean whnf_core(t,false,true)) + the `a_n == b_n` check (:341)
//           + quick re-consult ONLY when a side changed (:347-356);
//       proof-irrelevance (:358-367 — R9 transcription, unchanged);
//       P2  the lazy-delta loop (:386-403);
//       P3  Const-head name+levels / FVar-id compare on the delta-final
//           pair (:408-429);
//       P4  Proj-vs-Proj via lazy_delta_proj_reduction (:431-438,
//           delta.rs:346-384 incl. the reduce_proj_core fallback);
//       P5  second whnf_core_no_delta with FULL projection (cheap=false,
//           :440-451; on change, recurse def_eq — the cheap-vs-full proj
//           reconvergence);
//       P6  is_def_eq_structural (structural.rs:10-71): BVar/FVar/Sort/
//           Const arms, the App SPINE compare (:97-142, branch-sharing
//           cache consult elided [C-cache2]), (Lam,Lam)|(Pi,Pi) ->
//           binding (:40-42), Lit, Proj, and the PRODUCTION eta arms
//           (:47-56 -> eta.rs:27-68 try_eta_expansion_impl: type the other
//           side quick-or-full, whnf, Pi => wrap in a matching Lam and
//           re-enter def_eq — through BINDING, not raw body compare).
//     STILL ELIDED after this round (stated per the discipline):
//       ptr-eq / equiv-manager / def-eq cache / #1773 negative-cache guard
//       / args_failure_cache ([C-cache2] — args_failed_before => always
//       false, cache_args_failure => no-op, at the production call sites);
//       heartbeats/stack_safe (B4); the Bool.true reflection shortcut
//       (:306-327 — no Bool.true in the modeled registry; everywhere-inert)
//       [C-refl]; branch-sharing #3402 (:369-384) [C-cache2]; P7 string-lit
//       expansion (:461-465 — Literal::Str is a u32 tag model, B5)
//       [C-strlit]; P8 unit-like (:467-473 — needs the structure registry,
//       absent) [C-unitlike]; struct-eta inside P6 (structural.rs:158-219)
//       => false stub [C-structeta] (verified separately in the eta rungs);
//       reduce_nat/reduce_int/reduce_native/try_monad_reduce BODIES —
//       transcribed as REGISTRY-EMPTY stubs at the production call
//       positions ([C-nat]/[C-native]/[C-monad]: the modeled env registers
//       no native reducers and the scenario space contains no Nat-arith /
//       monad-class heads, where production returns None identically);
//       eager_reduce fixed false (B4 config).
//
// NEW SCENARIOS (cases 23-27; the R10 23-case set is 0..22 UNCHANGED):
//   case 23 "def.opq" — THE HINT-GATED REJECT (the falsifiability lever):
//     domains Const(opq2) =?= Const(opq1), two ConstantKind::Opaque consts
//     with IDENTICAL hidden values (Sort 0). Production def_eq must NOT
//     unfold them (get_delta_const kind+reducibility gates) => delta
//     exhausts => P3 names differ => P6 Const arm false => REJECT. The
//     R10-config control's eager whnf BLASTS THROUGH both to Sort 0 =>
//     ACCEPT. Divergence set this round = EXACTLY {23}.
//   case 24 "def.hgt" — HINT ORDER: Const(gg) =?= Const(ff), ff :=
//     Const(gg) at Regular(2), gg := Sort 0 at Regular(1). Ordering
//     Greater => the TALLER side (ff) unfolds FIRST, one step, then
//     finish's t==s fires — accepted WITHOUT ever unfolding gg. (The
//     step-count observable lives in probe p0 with the swapped-hint
//     control.)
//   case 25 "def.args" — SAME-HEAD ARGS-ONLY: App(fap, beta-redex) =?=
//     App(fap, Sort 0), same name, Regular => is_def_eq_args_only decides
//     via the recursive def_eq on the args (P1 beta) => DefEqual.
//   case 26 "def.eqh" — HINT-EQUAL BOTH-UNFOLD: Const(e2) =?= Const(e1),
//     both Regular(3), different names => Ordering::Equal, the args block
//     skipped (names differ), BOTH unfold in one step => t==s.
//   case 27 "def.axstuck" — DELTA EXHAUST: fa2/fa1 := distinct AXIOMS
//     (value None — excluded by the is_some gate); both unfold once, then
//     (None,None) => DefUnknown => Err((Const ax2, Const ax1)) => P3/P6
//     reject; the TypeMismatch payload pins the ORIGINAL Pi pair. Both
//     configs REJECT (agreement through the exhaust path).
//
// MODELED BOUNDARIES (R10 list carried forward + R11 items):
//   B1'. env: slice-scan over &[EnvEntry] — EnvEntry is the PRODUCTION
//       ConstantInfo field shape (env/types.rs:235-256: name, level_params,
//       type_, value: Option<Expr>, reducibility, kind; is_reducible — the
//       serde-compat duplicate of reducibility==Reducible — dropped as
//       serialization plumbing). A const's TYPE is now the STORED type_
//       (production env.instantiate_type reads the declared type;
//       supersedes the R6-R10 "inferred type of value" model). B10: no
//       level-param instantiation (values universe-monomorphic;
//       apply_level_subst is the identity on them) — the #1277 arity gate
//       IS transcribed and live (probe p2).
//   B4/B5/B6/B7/B8/B9/B11, [C-refcell], [C-idx]/[C-guard], [C-cache2],
//       [C-inferonly], [C-proj-quick]: unchanged from R10 (see the landed
//       clean_binding_defeq_slice.rs header).
//   B9 additions this round: `Reducibility::compare`'s std::cmp::Ordering
//       -> i32 (-1/0/1) with match arms Less/Greater/Equal -> <0/>0/==0
//       [B9-ord] (the landed str_bytes_cmp convention); kind_rank u8
//       compares as i32; `impl PartialEq for ReductionStatus`-free match
//       via a copy enum with explicit discriminants; iterator zip/all in
//       is_def_eq_args_only / P3 levels / the P6 spine -> index loops;
//       production multi-arg beta (whnf.rs:536-597 instantiate_rev
//       telescope) stays the pillar's one-binder-per-step beta [B9-beta]
//       — identical WHNF fixpoint (the landed pillar convention since R6);
//       the whnf_core trampoline (whnf.rs:359-361 #20) stays direct
//       recursion (same fixpoint, B4 stack discipline).
//   [C-pillar] is RESTATED this round — see the phase table above: the
//       aware def_eq is no longer the eager-whnf pillar; it is the
//       production is_def_eq_core ordering with the elisions listed there.
//       whnf_impl (the FULL whnf used by infer/§5/§7 plumbing) remains the
//       landed pillar shape, now gated by the production unfold_definition
//       rule (kind-Opaque blocked + #1277 arity) [B-whnf-gate].
//   THE *_blind FAMILY IS NOT A TRANSCRIPTION: it is the R10-LANDED
//       configuration (binding-aware + context-aware + EAGER full-delta
//       whnf def_eq) kept as the divergence CONTROL, adapted ONLY to the
//       EnvEntry shape: unfold_const_blind returns ANY Some(value) —
//       ignoring kind/reducibility/arity, exactly the R10 semantics — and
//       const_type_blind reads the stored type_ (the R11 B1' env model,
//       shared so the controls isolate the DEF_EQ difference, not the env
//       model). Its whnf is a SEPARATE _blind copy this round (the aware
//       whnf gained the production unfold gate).
//   lazy_delta_reduction_probe / lazy_delta_reduction_swapped are probe
//       controls: _probe is the transcription text with the production
//       `iterations` counter SURFACED through an out-param;
//       _swapped additionally INVERTS the hint comparison (Less/Greater
//       arm bodies exchanged) — the armed order-falsification control.
//
// SOURCES (verbatim transcription targets in $HOME/clean/crates/clean-kernel/src):
//   tc/def_eq/delta.rs         — ReductionStatus (:18-28), lazy_delta_reduction
//                                (:57-168), lazy_delta_reduction_step (:170-200),
//                                step_both/_equal/_left_only/_right_only/
//                                _no_consts (:202-308), finish (:321-331),
//                                lazy_delta_proj_reduction (:346-384),
//                                args_failed_before/cache_args_failure
//                                (:393-411, [C-cache2] stubs).
//   tc/def_eq/delta_helpers.rs — try_unfold_const_in_place (:55-79),
//                                is_def_eq_args_only (:81-111),
//                                get_delta_const (:113-156),
//                                replace_head_const (:158-172),
//                                reduce_proj_core (:174-190, Str arm
//                                [C-strlit]), try_unfold_proj_app (:221-230).
//   tc/def_eq/mod.rs           — is_def_eq_inner P0 (:218), is_def_eq_core
//                                (:273-481), quick_is_def_eq (:493-524).
//   tc/def_eq/structural.rs    — is_def_eq_structural (:10-71),
//                                is_def_eq_app_spine (:97-142).
//   tc/eta.rs                  — try_eta_expansion_impl (:27-68).
//   tc/whnf.rs                 — whnf_core_no_delta (:272-297 cache-elided) /
//                                whnf_core_inner (:341-505: App beta
//                                (:536-631), Let zeta (:432-434), Const
//                                STUCK in NoDelta modes (:439-442), FVar
//                                zeta (:455-461 — runs in ALL modes incl.
//                                NoDelta), Proj (:462-464 ->
//                                whnf_proj.rs:73-146 cheap/full dispatch),
//                                MData strip (:465)).
//   env/unfold.rs              — unfold_definition (:176-192).
//   env/types.rs               — Reducibility (:50-133 incl. compare/
//                                kind_rank/height), ConstantKind (:220-231),
//                                ConstantInfo shape (:235-256).
//   tc/reduction/nat.rs        — is_nat_zero_expr (:20-26), is_nat_succ_expr
//                                (:35-51), is_def_eq_offset (:60-69).
//   tc/config.rs               — levels_eq (:353-360, override None).
//   (R8-R10 sources for everything unchanged — see the landed
//   clean_binding_defeq_slice.rs / clean_ctx_whnf_slice.rs headers.)
//
// Crate name is load-bearing (appears in the mangled extern-leaf symbols the
// JIT binds): it MUST stay `clean_lazy_delta_slice`.
//
// REGEN (one module per root; trust-ir main — NO frontend changes this round):
//   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//   cd $HOME/trust-ir/frontend
//   env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//     $S/bin/cargo run --bin trust_ir_mir -- \
//     ../../trust-cg/crates/trust-cg-codegen/tests/slices/clean_lazy_delta_slice.rs \
//     --crate-type=lib --mir-emit-closure <root> <out.tir>
//   roots: ld_gate_root | ld_blind_root | ld_probe_root
#![allow(dead_code)]
#![allow(clippy::all)]
#![allow(unused_variables)]

use std::sync::Arc;
use std::hash::{Hash, Hasher};
#[allow(unused_imports)]
use std::convert::TryFrom; // pre-2021 prelude (the MIR driver's edition)

// ════════════════════════════════════════════════════════════════════════════
// clean-kernel name.rs — the production Name (VERBATIM declarations; round-4/5
// transcriptions, harness-proved bit-identical to the real clean-kernel).
// ════════════════════════════════════════════════════════════════════════════

/// name.rs:150-159 (production, non-kani): the recursive inner representation.
#[derive(Clone, Debug)]
pub enum NameInner {
    /// Anonymous name
    Anon,
    /// String component
    Str(Arc<Name>, Arc<str>),
    /// Numeric component (for auto-generated names)
    Num(Arc<Name>, u64),
}

/// name.rs:233-239: hierarchical name with construction-time cached hash.
#[derive(Clone, Debug)]
pub struct Name {
    pub inner: NameInner,
    /// Cached hash value, computed at creation time
    pub cached_hash: u64,
}

/// VERBATIM production `Hash for Name` (name.rs:461-465): O(1) — writes the
/// construction-time cached_hash. This is the impl `hash_name` (Const/Proj
/// payloads) and Level's Param-arm hash reach; the HASHER stays the KaniHasher
/// model (B7), but the CONTENT is now the real murmur/mix chain value.
impl Hash for Name {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        // O(1) hash using cached value
        self.cached_hash.hash(state);
    }
}

// ── clean-kernel expr/meta.rs:264-273 — mix_hash (VERBATIM; shared by the Name
//    compute_hash chain AND the ExprMeta combinators below) ──────────────────

/// MurmurHash2-64A mixing step. Matches Lean 4's `lean_uint64_mix_hash`.
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

// ── clean-kernel env/native_reducers_string.rs:357-393 — murmur_hash_64a ─────
// [T-murmur-idx] index-loop transcription (round 4, harness-proved bit-identical
// against BOTH the as-chunks oracle and clean-kernel golden constants).

pub fn murmur_hash_64a_idx(data: &[u8], seed: u64) -> u64 {
    const M: u64 = 0xc6a4_a793_5bd1_e995;
    const R: u32 = 47;
    let len = data.len();
    let mut h: u64 = seed ^ (len as u64).wrapping_mul(M);

    // Process 8-byte blocks (`as_chunks::<8>()` in production).
    let nblocks = len / 8;
    let mut b = 0usize;
    while b < nblocks {
        let base = b * 8;
        // `u64::from_le_bytes(*block)` assembled byte-by-byte.
        let mut k: u64 = 0;
        let mut j = 0usize;
        while j < 8 {
            k |= (data[base + j] as u64) << (8 * j as u32);
            j += 1;
        }
        k = k.wrapping_mul(M);
        k ^= k >> (R & 63);
        k = k.wrapping_mul(M);
        h ^= k;
        h = h.wrapping_mul(M);
        b += 1;
    }

    // Process the remaining <8 bytes (production: tail iter fold; XOR is
    // order-independent, `h *= M` once iff the tail is non-empty).
    let tail_start = nblocks * 8;
    let mut i = tail_start;
    while i < len {
        h ^= (data[i] as u64) << ((i - tail_start).wrapping_mul(8) & 63);
        i += 1;
    }
    if tail_start < len {
        h = h.wrapping_mul(M);
    }

    h ^= h >> (R & 63);
    h = h.wrapping_mul(M);
    h ^= h >> (R & 63);
    h
}

// ── clean-kernel name.rs:339-364, 483-527 — construction + compute_hash ──────

/// `Name::anon()`: `from_inner(NameInner::Anon)`; `compute_hash(Anon) = 1723`.
pub fn name_anon() -> Name {
    Name {
        inner: NameInner::Anon,
        cached_hash: 1723,
    }
}

/// `Name::str(self, s)` with `compute_hash(Str(p, s)) =
/// mix_hash(p.cached_hash, murmur_hash_64a(s.as_bytes(), 11))`.
/// [T-hash-src] production hashes the bytes read back out of the STORED
/// `Arc<str>`; this transcription hashes the SAME bytes from the incoming
/// `&str` (`Arc::from` copies them verbatim) — value-identical, keeping the
/// hash computation fully in-module (round-4/5 convention).
pub fn name_str_part(parent: Name, part: &str) -> Name {
    let string_hash = murmur_hash_64a_idx(part.as_bytes(), 11);
    let cached_hash = mix_hash(parent.cached_hash, string_hash);
    let inner = NameInner::Str(Arc::new(parent), Arc::from(part));
    Name { inner, cached_hash }
}

/// `Name::num(self, n)`: `compute_hash(Num(p, n)) = mix_hash(p.cached_hash, n)`.
pub fn name_num_part(parent: Name, n: u64) -> Name {
    let cached_hash = mix_hash(parent.cached_hash, n);
    Name {
        inner: NameInner::Num(Arc::new(parent), n),
        cached_hash,
    }
}

// ── `part.parse::<u64>()` — [T-parse] the u64 FromStr decimal path ───────────
// Optional leading '+', at least one digit, digits only, overflow rejects —
// round-4 harness-verified against the REAL `str::parse::<u64>` on every part.
// LIVE here (decl name "thm.42") — it was runtime-dead on round 5's all-Str
// harness names.

pub fn parse_u64_ascii(part: &str) -> (bool, u64) {
    let b = part.as_bytes();
    let mut i = 0usize;
    if b.len() > 0 && b[0] == b'+' {
        i = 1;
    }
    if i >= b.len() {
        return (false, 0);
    }
    let mut acc: u64 = 0;
    while i < b.len() {
        let c = b[i];
        if c < b'0' || c > b'9' {
            return (false, 0);
        }
        let d = (c - b'0') as u64;
        // overflow iff acc*10 + d > u64::MAX  <=>  acc > (MAX - d)/10.
        if acc > (u64::MAX - d) / 10 {
            return (false, 0);
        }
        acc = acc * 10 + d;
        i += 1;
    }
    (true, acc)
}

/// `from_string_uncached`'s fold body (name.rs:558-564), one part:
/// `if let Ok(n) = part.parse::<u64>() { acc.num(n) } else { acc.str(part) }`.
/// (Production `Name::from_string` IS `from_string_uncached` — name.rs:578-581
/// — no interner on this path at all; the round-5 finding.)
pub fn fold_step(acc: Name, part: &str) -> Name {
    let (is_num, n) = parse_u64_ascii(part);
    if is_num {
        name_num_part(acc, n)
    } else {
        name_str_part(acc, part)
    }
}

// ── clean-kernel name.rs:367-377 — production PartialEq ─────────────────────
// [T-eq-iter] hash fast-path VERBATIM; the derived-recursive `NameInner::eq`
// transcribed as an iterative parent-chain walk. `str` equality is length +
// bytewise compare (== `str::eq`), running IN-MODULE over the deref'd pairs.
// EVERY Name equality the decl gate performs goes through this fn.

/// `str::eq` value semantics: length lane, then every byte.
pub fn str_bytes_eq(a: &str, b: &str) -> bool {
    let ab = a.as_bytes();
    let bb = b.as_bytes();
    if ab.len() != bb.len() {
        return false;
    }
    let mut i = 0usize;
    while i < ab.len() {
        if ab[i] != bb[i] {
            return false;
        }
        i += 1;
    }
    true
}

pub fn name_eq(a: &Name, b: &Name) -> bool {
    // Fast path: if hashes differ, names differ (name.rs:370-373).
    if a.cached_hash != b.cached_hash {
        return false;
    }
    // Hashes match, need full comparison (the derived NameInner::eq, walked
    // iteratively leaf-to-root).
    let mut x: &Name = a;
    let mut y: &Name = b;
    loop {
        match (&x.inner, &y.inner) {
            (NameInner::Anon, NameInner::Anon) => return true,
            (NameInner::Str(xp, xs), NameInner::Str(yp, ys)) => {
                if !str_bytes_eq(&**xs, &**ys) {
                    return false;
                }
                x = &**xp;
                y = &**yp;
            }
            (NameInner::Num(xp, xn), NameInner::Num(yp, yn)) => {
                if *xn != *yn {
                    return false;
                }
                x = &**xp;
                y = &**yp;
            }
            _ => return false,
        }
    }
}

// ── clean-kernel name.rs:393-458 — production Ord (Lean cmp_core) ───────────
// [T-ord] `is_norm_lt`'s Param arm is `n1 < n2` = `Name::cmp(n1,n2) == Less`.
// VERBATIM algorithm: collect components root-to-leaf, compare pairwise —
// Num sorts before Str; Num-Num numeric; Str-Str lexicographic (`str::cmp` ==
// `as_bytes().cmp()`: first differing byte, else shorter is Less); shorter
// prefix sorts first. REWRITES (B9): SmallVec<[NameComponent;8]> -> Vec<&Name>
// node stacks (each non-Anon chain node IS exactly one component; pushing
// leaf-to-root then popping yields the root-to-leaf pairwise order);
// `s1.cmp(s2)` -> `str_bytes_cmp` (identical bytewise-then-length order).

/// `str::cmp` == `as_bytes().cmp()`: -1 / 0 / 1.
fn str_bytes_cmp(a: &str, b: &str) -> i32 {
    let ab = a.as_bytes();
    let bb = b.as_bytes();
    let mut i = 0usize;
    while i < ab.len() && i < bb.len() {
        if ab[i] < bb[i] {
            return -1;
        }
        if ab[i] > bb[i] {
            return 1;
        }
        i += 1;
    }
    if ab.len() < bb.len() {
        return -1;
    }
    if ab.len() > bb.len() {
        return 1;
    }
    0
}

pub fn name_cmp_is_lt(a: &Name, b: &Name) -> bool {
    // Collect non-Anon nodes leaf-to-root (pop order = root-to-leaf).
    let mut sa: Vec<&Name> = Vec::new();
    {
        let mut cur: &Name = a;
        loop {
            match &cur.inner {
                NameInner::Anon => break,
                NameInner::Str(p, _) => {
                    sa.push(cur);
                    cur = &**p;
                }
                NameInner::Num(p, _) => {
                    sa.push(cur);
                    cur = &**p;
                }
            }
        }
    }
    let mut sb: Vec<&Name> = Vec::new();
    {
        let mut cur: &Name = b;
        loop {
            match &cur.inner {
                NameInner::Anon => break,
                NameInner::Str(p, _) => {
                    sb.push(cur);
                    cur = &**p;
                }
                NameInner::Num(p, _) => {
                    sb.push(cur);
                    cur = &**p;
                }
            }
        }
    }
    // Pairwise root-to-leaf; run-out = shorter prefix sorts first.
    loop {
        let xa = sa.pop();
        let xb = sb.pop();
        match (xa, xb) {
            (None, None) => return false,
            (None, Some(_)) => return true,
            (Some(_), None) => return false,
            (Some(x), Some(y)) => match (&x.inner, &y.inner) {
                (NameInner::Num(_, n1), NameInner::Num(_, n2)) => {
                    if *n1 != *n2 {
                        return *n1 < *n2;
                    }
                }
                (NameInner::Str(_, s1), NameInner::Str(_, s2)) => {
                    let c = str_bytes_cmp(&**s1, &**s2);
                    if c != 0 {
                        return c < 0;
                    }
                }
                // Num sorts before Str (Lean 4: anonymous_name_lt).
                (NameInner::Num(_, _), NameInner::Str(_, _)) => return true,
                (NameInner::Str(_, _), NameInner::Num(_, _)) => return false,
                // Anon nodes are never pushed.
                _ => {}
            },
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Leaf payloads.
// ════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FVarId(pub u64);

pub type LevelArc = Arc<Level>;

/// VERBATIM `level_arc` (level/mod.rs:36-40, non-kani): wrap a Level in the
/// production pointer type.
#[inline(always)]
fn level_arc(l: Level) -> LevelArc {
    Arc::new(l)
}

// The real Level enum (level/mod.rs:81). Variant ORDER is VERBATIM so
// discriminants match the JIT (Zero=0, Succ=1, Max=2, IMax=3, Param=4).
// Param now carries the PRODUCTION Name.
#[derive(Clone, Debug)]
pub enum Level {
    Zero,
    Succ(LevelArc),
    Max(LevelArc, LevelArc),
    IMax(LevelArc, LevelArc),
    Param(Name),
}

// VERBATIM the cfg(kani) iterative explicit-stack PartialEq (mod.rs:142-168) —
// the body clean's own soundness_harness checks against the derived production
// eq. The Param arm's Name equality is the PRODUCTION name_eq.
impl PartialEq for Level {
    fn eq(&self, other: &Self) -> bool {
        let mut stack: Vec<(&Level, &Level)> = vec![(self, other)];
        while let Some((a, b)) = stack.pop() {
            match (a, b) {
                (Level::Zero, Level::Zero) => {}
                (Level::Succ(la), Level::Succ(lb)) => {
                    stack.push((la, lb));
                }
                (Level::Max(la1, la2), Level::Max(lb1, lb2))
                | (Level::IMax(la1, la2), Level::IMax(lb1, lb2)) => {
                    stack.push((la1, lb1));
                    stack.push((la2, lb2));
                }
                (Level::Param(na), Level::Param(nb)) => {
                    if !name_eq(na, nb) {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }
}

impl Eq for Level {}

// VERBATIM the production cfg(not(kani)) Hash (mod.rs, "matches derived
// behavior": discriminant + recursive field hashing). B7: monomorphized at
// KaniHasher; <Arc<Level> as Hash> is the extern leaf. The Param arm reaches
// the production `Hash for Name` — the REAL cached_hash flows into the state.
impl std::hash::Hash for Level {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Level::Zero => {}
            Level::Succ(l) => l.hash(state),
            Level::Max(l, r) | Level::IMax(l, r) => {
                l.hash(state);
                r.hash(state);
            }
            Level::Param(n) => n.hash(state),
        }
    }
}

impl Level {
    // ── smart constructors (mod.rs:259-359) ──

    pub fn zero() -> Self {
        Level::Zero
    }

    pub fn succ(l: Level) -> Self {
        Level::Succ(level_arc(l))
    }

    // VERBATIM the cfg(kani) `max` path (mod.rs:295-308): the is_geq subsumption
    // shortcut is gated out (breaks the max->is_geq->normalize->imax->max cycle);
    // normalize performs subsumption during canonicalization, so only intermediate
    // Max nodes are less-simplified — correctness preserved. Same selection as the
    // verified level rung.
    pub fn max(l1: Level, l2: Level) -> Self {
        if l1 == l2 {
            return l1;
        }
        if l1.is_zero() {
            return l2;
        }
        if l2.is_zero() {
            return l1;
        }
        Level::Max(level_arc(l1), level_arc(l2))
    }

    // VERBATIM `imax` (mod.rs:324-349).
    pub fn imax(l1: Level, l2: Level) -> Self {
        if l2.is_zero() {
            return Level::Zero;
        }
        if l2.is_nonzero() {
            return Level::max(l1, l2);
        }
        if l1.is_zero() {
            return l2;
        }
        if l1 == Level::succ(Level::zero()) {
            return l2;
        }
        if l1 == l2 {
            return l1;
        }
        Level::IMax(level_arc(l1), level_arc(l2))
    }

    pub fn param(name: Name) -> Self {
        Level::Param(name)
    }

    // VERBATIM `is_zero` (mod.rs:367-374).
    pub fn is_zero(&self) -> bool {
        match self {
            Level::Zero => true,
            Level::Succ(_) | Level::Param(_) => false,
            Level::Max(l1, l2) => l1.is_zero() && l2.is_zero(),
            Level::IMax(_, l2) => l2.is_zero(),
        }
    }

    // VERBATIM `is_nonzero` (mod.rs:382-389).
    fn is_nonzero(&self) -> bool {
        match self {
            Level::Zero | Level::Param(_) => false,
            Level::Succ(_) => true,
            Level::Max(l1, l2) => l1.is_nonzero() || l2.is_nonzero(),
            Level::IMax(_, l2) => l2.is_nonzero(),
        }
    }

    // VERBATIM `has_params_impl` (mod.rs:1245-1254); stack_safe pass-through (B4).
    pub fn has_params(&self) -> bool {
        match self {
            Level::Zero => false,
            Level::Succ(l) => l.has_params(),
            Level::Max(l1, l2) | Level::IMax(l1, l2) => l1.has_params() || l2.has_params(),
            Level::Param(_) => true,
        }
    }

    // VERBATIM `get_offset` (mod.rs:399-408). Iterative Succ-strip.
    fn get_offset(&self) -> (&Level, u32) {
        let mut current = self;
        let mut offset = 0u32;
        while let Level::Succ(inner) = current {
            offset = offset.saturating_add(1);
            current = inner;
        }
        (current, offset)
    }

    // VERBATIM `add_offset` (mod.rs:416-423); `for _ in 0..n` -> counter while (B9).
    fn add_offset(&self, n: u32) -> Level {
        let mut result = self.clone();
        let mut c = 0u32;
        while c < n {
            result = Level::succ(result);
            c += 1;
        }
        result
    }

    // `normalize` (mod.rs:433-435); stack_safe pass-through (B4).
    pub fn normalize(&self) -> Level {
        self.normalize_impl()
    }

    // VERBATIM `kind_ord` (mod.rs:441-449).
    fn kind_ord(&self) -> u8 {
        match self {
            Level::Zero => 0,
            Level::Succ(_) => 1,
            Level::Max(_, _) => 2,
            Level::IMax(_, _) => 3,
            Level::Param(_) => 4,
        }
    }

    // VERBATIM the cfg(kani) iterative `is_norm_lt` (mod.rs:459-493). The Param
    // arm `n1 < n2` is the PRODUCTION Name Ord — name_cmp_is_lt [T-ord].
    fn is_norm_lt(a: &Level, b: &Level) -> bool {
        let mut a = a;
        let mut b = b;
        loop {
            if a == b {
                return false;
            }
            let (base1, off1) = a.get_offset();
            let (base2, off2) = b.get_offset();
            if base1 != base2 {
                if base1.kind_ord() != base2.kind_ord() {
                    return base1.kind_ord() < base2.kind_ord();
                }
                match (base1, base2) {
                    (Level::Param(n1), Level::Param(n2)) => return name_cmp_is_lt(n1, n2),
                    (Level::Max(a1, b1), Level::Max(a2, b2))
                    | (Level::IMax(a1, b1), Level::IMax(a2, b2)) => {
                        if a1 != a2 {
                            a = a1;
                            b = a2;
                            continue;
                        } else {
                            a = b1;
                            b = b2;
                            continue;
                        }
                    }
                    _ => return false,
                }
            } else {
                return off1 < off2;
            }
        }
    }

    // VERBATIM the cfg(kani) iterative `push_max_args` (mod.rs:530-542).
    fn push_max_args(l: &Level, buf: &mut Vec<Level>) {
        let mut stack: Vec<&Level> = vec![l];
        while let Some(current) = stack.pop() {
            match current {
                Level::Max(a, b) => {
                    stack.push(b);
                    stack.push(a);
                }
                _ => buf.push(current.clone()),
            }
        }
    }

    // VERBATIM `mk_max_from_args` (mod.rs:558-571). Right-associated rebuild.
    fn mk_max_from_args(args: &[Level]) -> Level {
        if args.len() == 1 {
            return args[0].clone();
        }
        let mut r = Level::Max(
            level_arc(args[args.len() - 2].clone()),
            level_arc(args[args.len() - 1].clone()),
        );
        let mut i = args.len() - 2;
        while i > 0 {
            i -= 1;
            r = Level::Max(level_arc(args[i].clone()), level_arc(r));
        }
        r
    }

    // VERBATIM `is_explicit` (mod.rs:577-579).
    fn is_explicit(&self) -> bool {
        matches!(self.get_offset().0, Level::Zero)
    }

    // `normalize_impl` (mod.rs:593-639). VERBATIM control flow; Zero/Param arm is
    // the cfg(kani) iterative re-wrap; dead unreachable!() arms replaced with
    // benign in-domain values (non-lowerable &str panic constants) — identical on
    // the reachable domain. Param clone is a real Name clone (Arc bump).
    fn normalize_impl(&self) -> Level {
        let (base, outer_offset) = self.get_offset();

        match base {
            Level::Zero | Level::Param(_) => {
                let mut result = match base {
                    Level::Zero => Level::Zero,
                    Level::Param(n) => Level::Param(n.clone()),
                    _ => Level::Zero,
                };
                let mut c = 0u32;
                while c < outer_offset {
                    result = Level::succ(result);
                    c += 1;
                }
                result
            }
            // DEAD: get_offset strips every Succ layer.
            Level::Succ(_) => base.clone(),

            Level::IMax(l1, l2) => {
                let l1_norm = l1.normalize_impl();
                let l2_norm = l2.normalize_impl();
                let result = Level::imax(l1_norm, l2_norm);
                if matches!(result, Level::Max(_, _)) {
                    result.add_offset(outer_offset).normalize_impl()
                } else {
                    result.add_offset(outer_offset)
                }
            }

            Level::Max(_, _) => Self::normalize_max(base, outer_offset),
        }
    }

    // `normalize_max` (mod.rs:644-690). VERBATIM EXCEPT Step 3: `args.sort_by`
    // (generic core::slice::sort, not lowerable) rewritten as a STABLE INSERTION
    // SORT with the IDENTICAL `is_norm_lt` strict-weak order (B9; proven
    // byte-identical canonical forms in the verified level rung).
    fn normalize_max(base: &Level, outer_offset: u32) -> Level {
        // Step 1: flatten.
        let mut todo = Vec::new();
        Self::push_max_args(base, &mut todo);

        // Step 2: normalize each arg, re-flatten.
        let mut args = Vec::new();
        let mut ti = 0;
        while ti < todo.len() {
            let normed = todo[ti].normalize_impl();
            Self::push_max_args(&normed, &mut args);
            ti += 1;
        }

        // Step 3: sort with is_norm_lt — stable insertion sort (see above).
        let mut i = 1;
        while i < args.len() {
            let mut j = i;
            while j > 0 && Self::is_norm_lt(&args[j], &args[j - 1]) {
                args.swap(j, j - 1);
                j -= 1;
            }
            i += 1;
        }

        // Step 4: dedup same-base (keep largest offset) + explicit subsumption.
        let deduped = Self::dedup_max_args(&args);

        // Step 5: semantic subsumption.
        let mut rargs = Self::subsume_max_args(&deduped);

        // Step 6: reapply outer offset.
        if outer_offset > 0 {
            let mut k = 0;
            while k < rargs.len() {
                rargs[k] = rargs[k].add_offset(outer_offset);
                k += 1;
            }
        }

        if rargs.is_empty() {
            Level::Zero
        } else {
            Self::mk_max_from_args(&rargs)
        }
    }

    // `subsume_max_args` (mod.rs:727-770). VERBATIM; iter().filter()/any()
    // closures rewritten as index loops with IDENTICAL predicates (B9).
    fn subsume_max_args(args: &[Level]) -> Vec<Level> {
        if args.len() <= 1 {
            return args.to_vec();
        }
        let mut any_composite = false;
        {
            let mut c = 0;
            while c < args.len() {
                if matches!(args[c].get_offset().0, Level::Max(_, _) | Level::IMax(_, _)) {
                    any_composite = true;
                    break;
                }
                c += 1;
            }
        }
        if !any_composite {
            return args.to_vec();
        }

        let mut kept: Vec<Level> = Vec::new();
        let mut i = 0;
        while i < args.len() {
            let x = &args[i];
            let x_composite =
                matches!(x.get_offset().0, Level::Max(_, _) | Level::IMax(_, _));

            let mut dominated_by_kept = false;
            {
                let mut ky = 0;
                while ky < kept.len() {
                    let y = &kept[ky];
                    let y_composite =
                        matches!(y.get_offset().0, Level::Max(_, _) | Level::IMax(_, _));
                    if (x_composite || y_composite) && Self::is_geq_core(y, x) {
                        dominated_by_kept = true;
                        break;
                    }
                    ky += 1;
                }
            }
            if dominated_by_kept {
                i += 1;
                continue;
            }

            let mut dominated_by_later_strict = false;
            {
                let mut ly = i + 1;
                while ly < args.len() {
                    let y = &args[ly];
                    let y_composite =
                        matches!(y.get_offset().0, Level::Max(_, _) | Level::IMax(_, _));
                    if (x_composite || y_composite)
                        && Self::is_geq_core(y, x)
                        && !Self::is_geq_core(x, y)
                    {
                        dominated_by_later_strict = true;
                        break;
                    }
                    ly += 1;
                }
            }
            if dominated_by_later_strict {
                i += 1;
                continue;
            }

            kept.push(x.clone());
            i += 1;
        }
        kept
    }

    // VERBATIM `dedup_max_args` (mod.rs:775-824).
    fn dedup_max_args(args: &[Level]) -> Vec<Level> {
        let mut rargs: Vec<Level> = Vec::new();
        let mut i = 0;

        if args[i].is_explicit() {
            while i + 1 < args.len() && args[i + 1].is_explicit() {
                i += 1;
            }
            let k = args[i].get_offset().1;
            let mut j = i + 1;
            while j < args.len() {
                if args[j].get_offset().1 >= k {
                    break;
                }
                j += 1;
            }
            if j < args.len() {
                i += 1;
            }
        }

        if i < args.len() {
            rargs.push(args[i].clone());
            let mut prev_offset = args[i].get_offset();
            i += 1;
            while i < args.len() {
                let curr_offset = args[i].get_offset();
                if prev_offset.0 == curr_offset.0 {
                    if prev_offset.1 < curr_offset.1 {
                        prev_offset = curr_offset;
                        rargs.pop();
                        rargs.push(args[i].clone());
                    }
                } else {
                    prev_offset = curr_offset;
                    rargs.push(args[i].clone());
                }
                i += 1;
            }
        }

        rargs
    }

    // `is_geq` (mod.rs:840-844).
    fn is_geq(l1: &Level, l2: &Level) -> bool {
        let n1 = l1.normalize();
        let n2 = l2.normalize();
        Self::is_geq_core(&n1, &n2)
    }

    // VERBATIM the cfg(kani) `is_geq_core` = is_geq_core_iter (mod.rs:871-915):
    // conjunction worklist, NO hashbrown memoization.
    fn is_geq_core(l1: &Level, l2: &Level) -> bool {
        let mut worklist: Vec<(&Level, &Level)> = vec![(l1, l2)];
        while let Some((l1, l2)) = worklist.pop() {
            if l1 == l2 || l2.is_zero() {
                continue;
            }
            let (base1, offset1) = l1.get_offset();
            if offset1 > 0 && *base1 == *l2 {
                continue;
            }
            if let Level::Max(a, b) = l2 {
                worklist.push((l1, a));
                worklist.push((l1, b));
                continue;
            }
            if let Level::Max(a, b) = l1 {
                if Self::is_geq_leaf(a, l2) || Self::is_geq_leaf(b, l2) {
                    continue;
                }
                return false;
            }
            if let Level::IMax(a, b) = l2 {
                worklist.push((l1, a));
                worklist.push((l1, b));
                continue;
            }
            if let Level::IMax(_, b) = l1 {
                worklist.push((b, l2));
                continue;
            }
            let (base2, offset2) = l2.get_offset();
            if base1 == base2 || base2.is_zero() {
                if offset1 >= offset2 {
                    continue;
                }
                return false;
            }
            if offset1 == offset2 && offset1 > 0 {
                worklist.push((base1, base2));
                continue;
            }
            return false;
        }
        true
    }

    // VERBATIM the cfg(kani) `is_geq_leaf` (mod.rs:920-930).
    fn is_geq_leaf(l1: &Level, l2: &Level) -> bool {
        if l1 == l2 || l2.is_zero() {
            return true;
        }
        let (base1, offset1) = l1.get_offset();
        if offset1 > 0 && *base1 == *l2 {
            return true;
        }
        let (base2, offset2) = l2.get_offset();
        (base1 == base2 || base2.is_zero()) && offset1 >= offset2
    }

    // ── THE VERIFIED UNIVERSE PILLAR: `is_def_eq` (mod.rs:1026-1033) — VERBATIM. ──
    pub fn is_def_eq(l1: &Level, l2: &Level) -> bool {
        if l1 == l2 {
            return true;
        }
        l1.normalize() == l2.normalize()
    }
}

pub type LevelVec = Vec<Level>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Literal { Nat(u64), Str(u32) }

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BinderData { pub info: u8, pub mult: u8 }

// ════════════════════════════════════════════════════════════════════════════
// expr/meta.rs — KaniHasher (B7 payload-hasher model; the Name/Level content
// flowing through it is now the REAL production cached_hash chain) + the
// monomorphic per-type hashers.
// ════════════════════════════════════════════════════════════════════════════

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
// JIT symbols. Same as the prior verified rungs.
#[inline]
fn hash_name(value: &Name) -> u64 {
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
fn hash_lit(value: &Literal) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

/// `hash_to_u64(levels)` for `levels: &LevelVec` — the production Const-arm
/// levels_hash input (expr/kind.rs:569). `<Vec<Level> as Hash>` ==
/// `<[Level] as Hash>`: `write_length_prefix(len)` [KaniHasher: write_usize ->
/// write_u64] then per-element `Level::hash` — replayed as an explicit loop
/// (B9; the library generic slice-hash body is not lowerable). Identical
/// hasher-write sequence.
#[inline]
fn hash_levels(value: &[Level]) -> u64 {
    let mut hasher = KaniHasher::new();
    hasher.write_u64(value.len() as u64);
    let mut i = 0usize;
    while i < value.len() {
        value[i].hash(&mut hasher);
        i += 1;
    }
    hasher.finish()
}

// clean's Level has NO MVar variant (mod.rs:81-92); the production non-kani
// body recurses structurally and is everywhere-false — the cfg(kani) selection
// (unconditional false) is taken, as in every verified rung.
#[inline]
fn level_has_mvar(_l: &Level) -> bool { false }

// ════════════════════════════════════════════════════════════════════════════
// expr/meta.rs — VERBATIM ExprMeta (identical to the verified rungs).
// ════════════════════════════════════════════════════════════════════════════

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
    /// R10 NEW — meta.rs:136-138 VERBATIM: any loose bound variables?
    fn has_loose_bvars(self) -> bool {
        self.loose_bvar_range() > 0
    }

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

// The production ExprKind core (B5: the 11-variant subset the prior rungs verify).
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
            // ── THE FIXED T1 NUANCE: VERBATIM the production Const arm
            // (expr/kind.rs:567-581) — levels_hash mixed into the node hash,
            // has_level_param / has_level_mvar derived from the levels. The
            // `.iter().any(..)` predicates are index loops (B9). ──
            ExprKind::Const(name, levels) => {
                let name_hash = hash_name(name);
                let levels_hash = hash_levels(levels);
                let mut has_level_param = false;
                {
                    let mut li = 0usize;
                    while li < levels.len() {
                        if levels[li].has_params() {
                            has_level_param = true;
                            break;
                        }
                        li += 1;
                    }
                }
                let mut has_level_mvar = false;
                {
                    let mut li = 0usize;
                    while li < levels.len() {
                        if level_has_mvar(&levels[li]) {
                            has_level_mvar = true;
                            break;
                        }
                        li += 1;
                    }
                }
                ExprMeta::pack(
                    mix_hash(5, mix_hash(name_hash, levels_hash)) as u32,
                    0,
                    0,
                    false,
                    false,
                    has_level_mvar,
                    has_level_param,
                )
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
    // The O(1) metadata quick checks (expr/mod.rs:289-303) — VERBATIM.
    fn has_fvar_quick(&self) -> bool { self.meta.has_fvar() }
    fn has_expr_mvar_quick(&self) -> bool { self.meta.has_expr_mvar() }
    fn has_level_mvar_quick(&self) -> bool { self.meta.has_level_mvar() }
    /// R10 NEW — expr/subst.rs:628-631 VERBATIM: O(1) via cached metadata.
    /// The is_def_eq_binding no-loose-bvars fast-path gate.
    fn has_loose_bvars(&self) -> bool {
        self.meta.has_loose_bvars()
    }
    fn bvar(idx: u32) -> Self { Expr::from_kind(ExprKind::BVar(idx)) }
    fn cnst(name: Name) -> Self { Expr::from_kind(ExprKind::Const(name, Vec::new())) }
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

    // VERBATIM lift_at (verified substitution core).
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
    // VERBATIM instantiate / instantiate_at (the beta primitive). Name copies
    // are now real Name clones (Arc bumps) — the production text.
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
            ExprKind::Let(name, ty, val_e, body, nondep) => Expr::lett(name.clone(), ty.instantiate_at(val, depth), val_e.instantiate_at(val, depth), body.instantiate_at(val, depth.saturating_add(1)), *nondep),
            ExprKind::Proj(name, idx, e) => Expr::proj(name.clone(), *idx, e.instantiate_at(val, depth)),
            _ => self.clone(),
        }
    }
    // ── expr/subst.rs:897-903 abstract_fvar / :312-380 Abstractor — the
    // CLOSE half of the production open→infer→close binder discipline:
    // replace FVar(id) at binder depth d with BVar(d), shifting loose BVars
    // >= d up by one (checked_add_u32 == saturating_add,
    // local_context.rs:26-28). The ExprFolderOpt walk (fold_opt_or_clone,
    // visitor_opt.rs:133-231) is transcribed as direct recursion [T-abs];
    // the pointer-identity memo is elided (pure perf — subst.rs:305-310's
    // own SOUNDNESS note: byte-identical output) and the `should_descend`
    // O(1) meta gate (:332-334) is transcribed VERBATIM. Rebuilds go through
    // the from_kind smart ctors (== the folder's ek(..) merges; child-Arc
    // sharing differences cannot change values or metas — meta is computed
    // from child metas). ──
    fn abstract_fvar(&self, id: FVarId) -> Expr {
        self.abstract_fvar_at(id, 0)
    }
    fn abstract_fvar_at(&self, id: FVarId, depth: u32) -> Expr {
        // should_descend (subst.rs:332-334): no FVar anywhere below AND no
        // loose BVar at-or-above the cut => unchanged.
        if !(self.has_fvar_quick() || depth < self.loose_bvar_range()) {
            return self.clone();
        }
        match &self.kind {
            // fold_fvar_opt (subst.rs:352-358).
            ExprKind::FVar(fid) => {
                if *fid == id {
                    Expr::bvar(depth)
                } else {
                    self.clone()
                }
            }
            // fold_bvar_opt (subst.rs:360-370): shift loose BVars up past
            // the new binder.
            ExprKind::BVar(idx) => {
                if *idx >= depth {
                    Expr::bvar(idx.saturating_add(1))
                } else {
                    self.clone()
                }
            }
            ExprKind::App(f, a) => Expr::app(
                f.abstract_fvar_at(id, depth),
                a.abstract_fvar_at(id, depth),
            ),
            // fold_binder_body_opt (subst.rs:372-378): body at depth+1.
            ExprKind::Lam(bd, ty, body) => Expr::lam(
                *bd,
                ty.abstract_fvar_at(id, depth),
                body.abstract_fvar_at(id, depth.saturating_add(1)),
            ),
            ExprKind::Pi(bd, ty, body) => Expr::pi(
                *bd,
                ty.abstract_fvar_at(id, depth),
                body.abstract_fvar_at(id, depth.saturating_add(1)),
            ),
            // visitor_opt.rs:218-224: Let ty/val at depth, body at depth+1.
            ExprKind::Let(name, ty, val, body, nondep) => Expr::lett(
                name.clone(),
                ty.abstract_fvar_at(id, depth),
                val.abstract_fvar_at(id, depth),
                body.abstract_fvar_at(id, depth.saturating_add(1)),
                *nondep,
            ),
            ExprKind::Proj(name, idx, e) => {
                Expr::proj(name.clone(), *idx, e.abstract_fvar_at(id, depth))
            }
            ExprKind::MData(tag, e) => Expr::mdata(*tag, e.abstract_fvar_at(id, depth)),
            // Sort/Const/Lit carry no FVar/BVar (folder returns None).
            _ => self.clone(),
        }
    }
    // ── expr/subst.rs:922-925 subst_fvar / :385-402 FVarSubst — the ZETA
    // substitution (Let bodies): replace FVar(id) with `replacement`, NO
    // depth tracking ("FVars are not affected by binder scope"). Direct
    // recursion [T-fsubst]; should_descend = has_fvar_quick VERBATIM
    // (:391-393). ──
    fn subst_fvar(&self, id: FVarId, replacement: &Expr) -> Expr {
        if !self.has_fvar_quick() {
            return self.clone();
        }
        match &self.kind {
            ExprKind::FVar(fid) => {
                if *fid == id {
                    replacement.clone()
                } else {
                    self.clone()
                }
            }
            ExprKind::App(f, a) => Expr::app(
                f.subst_fvar(id, replacement),
                a.subst_fvar(id, replacement),
            ),
            ExprKind::Lam(bd, ty, body) => Expr::lam(
                *bd,
                ty.subst_fvar(id, replacement),
                body.subst_fvar(id, replacement),
            ),
            ExprKind::Pi(bd, ty, body) => Expr::pi(
                *bd,
                ty.subst_fvar(id, replacement),
                body.subst_fvar(id, replacement),
            ),
            ExprKind::Let(name, ty, val, body, nondep) => Expr::lett(
                name.clone(),
                ty.subst_fvar(id, replacement),
                val.subst_fvar(id, replacement),
                body.subst_fvar(id, replacement),
                *nondep,
            ),
            ExprKind::Proj(name, idx, e) => {
                Expr::proj(name.clone(), *idx, e.subst_fvar(id, replacement))
            }
            ExprKind::MData(tag, e) => Expr::mdata(*tag, e.subst_fvar(id, replacement)),
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

// ════════════════════════════════════════════════════════════════════════════
// tc/local_context.rs — THE PRODUCTION LOCAL CONTEXT (the B3 de-modeling).
// LocalDecl (:31-43) VERBATIM. LocalContext (:47-58): the decls Vec + the
// MONOTONIC `next_id: u64` fresh-FVarId counter VERBATIM (`id =
// FVarId(next_id); next_id += 1` — never decremented, ids never reused after
// pop: the #1773 FVarId-unreachability invariant). index_by_id/used_ids
// (hashbrown) modeled: [C-idx]/[C-guard] — see the file header.
// ════════════════════════════════════════════════════════════════════════════

/// tc/local_context.rs:31-43 — VERBATIM.
#[derive(Clone, Debug)]
pub struct LocalDecl {
    /// Unique identifier
    pub id: FVarId,
    /// User-facing name
    pub name: Name,
    /// Type of the variable
    pub type_: Expr,
    /// Value (for let bindings)
    pub value: Option<Expr>,
    /// Binder data (info + multiplicity)
    pub bi: BinderData,
}

/// tc/local_context.rs:47-58 — decls + next_id VERBATIM; index/used modeled
/// ([C-idx]/[C-guard]).
pub struct LocalContext {
    pub decls: Vec<LocalDecl>,
    pub used_ids: Vec<FVarId>,
    pub next_id: u64,
    pub guard_trips: u64,
}

impl LocalContext {
    /// `LocalContext::new()` (:67-69) — empty context, next_id = 0.
    pub fn new() -> Self {
        LocalContext {
            decls: Vec::new(),
            used_ids: Vec::new(),
            next_id: 0,
            guard_trips: 0,
        }
    }

    /// [C-guard] the two production freshness assert! CONDITIONS (push and
    /// push_let share them, :82-89/:113-120): an ACTIVE duplicate (same id
    /// still in decls — production: `!index_by_id.contains_key(&id)`) and an
    /// EVER-USED duplicate (production: `used_ids.insert(id)` returning
    /// false). A would-be panic increments guard_trips instead of aborting.
    fn freshness_guard(&mut self, id: FVarId) {
        let mut active_dup = false;
        {
            let mut i = 0usize;
            while i < self.decls.len() {
                if self.decls[i].id == id {
                    active_dup = true;
                    break;
                }
                i += 1;
            }
        }
        if active_dup {
            // production: assert!(.., "generated active duplicate FVarId")
            self.guard_trips += 1;
        }
        let mut ever_used = false;
        {
            let mut i = 0usize;
            while i < self.used_ids.len() {
                if self.used_ids[i] == id {
                    ever_used = true;
                    break;
                }
                i += 1;
            }
        }
        if ever_used {
            // production: assert!(.., "generated previously-used FVarId")
            self.guard_trips += 1;
        } else {
            self.used_ids.push(id);
        }
    }

    /// `push` (:79-99) — THE FRESH-FVAR ALLOCATOR, VERBATIM: mint the id from
    /// the monotonic counter, guard freshness, append the decl (value: None).
    /// `bi: impl Into<BinderData>` monomorphized at BinderData (identity
    /// Into — the tc always passes `*bi`) [B9].
    pub fn push(&mut self, name: Name, type_: Expr, bi: BinderData) -> FVarId {
        let id = FVarId(self.next_id);
        self.next_id += 1;
        self.freshness_guard(id);
        self.decls.push(LocalDecl {
            id,
            name,
            type_,
            value: None,
            bi,
        });
        id
    }

    /// `push_let` (:109-129) — VERBATIM; value: Some(value); bi =
    /// BinderInfo::Default.into() = BinderData { Default, Many } (the
    /// production From<BinderInfo>, expr/types.rs:145-153) = bdm().
    pub fn push_let(&mut self, name: Name, type_: Expr, value: Expr) -> FVarId {
        let id = FVarId(self.next_id);
        self.next_id += 1;
        self.freshness_guard(id);
        self.decls.push(LocalDecl {
            id,
            name,
            type_,
            value: Some(value),
            bi: bdm(),
        });
        id
    }

    /// `pop` (:189-193) — VERBATIM minus the index-map removal ([C-idx]: the
    /// backward scan never sees popped entries). The popped decl is dropped
    /// (leak model). Popped ids are NEVER re-minted (next_id is monotonic).
    pub fn pop(&mut self) {
        let _decl = self.decls.pop();
    }

    /// R10 NEW — `truncate_to` (:236-242) VERBATIM minus the index-map
    /// removal ([C-idx]: the backward scan never sees popped entries).
    /// "Used by iterative binder comparison (`is_def_eq_binding`) to
    /// batch-restore context state after processing N consecutive binders."
    /// next_id is NOT touched — popped ids are never re-minted.
    pub fn truncate_to(&mut self, target_len: usize) {
        while self.decls.len() > target_len {
            let _decl = self.decls.pop();
        }
    }

    /// `get` (:201-204) — [C-idx] BACKWARD scan (latest pushed position wins,
    /// exactly like the overwriting HashMap index).
    pub fn get(&self, id: FVarId) -> Option<&LocalDecl> {
        let mut i = self.decls.len();
        while i > 0 {
            i -= 1;
            if self.decls[i].id == id {
                return Some(&self.decls[i]);
            }
        }
        None
    }

    /// `len` (:212-214).
    pub fn len(&self) -> usize {
        self.decls.len()
    }
}

// ════════════════════════════════════════════════════════════════════════════
// R10 NEW — the production `Expr::PartialEq` (expr/mod.rs:363-375): the
// ExprMeta-word pre-filter (ExprMeta PartialEq is the raw u64 compare —
// meta.rs:246-250) then the DERIVED `ExprKind` eq. This is the exact
// relation binding.rs's `ty1 != ty2` syntactic pre-check (#3230) evaluates.
// UNLIKE the pillar's structural_eq (def-eq-shaped: level_eq normalizes,
// binder data and Let names ignored), the derived kind eq compares
// BinderData fieldwise, Let names (Name::eq = name_eq) and nondep flags,
// MData tags, and Levels with the STRUCTURAL Level PartialEq. [B9]:
// derived-eq → explicit recursion; Vec<Level> eq → index loop.
// ════════════════════════════════════════════════════════════════════════════

fn level_vec_syntactic_eq(a: &[Level], b: &[Level]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0usize;
    while i < a.len() {
        if !(a[i] == b[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn expr_syntactic_eq(a: &Expr, b: &Expr) -> bool {
    // expr/mod.rs:365-369 — metadata pre-filter, O(1).
    if a.meta.raw() != b.meta.raw() {
        return false;
    }
    // expr/mod.rs:371-372 — `self.kind == other.kind` (derived).
    match (&a.kind, &b.kind) {
        (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
        (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
        (ExprKind::Sort(l1), ExprKind::Sort(l2)) => l1 == l2,
        (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => {
            name_eq(n1, n2) && level_vec_syntactic_eq(ls1, ls2)
        }
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
            expr_syntactic_eq(f1, f2) && expr_syntactic_eq(a1, a2)
        }
        (ExprKind::Lam(b1, t1, y1), ExprKind::Lam(b2, t2, y2))
        | (ExprKind::Pi(b1, t1, y1), ExprKind::Pi(b2, t2, y2)) => {
            // derived BinderData eq = fieldwise [B9].
            b1.info == b2.info
                && b1.mult == b2.mult
                && expr_syntactic_eq(t1, t2)
                && expr_syntactic_eq(y1, y2)
        }
        (ExprKind::Let(n1, t1, v1, y1, d1), ExprKind::Let(n2, t2, v2, y2, d2)) => {
            name_eq(n1, n2)
                && expr_syntactic_eq(t1, t2)
                && expr_syntactic_eq(v1, v2)
                && expr_syntactic_eq(y1, y2)
                && *d1 == *d2
        }
        (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
        (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
            name_eq(n1, n2) && *i1 == *i2 && expr_syntactic_eq(e1, e2)
        }
        (ExprKind::MData(t1, e1), ExprKind::MData(t2, e2)) => {
            *t1 == *t2 && expr_syntactic_eq(e1, e2)
        }
        _ => false,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// env/types.rs:50-133 — Reducibility, THE HINT (VERBATIM declarations;
// compare() returns i32 [B9-ord]: -1 = unfold self first, +1 = unfold other
// first, 0 = unfold both — the exact Ordering semantics of the production
// compare, Lean 4 declaration.cpp:24-49).
// ════════════════════════════════════════════════════════════════════════════

/// Variant ORDER is VERBATIM so discriminants match the JIT decode
/// (Reducible=0, Regular=1, Irreducible=2, Opaque=3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reducibility {
    /// Always unfoldable — abbreviations/`@[reducible]` (Lean 4: `Abbreviation`)
    Reducible,
    /// Normal definitions with a computed height (Lean 4: `Regular(height)`)
    Regular(u32),
    /// Only unfoldable in All mode (`@[irreducible]`) — NOTE: participates
    /// in the KERNEL lazy-delta loop (only rank-ordered after Regular).
    Irreducible,
    /// Never unfoldable (theorems/opaque declarations) (Lean 4: `Opaque`)
    Opaque,
}

impl Reducibility {
    /// `height` (env/types.rs:70-75) — 0 for non-Regular variants.
    pub fn height(&self) -> u32 {
        match self {
            Reducibility::Regular(h) => *h,
            _ => 0,
        }
    }

    /// `is_regular` (env/types.rs:80-82).
    pub fn is_regular(&self) -> bool {
        matches!(self, Reducibility::Regular(_))
    }

    /// `kind_rank` (env/types.rs:113-120) — lower = more reducible = unfold
    /// first. Returned as i32 for the [B9-ord] compare.
    fn kind_rank(&self) -> i32 {
        match self {
            Reducibility::Reducible => 0,
            Reducibility::Regular(_) => 1,
            Reducibility::Irreducible => 2,
            Reducibility::Opaque => 3,
        }
    }

    /// `compare` (env/types.rs:94-109) — [B9-ord]: std::cmp::Ordering -> i32.
    /// Same kind + both Regular: higher height = unfold first = negative
    /// (production `h2.cmp(h1)`); same kind otherwise: 0; different kinds:
    /// lower rank = more reducible = negative (production `a.cmp(&b)`).
    pub fn compare(&self, other: &Reducibility) -> i32 {
        let a = self.kind_rank();
        let b = other.kind_rank();
        if a == b {
            match (self, other) {
                (Reducibility::Regular(h1), Reducibility::Regular(h2)) => {
                    // Higher height = unfold first = Less (reversed cmp).
                    if *h2 < *h1 {
                        -1
                    } else if *h2 > *h1 {
                        1
                    } else {
                        0
                    }
                }
                _ => 0,
            }
        } else if a < b {
            -1
        } else {
            1
        }
    }
}

/// env/types.rs:220-231 — ConstantKind, VERBATIM variant order
/// (Definition=0, Theorem=1, Opaque=2, Axiom=3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstantKind {
    /// Normal definition with a computable value
    Definition,
    /// Theorem — proof-irrelevant, never compared by value
    Theorem,
    /// Opaque constant — has a hidden value not exposed during reduction
    Opaque,
    /// Axiom — no value, taken on faith
    Axiom,
}

/// env/types.rs:235-256 — the PRODUCTION ConstantInfo field shape (B1'):
/// name, level_params, type_, value, reducibility, kind. The serde-compat
/// `is_reducible` duplicate (== reducibility matches Reducible) is dropped
/// as serialization plumbing. type_/value are stored by value as in
/// production.
pub struct EnvEntry {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub type_: Expr,
    pub value: Option<Expr>,
    pub reducibility: Reducibility,
    pub kind: ConstantKind,
}

// ── Modeled environment (B1'): slice-scan over the ConstantInfo-shaped
// entries. Verifier layout: 2 fat-pointer fields, 4 words (unchanged). ──
pub struct Verifier<'env> {
    pub env: &'env [EnvEntry],
    pub ctors: &'env [(Name, u32)],
}

// ── The slice TypeError (tc/infer.rs TypeError, reachable subset in source
// shape; carries the offending Expr/Name directly — no format!/String). ──
#[derive(Clone, Debug)]
pub enum TypeError {
    UnboundVariable(u32),
    UnknownFVar(FVarId),
    UnknownConst(Name),
    TypeMismatch { expected: Arc<Expr>, inferred: Arc<Expr> },
    NotAPi { ty: Arc<Expr> },
    ExpectedSort { ty: Arc<Expr> },
    SortDepthExceeded { depth: u32 },
    Unsupported,
}

// ════════════════════════════════════════════════════════════════════════════
// tc/def_eq/delta.rs:18-28 — ReductionStatus, VERBATIM (variant order:
// Continue=0, DefEqual=1, DefUnknown=2, DefDiff=3).
// ════════════════════════════════════════════════════════════════════════════
#[derive(Clone, Copy, Debug)]
enum ReductionStatus {
    /// Made progress (unfolded something), continue looping.
    Continue,
    /// Definitively equal (same-head argument-wise match succeeded).
    DefEqual,
    /// Neither side is delta-reducible; delta is exhausted.
    DefUnknown,
    /// Definitively not equal (`quick_is_def_eq` returned `Some(false)`).
    DefDiff,
}

impl<'env> Verifier<'env> {
    // ── env lookups (B1' slice-scan; entry-name equality = PRODUCTION
    // name_eq). get_const == the scan itself. ──
    fn find_entry(&self, name: &Name) -> Option<&EnvEntry> {
        let mut i: usize = 0;
        let n = self.env.len();
        while i < n {
            let entry = &self.env[i];
            if name_eq(&entry.name, name) {
                return Some(entry);
            }
            i += 1;
        }
        None
    }

    /// env/unfold.rs:176-192 unfold_definition — THE KERNEL RULE, VERBATIM:
    /// no transparency; ConstantKind::Opaque blocked; axioms excluded by the
    /// value `?`; the #1277 level-arity gate. B10: apply_level_subst is the
    /// identity on the universe-monomorphic modeled values (no substitution
    /// performed). `?`-on-Option → match [B9].
    fn unfold_definition_model(&self, name: &Name, levels: &[Level]) -> Option<Expr> {
        let info = match self.find_entry(name) {
            Some(i) => i,
            None => return None,
        };
        // [B9-matches] `info.kind == ConstantKind::Opaque` -> matches!
        // (identical discriminant test on fieldless variants; the frontend
        // does not lower whole-enum comparison constants).
        if matches!(info.kind, ConstantKind::Opaque) {
            return None;
        }
        let value = match &info.value {
            Some(v) => v,
            None => return None,
        };
        // Enforce level parameter count match — reject silent truncation (#1277)
        if info.level_params.len() != levels.len() {
            return None;
        }
        Some(value.clone())
    }

    fn get_constructor_num_params(&self, name: &Name) -> Option<u32> {
        let mut i: usize = 0;
        let n = self.ctors.len();
        while i < n {
            let entry = &self.ctors[i];
            if name_eq(&entry.0, name) { return Some(entry.1); }
            i += 1;
        }
        None
    }

    /// B1' const type: the STORED declared type (production
    /// env.instantiate_type; B10: no level instantiation).
    fn const_type(&self, name: &Name) -> Option<Expr> {
        match self.find_entry(name) {
            Some(info) => Some(info.type_.clone()),
            None => None,
        }
    }

    fn try_iota_reduction(&self, _e: &Expr) -> Option<Expr> { None } // B8
    fn try_quot_reduction(&self, _e: &Expr) -> Option<Expr> { None } // B8

    // ── The loop-top / whnf hook stubs at their production call positions.
    // [C-nat]/[C-native]/[C-monad]: the modeled env registers no native
    // reducers and the scenario space contains no Nat-arithmetic or
    // monad-class Const heads — production reduce_nat (reduction/nat.rs:77,
    // keyed on Nat.succ/add/... heads), reduce_native (delta_helpers.rs:250,
    // keyed on env.get_native_reducer — registry empty) and try_monad_reduce
    // (monad_reduce.rs:119, keyed on Bind.bind/Pure.pure heads) return None
    // on every input the scenarios produce; the stubs are behaviorally
    // identical there. is_def_eq_offset IS transcribed (below) — it is
    // keyed only on Nat LITERALS + the Nat.zero/Nat.succ names (B11). ──
    fn reduce_nat(&self, _e: &Expr) -> Option<Expr> { None }
    fn reduce_native(&self, _e: &Expr) -> Option<Expr> { None }
    fn try_monad_reduce(&self, _e: &Expr) -> Option<Expr> { None }
    /// eager_reduce: production Cell<bool>, false in the kernel gate (B4).
    fn eager_reduce(&self) -> bool { false }

    // ── tc/reduction/nat.rs:20-26 is_nat_zero_expr — VERBATIM on the
    // Literal::Nat(u64) core (BigNat::Small model); the Const arm's
    // interned NAT_ZERO is the per-call two-part name (B11). ──
    fn is_nat_zero_expr(e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Lit(Literal::Nat(n)) => *n == 0,
            ExprKind::Const(name, levels) => {
                levels.len() == 0 && name_eq(name, &nat_zero_name())
            }
            _ => false,
        }
    }

    /// tc/reduction/nat.rs:35-51 is_nat_succ_expr — VERBATIM on the u64
    /// model: literal n > 0 -> literal n-1; App(Const(Nat.succ,[]), arg) ->
    /// arg. `BigNat::pred()? ` → the n>0 guard [B9].
    fn is_nat_succ_expr(e: &Expr) -> Option<Expr> {
        match &e.kind {
            ExprKind::Lit(Literal::Nat(n)) => {
                if *n > 0 {
                    Some(Expr::nat(*n - 1))
                } else {
                    None
                }
            }
            ExprKind::App(f, arg) => {
                if let ExprKind::Const(name, levels) = &f.kind {
                    if levels.len() == 0 && name_eq(name, &nat_succ_name()) {
                        return Some(arg.as_ref().clone());
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// tc/reduction/nat.rs:60-69 is_def_eq_offset — VERBATIM: both-zero ->
    /// Some(true); both-succ -> peel and recurse through the full def_eq.
    fn is_def_eq_offset(&self, t: &Expr, s: &Expr, ctx: &mut LocalContext) -> Option<bool> {
        if Self::is_nat_zero_expr(t) && Self::is_nat_zero_expr(s) {
            return Some(true);
        }
        let pred_t = Self::is_nat_succ_expr(t);
        let pred_s = Self::is_nat_succ_expr(s);
        match (pred_t, pred_s) {
            (Some(pt), Some(ps)) => Some(self.def_eq_impl(&pt, &ps, ctx)),
            _ => None,
        }
    }

    // ════════════════════════════════════════════════════════════════════
    // FULL WHNF (the pillar, context-aware since R9) — used by infer/§5/§7
    // plumbing and the cheap_proj=false projection operand. THE R11 CHANGE
    // [B-whnf-gate]: the Const arm unfolds through the PRODUCTION
    // unfold_definition rule (kind-Opaque blocked, #1277 arity) instead of
    // the raw slice-scan; the App stuck branch consults the reduce_nat/
    // reduce_native hook positions (registry-empty stubs), matching
    // whnf_core_inner Full mode (whnf.rs:421-424 / :616-626).
    // ════════════════════════════════════════════════════════════════════
    fn whnf_impl(&self, e: &Expr, ctx: &LocalContext) -> Expr { self.whnf_inner(e, ctx) }
    fn whnf_inner(&self, e: &Expr, ctx: &LocalContext) -> Expr {
        match &e.kind {
            ExprKind::App(f, a) => {
                let f_whnf = self.whnf_impl(f, ctx);
                match &f_whnf.kind {
                    ExprKind::Lam(_, _, body) => { let reduced = body.instantiate(a); self.whnf_impl(&reduced, ctx) }
                    _ => {
                        let app = Expr::from_kind(ExprKind::App(Arc::new(f_whnf), a.clone()));
                        if let Some(reduced) = self.try_iota_reduction(&app) { return self.whnf_impl(&reduced, ctx); }
                        if let Some(reduced) = self.try_quot_reduction(&app) { return self.whnf_impl(&reduced, ctx); }
                        if let Some(reduced) = self.reduce_nat(&app) { return self.whnf_impl(&reduced, ctx); }
                        if let Some(reduced) = self.reduce_native(&app) { return self.whnf_impl(&reduced, ctx); }
                        app
                    }
                }
            }
            ExprKind::Let(_, _, val, body, _) => { let reduced = body.instantiate(val); self.whnf_impl(&reduced, ctx) }
            // [B-whnf-gate] whnf.rs:443-446 Full mode: unfold_definition_cached
            // ([C-cache2] cache elided) = the production kernel unfold rule.
            ExprKind::Const(name, levels) => match self.unfold_definition_model(name, levels) {
                Some(val) => self.whnf_impl(&val, ctx),
                None => e.clone(),
            },
            // R9 — tc/whnf.rs:455-461 FVar ZETA (runs in ALL whnf modes).
            ExprKind::FVar(id) => {
                let val_opt: Option<Expr> = match ctx.get(*id) {
                    Some(d) => d.value.clone(),
                    None => None,
                };
                match val_opt {
                    Some(val) => self.whnf_impl(&val, ctx),
                    None => e.clone(),
                }
            }
            ExprKind::Proj(struct_name, idx, expr) => self.reduce_proj(struct_name, *idx, expr, ctx),
            ExprKind::MData(_, inner) => self.whnf_impl(inner, ctx),
            _ => e.clone(),
        }
    }
    fn reduce_proj(&self, struct_name: &Name, idx: u32, expr: &Expr, ctx: &LocalContext) -> Expr {
        let expr_whnf = self.whnf_impl(expr, ctx);
        let head = expr_whnf.get_app_fn();
        if let ExprKind::Const(ctor_name, _) = &head.kind {
            if let Some(num_params) = self.get_constructor_num_params(ctor_name) {
                let args = expr_whnf.get_app_args();
                let field_idx = num_params as usize + idx as usize;
                if field_idx < args.len() { return self.whnf_impl(&args[field_idx], ctx); }
            }
        }
        Expr::from_kind(ExprKind::Proj(struct_name.clone(), idx, Arc::new(expr_whnf)))
    }

    // ════════════════════════════════════════════════════════════════════
    // R11 NEW — WHNF_CORE_NO_DELTA (tc/whnf.rs:272-297 wrapper, cache
    // elided [C-cache2], over whnf_core_inner :341-505 in the two NoDelta
    // modes): beta / zeta / FVar-zeta / proj / MData, NO Const unfolding.
    //   cheap_proj=true  == Lean whnf_core(e,false,true)  (P1, the delta
    //                       loop's in-place reducer);
    //   cheap_proj=false == Lean whnf_core(e,false,false) (P5, try_unfold_
    //                       proj_app) — the projection OPERAND gets the
    //                       FULL whnf (whnf_proj.rs:88-101).
    // [B9-beta]: one-binder-per-step beta (the landed pillar convention;
    // production consumes the lambda telescope via instantiate_rev —
    // identical WHNF fixpoint). The #20 trampoline stays direct recursion.
    // ════════════════════════════════════════════════════════════════════
    fn whnf_core_no_delta(&self, e: &Expr, cheap_proj: bool, ctx: &LocalContext) -> Expr {
        match &e.kind {
            ExprKind::App(f, a) => {
                // whnf.rs:363-430 — the Nat/native pre-checks fire when the
                // spine head is a visible Const (registry-empty stubs here),
                // then beta_or_iota_step (:536-631).
                let f0 = e.get_app_fn();
                if matches!(&f0.kind, ExprKind::Const(_, _)) {
                    if let Some(reduced) = self.reduce_nat(e) {
                        return self.whnf_core_no_delta(&reduced, cheap_proj, ctx);
                    }
                    if let Some(reduced) = self.reduce_native(e) {
                        return self.whnf_core_no_delta(&reduced, cheap_proj, ctx);
                    }
                }
                let f_whnf = self.whnf_core_no_delta(f, cheap_proj, ctx);
                match &f_whnf.kind {
                    ExprKind::Lam(_, _, body) => {
                        let reduced = body.instantiate(a);
                        self.whnf_core_no_delta(&reduced, cheap_proj, ctx)
                    }
                    _ => {
                        // Stuck head: rebuild, then iota/quot/nat/native
                        // (whnf.rs:598-629; B8/[C-nat]/[C-native] stubs).
                        let app = Expr::from_kind(ExprKind::App(Arc::new(f_whnf), a.clone()));
                        if let Some(reduced) = self.try_iota_reduction(&app) {
                            return self.whnf_core_no_delta(&reduced, cheap_proj, ctx);
                        }
                        if let Some(reduced) = self.try_quot_reduction(&app) {
                            return self.whnf_core_no_delta(&reduced, cheap_proj, ctx);
                        }
                        if let Some(reduced) = self.reduce_nat(&app) {
                            return self.whnf_core_no_delta(&reduced, cheap_proj, ctx);
                        }
                        if let Some(reduced) = self.reduce_native(&app) {
                            return self.whnf_core_no_delta(&reduced, cheap_proj, ctx);
                        }
                        app
                    }
                }
            }
            // whnf.rs:432-434 — Let zeta.
            ExprKind::Let(_, _, val, body, _) => {
                let reduced = body.instantiate(val);
                self.whnf_core_no_delta(&reduced, cheap_proj, ctx)
            }
            // whnf.rs:439-442 — Const is STUCK in the NoDelta modes. THE
            // no-delta fact: this is what defers unfolding to lazy delta.
            ExprKind::Const(_, _) => e.clone(),
            // whnf.rs:455-461 — FVar zeta runs in ALL modes.
            ExprKind::FVar(id) => {
                let val_opt: Option<Expr> = match ctx.get(*id) {
                    Some(d) => d.value.clone(),
                    None => None,
                };
                match val_opt {
                    Some(val) => self.whnf_core_no_delta(&val, cheap_proj, ctx),
                    None => e.clone(),
                }
            }
            // whnf.rs:462-464 -> whnf_proj.rs:73-146: cheap -> this same
            // no-delta whnf on the operand; full -> the FULL whnf_impl.
            ExprKind::Proj(struct_name, idx, expr) => {
                let operand = if cheap_proj {
                    self.whnf_core_no_delta(expr, cheap_proj, ctx)
                } else {
                    self.whnf_impl(expr, ctx)
                };
                let head = operand.get_app_fn();
                if let ExprKind::Const(ctor_name, _) = &head.kind {
                    if let Some(num_params) = self.get_constructor_num_params(ctor_name) {
                        let args = operand.get_app_args();
                        let field_idx = num_params as usize + *idx as usize;
                        if field_idx < args.len() {
                            // whnf_proj.rs:139-141 — continue reducing the
                            // extracted field in the same mode.
                            return self.whnf_core_no_delta(&args[field_idx], cheap_proj, ctx);
                        }
                    }
                }
                Expr::from_kind(ExprKind::Proj(struct_name.clone(), *idx, Arc::new(operand)))
            }
            // whnf.rs:465 — MData strips.
            ExprKind::MData(_, inner) => self.whnf_core_no_delta(inner, cheap_proj, ctx),
            _ => e.clone(),
        }
    }

    // ── Universe machinery (unchanged pillar): levels_eq == Level::is_def_eq
    // (tc/config.rs:353-360, override None in the kernel). ──
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

    // ════════════════════════════════════════════════════════════════════
    // R11 NEW — THE PRODUCTION DEF_EQ PHASE ORDERING (tc/def_eq/mod.rs).
    // is_def_eq/is_def_eq_impl (:176-197): cache/equiv layers [C-cache2],
    // stack_safe B4. def_eq_inner = is_def_eq_inner minus those layers:
    // the :218 `a == b` syntactic fast path (P0) then is_def_eq_core.
    // ════════════════════════════════════════════════════════════════════
    fn is_def_eq(&self, a: &Expr, b: &Expr, ctx: &mut LocalContext) -> bool { self.def_eq_inner(a, b, ctx) }
    fn def_eq_impl(&self, a: &Expr, b: &Expr, ctx: &mut LocalContext) -> bool { self.def_eq_inner(a, b, ctx) }
    fn def_eq_inner(&self, a: &Expr, b: &Expr, ctx: &mut LocalContext) -> bool {
        // mod.rs:218 — P0: `if a == b { return true; }` (Expr::PartialEq).
        if expr_syntactic_eq(a, b) {
            return true;
        }
        self.is_def_eq_core(a, b, ctx)
    }

    /// tc/def_eq/mod.rs:273-481 is_def_eq_core — the phase engine.
    /// Heartbeats (:281-288) B4; Bool.true reflection (:306-327) [C-refl];
    /// branch-sharing (:369-384) [C-cache2]; P7 (:461-465) [C-strlit];
    /// P8 (:467-473) [C-unitlike].
    fn is_def_eq_core(&self, a: &Expr, b: &Expr, ctx: &mut LocalContext) -> bool {
        // :300-304 — quick_is_def_eq at entry.
        match self.quick_is_def_eq(a, b, ctx) {
            Some(result) => return result,
            None => {}
        }

        // :329-333 — Phase 1: partial WHNF, beta/zeta/iota/proj only, NO
        // delta (Lean whnf_core(t, false, true)).
        let a_n = self.whnf_core_no_delta(a, true, ctx);
        let b_n = self.whnf_core_no_delta(b, true, ctx);

        // :341-345 — quick equality after partial reduction.
        if expr_syntactic_eq(&a_n, &b_n) {
            return true;
        }

        // :347-356 — re-consult quick ONLY when a side changed.
        if !expr_syntactic_eq(&a_n, a) || !expr_syntactic_eq(&b_n, b) {
            match self.quick_is_def_eq(&a_n, &b_n, ctx) {
                Some(result) => return result,
                None => {}
            }
        }

        // :358-367 — proof irrelevance (R9 transcription, production
        // position). ONLY Some(true) short-circuits.
        let proof_irrel = self.is_def_eq_proof_irrel(&a_n, &b_n, ctx);
        match proof_irrel {
            Some(true) => return true,
            _ => {}
        }

        // :386-403 — Phase 2: THE LAZY DELTA REDUCTION LOOP. Ok(result) is
        // the verdict; Err((t,s)) carries the FINAL partially-reduced pair.
        let (t_n, s_n) = match self.lazy_delta_reduction(&a_n, &b_n, ctx) {
            Ok(result) => return result,
            Err(final_exprs) => final_exprs,
        };

        // :408-421 — Phase 3: Const-head comparison after delta.
        match (&t_n.kind, &s_n.kind) {
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => {
                if name_eq(n1, n2) && self.level_vec_eq(ls1, ls2) {
                    return true;
                }
            }
            _ => {}
        }
        // :423-429 — Phase 3: FVar-id comparison.
        match (&t_n.kind, &s_n.kind) {
            (ExprKind::FVar(i), ExprKind::FVar(j)) => {
                if i == j {
                    return true;
                }
            }
            _ => {}
        }

        // :431-438 — Phase 4: projection comparison with lazy delta.
        // (Arc args deref-coerce — the landed [B9] convention.)
        let p4_pair: Option<(Arc<Expr>, Arc<Expr>, u32)> = match (&t_n.kind, &s_n.kind) {
            (ExprKind::Proj(_, i1, e1), ExprKind::Proj(_, i2, e2)) => {
                if *i1 == *i2 {
                    Some((e1.clone(), e2.clone(), *i1))
                } else {
                    None
                }
            }
            _ => None,
        };
        if let Some((e1, e2, i1)) = p4_pair {
            if self.lazy_delta_proj_reduction(&e1, &e2, i1, ctx) {
                return true;
            }
        }

        // :440-451 — Phase 5: second whnf_core with FULL projection.
        let t_full = self.whnf_core_no_delta(&t_n, false, ctx);
        let s_full = self.whnf_core_no_delta(&s_n, false, ctx);
        if !expr_syntactic_eq(&t_full, &t_n) || !expr_syntactic_eq(&s_full, &s_n) {
            return self.def_eq_impl(&t_full, &s_full, ctx);
        }

        // :453-459 — Phase 6: structural comparison on the reduced forms.
        if self.is_def_eq_structural(&t_n, &s_n, ctx) {
            return true;
        }

        // :461-473 — Phase 7 string-lit [C-strlit] / Phase 8 unit-like
        // [C-unitlike] elided.
        false
    }

    /// tc/def_eq/mod.rs:493-524 quick_is_def_eq — THE COMPLETE reachable-arm
    /// set: equiv consult (:495-497) [C-cache2]; (Lam,Lam)|(Pi,Pi) ->
    /// binding; (Sort,Sort) -> levels_eq; MData sym + the two #3134
    /// asymmetric strip arms; Squash STRUCTURALLY ABSENT (B5); (Lit,Lit)
    /// incl. the fast false; catch-all None. clean's ExprKind has NO MVar
    /// variant — no mvar arms exist to transcribe. NO FVar arm (Phase 3).
    fn quick_is_def_eq(&self, a: &Expr, b: &Expr, ctx: &mut LocalContext) -> Option<bool> {
        match (&a.kind, &b.kind) {
            (ExprKind::Lam(..), ExprKind::Lam(..)) | (ExprKind::Pi(..), ExprKind::Pi(..)) => {
                Some(self.is_def_eq_binding(a, b, ctx))
            }
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => Some(self.level_eq(l1, l2)),
            // MData is transparent for definitional equality.
            (ExprKind::MData(_, inner1), ExprKind::MData(_, inner2)) => {
                let i1: Arc<Expr> = inner1.clone();
                let i2: Arc<Expr> = inner2.clone();
                Some(self.def_eq_impl(&i1, &i2, ctx))
            }
            (ExprKind::MData(_, inner), _) => {
                let i: Arc<Expr> = inner.clone();
                Some(self.def_eq_impl(&i, b, ctx))
            }
            (_, ExprKind::MData(_, inner)) => {
                let i: Arc<Expr> = inner.clone();
                Some(self.def_eq_impl(a, &i, ctx))
            }
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => Some(l1 == l2),
            _ => None,
        }
    }

    // ════════════════════════════════════════════════════════════════════
    // R10 — IS_DEF_EQ_BINDING (tc/def_eq/binding.rs:12-64, the whole file)
    // — UNCHANGED transcription; its domain/body def_eq_impl recursions now
    // enter the R11 phase engine. [B9-disc]/[C-refcell] as R10.
    // ════════════════════════════════════════════════════════════════════
    fn is_def_eq_binding(&self, a: &Expr, b: &Expr, ctx: &mut LocalContext) -> bool {
        let save_len = ctx.len();
        let binder_is_lam = matches!(&a.kind, ExprKind::Lam(_, _, _));
        let mut a = a.clone();
        let mut b = b.clone();

        loop {
            let (ty1, body1): (Arc<Expr>, Arc<Expr>) = match &a.kind {
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    (ty.clone(), body.clone())
                }
                _ => return false,
            };
            let (bi2, ty2, body2): (BinderData, Arc<Expr>, Arc<Expr>) = match &b.kind {
                ExprKind::Lam(bi, ty, body) | ExprKind::Pi(bi, ty, body) => {
                    (*bi, ty.clone(), body.clone())
                }
                _ => return false,
            };

            if !expr_syntactic_eq(&ty1, &ty2) && !self.def_eq_impl(&ty1, &ty2, ctx) {
                ctx.truncate_to(save_len);
                return false;
            }

            if !body1.has_loose_bvars() && !body2.has_loose_bvars() {
                let result = self.def_eq_impl(&body1, &body2, ctx);
                ctx.truncate_to(save_len);
                return result;
            }

            let local_id = ctx.push(name_anon(), ty2.as_ref().clone(), bi2);
            let a_next = self.open_bvar(&body1, local_id);
            let b_next = self.open_bvar(&body2, local_id);
            let a_same = if binder_is_lam {
                matches!(&a_next.kind, ExprKind::Lam(_, _, _))
            } else {
                matches!(&a_next.kind, ExprKind::Pi(_, _, _))
            };
            let b_same = if binder_is_lam {
                matches!(&b_next.kind, ExprKind::Lam(_, _, _))
            } else {
                matches!(&b_next.kind, ExprKind::Pi(_, _, _))
            };
            if a_same && b_same {
                a = a_next;
                b = b_next;
                continue;
            }

            let result = self.def_eq_impl(&a_next, &b_next, ctx);
            ctx.truncate_to(save_len);
            return result;
        }
    }

    // ════════════════════════════════════════════════════════════════════
    // R11 NEW — THE LAZY DELTA REDUCTION LOOP (tc/def_eq/delta.rs:57-168),
    // VERBATIM: the 10_000-iteration termination cap, the four loop-top
    // hooks in production order, the step dispatch, the status map.
    // clippy::result_large_err — the production keeps (Expr,Expr) unboxed.
    // ════════════════════════════════════════════════════════════════════
    fn lazy_delta_reduction(
        &self,
        a: &Expr,
        b: &Expr,
        ctx: &mut LocalContext,
    ) -> Result<bool, (Expr, Expr)> {
        const MAX_LAZY_DELTA_ITERATIONS: u32 = 10_000;

        let mut t = a.clone();
        let mut s = b.clone();

        let mut iterations = 0u32;

        loop {
            iterations += 1;
            if iterations > MAX_LAZY_DELTA_ITERATIONS {
                // Conservative: treat as not definitionally equal (#1773).
                return Ok(false);
            }

            // 1. Structural Nat successor peeling (delta.rs:88-90).
            if let Some(result) = self.is_def_eq_offset(&t, &s, ctx) {
                return Ok(result);
            }

            // 2. Closed Nat arithmetic (delta.rs:94-101) — fvar guard
            // VERBATIM, reducer body [C-nat].
            if (!t.has_fvar_quick() && !s.has_fvar_quick()) || self.eager_reduce() {
                if let Some(t_v) = self.reduce_nat(&t) {
                    return Ok(self.def_eq_impl(&t_v, &s, ctx));
                }
                if let Some(s_v) = self.reduce_nat(&s) {
                    return Ok(self.def_eq_impl(&t, &s_v, ctx));
                }
            }

            // 3. Native reduction hook (delta.rs:107-112) — NO fvar guard;
            // registry-empty stub [C-native].
            if let Some(t_v) = self.reduce_native(&t) {
                return Ok(self.def_eq_impl(&t_v, &s, ctx));
            }
            if let Some(s_v) = self.reduce_native(&s) {
                return Ok(self.def_eq_impl(&t, &s_v, ctx));
            }

            // 4. Monadic reduction hook (delta.rs:125-134) — the
            // `reduced != side` progress gate VERBATIM; body [C-monad].
            if let Some(t_v) = self.try_monad_reduce(&t) {
                if !expr_syntactic_eq(&t_v, &t) {
                    return Ok(self.def_eq_impl(&t_v, &s, ctx));
                }
            }
            if let Some(s_v) = self.try_monad_reduce(&s) {
                if !expr_syntactic_eq(&s_v, &s) {
                    return Ok(self.def_eq_impl(&t, &s_v, ctx));
                }
            }

            // One delta step (delta.rs:143-166 status map).
            match self.lazy_delta_reduction_step(&mut t, &mut s, ctx) {
                ReductionStatus::Continue => {}
                ReductionStatus::DefEqual => return Ok(true),
                ReductionStatus::DefUnknown => return Err((t, s)),
                ReductionStatus::DefDiff => return Ok(false),
            }
        }
    }

    /// delta.rs:170-200 — the step dispatch on the two delta-const consults
    /// + the shared finish on Continue.
    fn lazy_delta_reduction_step(
        &self,
        t: &mut Expr,
        s: &mut Expr,
        ctx: &mut LocalContext,
    ) -> ReductionStatus {
        let t_delta = self.get_delta_const(t);
        let s_delta = self.get_delta_const(s);
        let status = match (t_delta, s_delta) {
            (Some(t_const), Some(s_const)) => self.lazy_delta_step_both(t, s, t_const, s_const, ctx),
            (Some((t_name, t_levels, _)), None) => {
                self.lazy_delta_step_left_only(t, s, t_name, t_levels, ctx)
            }
            (None, Some((s_name, s_levels, _))) => {
                self.lazy_delta_step_right_only(t, s, s_name, s_levels, ctx)
            }
            (None, None) => self.lazy_delta_step_no_consts(t, s),
        };
        if matches!(status, ReductionStatus::Continue) {
            return self.finish_lazy_delta_reduction_step(t, s, ctx);
        }
        status
    }

    /// delta.rs:202-234 — BOTH sides delta-reducible: hint-ordered
    /// unfolding. compare < 0 => unfold t first (fallback s); > 0 => unfold
    /// s first (fallback t); == 0 => the equal-hint arm. [B9-ord].
    fn lazy_delta_step_both(
        &self,
        t: &mut Expr,
        s: &mut Expr,
        t_const: (Name, LevelVec, Reducibility),
        s_const: (Name, LevelVec, Reducibility),
        ctx: &mut LocalContext,
    ) -> ReductionStatus {
        let (t_name, t_levels, t_red) = t_const;
        let (s_name, s_levels, s_red) = s_const;
        let ord = t_red.compare(&s_red);
        if ord < 0 {
            if self.try_unfold_const_in_place(t, &t_name, &t_levels, ctx)
                || self.try_unfold_const_in_place(s, &s_name, &s_levels, ctx)
            {
                ReductionStatus::Continue
            } else {
                ReductionStatus::DefUnknown
            }
        } else if ord > 0 {
            if self.try_unfold_const_in_place(s, &s_name, &s_levels, ctx)
                || self.try_unfold_const_in_place(t, &t_name, &t_levels, ctx)
            {
                ReductionStatus::Continue
            } else {
                ReductionStatus::DefUnknown
            }
        } else {
            self.lazy_delta_step_equal(t, s, (t_name, t_levels, t_red), (s_name, s_levels), ctx)
        }
    }

    /// delta.rs:236-262 — equal hints: the same-name Regular args-only
    /// shortcut (Lean type_checker.cpp:924-930), then unfold BOTH.
    fn lazy_delta_step_equal(
        &self,
        t: &mut Expr,
        s: &mut Expr,
        t_const: (Name, LevelVec, Reducibility),
        s_const: (Name, LevelVec),
        ctx: &mut LocalContext,
    ) -> ReductionStatus {
        let (t_name, t_levels, t_red) = t_const;
        let (s_name, s_levels) = s_const;
        if name_eq(&t_name, &s_name) && matches!(t_red, Reducibility::Regular(_)) {
            if !self.args_failed_before(t, s) {
                if self.is_def_eq_args_only(t, s, ctx) {
                    return ReductionStatus::DefEqual;
                }
                self.cache_args_failure(t, s);
            }
        }
        let t_changed = self.try_unfold_const_in_place(t, &t_name, &t_levels, ctx);
        let s_changed = self.try_unfold_const_in_place(s, &s_name, &s_levels, ctx);
        if t_changed || s_changed {
            ReductionStatus::Continue
        } else {
            ReductionStatus::DefUnknown
        }
    }

    /// delta.rs:264-280 — left-only: FIRST the rhs proj-app reconvergence,
    /// THEN unfold t.
    fn lazy_delta_step_left_only(
        &self,
        t: &mut Expr,
        s: &mut Expr,
        t_name: Name,
        t_levels: LevelVec,
        ctx: &mut LocalContext,
    ) -> ReductionStatus {
        if let Some(s_new) = self.try_unfold_proj_app(s, ctx) {
            *s = s_new;
            return ReductionStatus::Continue;
        }
        if self.try_unfold_const_in_place(t, &t_name, &t_levels, ctx) {
            ReductionStatus::Continue
        } else {
            ReductionStatus::DefUnknown
        }
    }

    /// delta.rs:282-298 — right-only, symmetric.
    fn lazy_delta_step_right_only(
        &self,
        t: &mut Expr,
        s: &mut Expr,
        s_name: Name,
        s_levels: LevelVec,
        ctx: &mut LocalContext,
    ) -> ReductionStatus {
        if let Some(t_new) = self.try_unfold_proj_app(t, ctx) {
            *t = t_new;
            return ReductionStatus::Continue;
        }
        if self.try_unfold_const_in_place(s, &s_name, &s_levels, ctx) {
            ReductionStatus::Continue
        } else {
            ReductionStatus::DefUnknown
        }
    }

    /// delta.rs:300-308 — neither side delta-reducible: DefUnknown
    /// IMMEDIATELY, NO proj attempt (#3134).
    fn lazy_delta_step_no_consts(&self, _t: &mut Expr, _s: &mut Expr) -> ReductionStatus {
        ReductionStatus::DefUnknown
    }

    /// delta.rs:321-331 — after each unfold: syntactic equality, then quick
    /// — NOT proof irrelevance (#3229: irrel runs once BEFORE the loop).
    fn finish_lazy_delta_reduction_step(
        &self,
        t: &Expr,
        s: &Expr,
        ctx: &mut LocalContext,
    ) -> ReductionStatus {
        if expr_syntactic_eq(t, s) {
            return ReductionStatus::DefEqual;
        }
        match self.quick_is_def_eq(t, s, ctx) {
            Some(true) => return ReductionStatus::DefEqual,
            Some(false) => return ReductionStatus::DefDiff,
            None => {}
        }
        ReductionStatus::Continue
    }

    /// delta.rs:346-384 — lazy delta for projection comparison (P4): the
    /// step loop WITHOUT the Nat/native hooks (production separation), the
    /// same 10k cap, the reduce_proj_core extraction fallback, then the
    /// plain recursive def_eq on the delta-reduced inners.
    fn lazy_delta_proj_reduction(
        &self,
        t_c: &Expr,
        s_c: &Expr,
        idx: u32,
        ctx: &mut LocalContext,
    ) -> bool {
        const MAX_PROJ_DELTA_ITERATIONS: u32 = 10_000;

        let mut t = t_c.clone();
        let mut s = s_c.clone();
        let mut iterations = 0u32;

        loop {
            iterations += 1;
            if iterations > MAX_PROJ_DELTA_ITERATIONS {
                return false; // Conservative: not def-eq
            }

            match self.lazy_delta_reduction_step(&mut t, &mut s, ctx) {
                ReductionStatus::Continue => {}
                ReductionStatus::DefEqual => return true,
                ReductionStatus::DefUnknown | ReductionStatus::DefDiff => {
                    if let Some(t_field) = self.reduce_proj_core(&t, idx) {
                        if let Some(s_field) = self.reduce_proj_core(&s, idx) {
                            return self.def_eq_impl(&t_field, &s_field, ctx);
                        }
                    }
                    return self.def_eq_impl(&t, &s, ctx);
                }
            }
        }
    }

    /// delta.rs:393-396 / :406-411 — the args-failure cache, [C-cache2]:
    /// always-miss / no-op at the production call sites (pure memoization
    /// of a deterministic recheck; production semantics without the cache
    /// = always run the args comparison).
    fn args_failed_before(&self, _t: &Expr, _s: &Expr) -> bool {
        false
    }
    fn cache_args_failure(&self, _t: &Expr, _s: &Expr) {}

    // ════════════════════════════════════════════════════════════════════
    // R11 NEW — the delta helpers (tc/def_eq/delta_helpers.rs).
    // ════════════════════════════════════════════════════════════════════

    /// delta_helpers.rs:113-156 get_delta_const — VERBATIM: head Const, env
    /// hit, `value.is_some() && kind != Opaque && reducibility != Opaque &&
    /// levels.len() == level_params.len()` (#1277). Theorems carry
    /// reducibility Opaque (#3305) and so NEVER participate here — while
    /// whnf CAN still unfold them (kind Theorem passes unfold_definition).
    fn get_delta_const(&self, e: &Expr) -> Option<(Name, LevelVec, Reducibility)> {
        let head = e.get_app_fn();
        if let ExprKind::Const(name, levels) = &head.kind {
            if let Some(info) = self.find_entry(name) {
                // [B9-matches] the two !=-enum-constant tests -> !matches!
                // (identical: Opaque carries no payload in either enum).
                if info.value.is_some()
                    && !matches!(info.kind, ConstantKind::Opaque)
                    && !matches!(info.reducibility, Reducibility::Opaque)
                    && levels.len() == info.level_params.len()
                {
                    return Some((name.clone(), levels.clone(), info.reducibility));
                }
            }
        }
        None
    }

    /// delta_helpers.rs:55-79 try_unfold_const_in_place — VERBATIM: the
    /// KERNEL unfold (no transparency — #3210; the production `_mode`
    /// parameter is unread and dropped here), then
    /// whnf_core_no_delta(replace_head_const(..), CHEAP) written in place.
    fn try_unfold_const_in_place(
        &self,
        expr: &mut Expr,
        name: &Name,
        levels: &[Level],
        ctx: &LocalContext,
    ) -> bool {
        let value = match self.unfold_definition_model(name, levels) {
            Some(v) => v,
            None => return false,
        };
        let replaced = self.replace_head_const(expr, &value);
        let reduced = self.whnf_core_no_delta(&replaced, true, ctx);
        *expr = reduced;
        true
    }

    /// delta_helpers.rs:158-172 replace_head_const — flat spine rebuild.
    fn replace_head_const(&self, e: &Expr, new_head: &Expr) -> Expr {
        if !matches!(&e.kind, ExprKind::App(_, _)) {
            return new_head.clone();
        }
        let args = e.get_app_args();
        let mut result = new_head.clone();
        let mut i: usize = 0;
        while i < args.len() {
            result = Expr::app(result, args[i].clone());
            i += 1;
        }
        result
    }

    /// delta_helpers.rs:81-111 is_def_eq_args_only — VERBATIM: both heads
    /// Const with levels_eq'd level vectors, then the arg spines compared
    /// pairwise through the full def_eq (zip-loop → index loop [B9];
    /// length run-out mismatch => false, as the production (None,Some) /
    /// (Some,None) arms).
    fn is_def_eq_args_only(&self, a: &Expr, b: &Expr, ctx: &mut LocalContext) -> bool {
        let a_fn = a.get_app_fn();
        let b_fn = b.get_app_fn();
        match (&a_fn.kind, &b_fn.kind) {
            (ExprKind::Const(_, ls1), ExprKind::Const(_, ls2)) => {
                if !self.level_vec_eq(ls1, ls2) {
                    return false;
                }
            }
            _ => return false,
        }

        let a_args = a.get_app_args();
        let b_args = b.get_app_args();
        if a_args.len() != b_args.len() {
            return false;
        }
        let mut i: usize = 0;
        while i < a_args.len() {
            if !self.def_eq_impl(&a_args[i], &b_args[i], ctx) {
                return false;
            }
            i += 1;
        }
        true
    }

    /// delta_helpers.rs:174-190 reduce_proj_core — VERBATIM minus the
    /// String-literal expansion arm ([C-strlit]: Literal::Str is a u32 tag
    /// model; no String projections exist in the scenario space).
    fn reduce_proj_core(&self, c: &Expr, idx: u32) -> Option<Expr> {
        let head = c.get_app_fn();
        let ctor_name = match &head.kind {
            ExprKind::Const(n, _) => n.clone(),
            _ => return None,
        };
        let num_params = match self.get_constructor_num_params(&ctor_name) {
            Some(n) => n,
            None => return None,
        };
        let args = c.get_app_args();
        let field_idx = (num_params as usize).saturating_add(idx as usize);
        if field_idx < args.len() {
            Some(args[field_idx].clone())
        } else {
            None
        }
    }

    /// delta_helpers.rs:221-230 try_unfold_proj_app — VERBATIM: a
    /// proj-headed side gets whnf_core with NO head delta but FULL
    /// projection reduction (cheap_proj = false) — the reconvergence step
    /// of the asymmetric lazy-delta arms.
    fn try_unfold_proj_app(&self, e: &Expr, ctx: &LocalContext) -> Option<Expr> {
        let head = e.get_app_fn();
        if matches!(&head.kind, ExprKind::Proj(_, _, _)) {
            let e_new = self.whnf_core_no_delta(e, false, ctx);
            if !expr_syntactic_eq(&e_new, e) {
                return Some(e_new);
            }
        }
        None
    }

    // ════════════════════════════════════════════════════════════════════
    // R11 NEW — PHASE 6 (tc/def_eq/structural.rs:10-71 is_def_eq_structural)
    // + the spine compare (:97-142, branch-sharing consult [C-cache2]) +
    // the production eta (eta.rs:27-68). struct-eta => false [C-structeta]
    // (needs the structure-like registry; verified separately in the eta
    // rungs). NO Let/MData arms — production parity (P1 whnf_core zeta/
    // strips them; quick handles MData at every recursion level).
    // ════════════════════════════════════════════════════════════════════
    fn is_def_eq_structural(&self, a_whnf: &Expr, b_whnf: &Expr, ctx: &mut LocalContext) -> bool {
        match (&a_whnf.kind, &b_whnf.kind) {
            (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
            (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => self.level_eq(l1, l2),
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => {
                name_eq(n1, n2) && self.level_vec_eq(ls1, ls2)
            }
            (ExprKind::App(_, _), ExprKind::App(_, _)) => {
                if self.is_def_eq_app_spine(a_whnf, b_whnf, ctx) {
                    return true;
                }
                self.try_structure_eta_expansion(a_whnf, b_whnf)
            }
            (ExprKind::Lam(..), ExprKind::Lam(..)) | (ExprKind::Pi(..), ExprKind::Pi(..)) => {
                self.is_def_eq_binding(a_whnf, b_whnf, ctx)
            }
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            (ExprKind::Proj(s1, i1, e1), ExprKind::Proj(s2, i2, e2)) => {
                if name_eq(s1, s2) && *i1 == *i2 {
                    let e1c: Arc<Expr> = e1.clone();
                    let e2c: Arc<Expr> = e2.clone();
                    self.def_eq_impl(&e1c, &e2c, ctx)
                } else {
                    false
                }
            }
            (ExprKind::Lam(_, _, _), _) => self.try_eta_expansion_impl(a_whnf, b_whnf, ctx),
            (_, ExprKind::Lam(_, _, _)) => self.try_eta_expansion_impl(b_whnf, a_whnf, ctx),
            _ => self.try_structure_eta_expansion(a_whnf, b_whnf),
        }
    }

    /// structural.rs:97-142 is_def_eq_app_spine — flatten both spines,
    /// arity gate, heads then args left-to-right through the full def_eq.
    /// The branch-sharing-cache consult (:121-132) is [C-cache2]-elided:
    /// the plain is_def_eq path (:134-138) is the semantics either way.
    fn is_def_eq_app_spine(&self, a: &Expr, b: &Expr, ctx: &mut LocalContext) -> bool {
        let a_args = a.get_app_args();
        let b_args = b.get_app_args();
        if a_args.len() != b_args.len() {
            return false;
        }
        let a_head = a.get_app_fn();
        let b_head = b.get_app_fn();
        if !self.def_eq_impl(&a_head, &b_head, ctx) {
            return false;
        }
        let mut i: usize = 0;
        while i < a_args.len() {
            if !self.def_eq_impl(&a_args[i], &b_args[i], ctx) {
                return false;
            }
            i += 1;
        }
        true
    }

    /// [C-structeta] structural.rs:158-219 — needs get_constructor +
    /// is_structure_like (the structure registry, absent from the modeled
    /// env); returns false exactly as production does when the head is not
    /// a registered structure constructor. Verified separately in the
    /// struct-eta rungs (e2e_eta_struct_ext.rs).
    fn try_structure_eta_expansion(&self, _a: &Expr, _b: &Expr) -> bool {
        false
    }

    /// eta.rs:27-68 try_eta_expansion_impl — THE PRODUCTION ETA: type the
    /// non-Lam side (quick-or-full — the same proof-irrel helper pair),
    /// whnf it; a Pi wraps `other` in a matching Lam over the Pi DOMAIN
    /// applied to BVar(0), then re-enters the full def_eq — which routes
    /// (Lam,Lam) through BINDING (opening into the context; the production
    /// comment: the old raw-body compare broke proof irrelevance under the
    /// binder). The production `_bd/_lam_ty/_lam_body` params are unread
    /// and dropped [B9].
    fn try_eta_expansion_impl(&self, lam_expr: &Expr, other: &Expr, ctx: &mut LocalContext) -> bool {
        let other_type = match self.infer_type_quick_or_full(other, ctx) {
            Some(t) => t,
            None => return false,
        };
        let other_type_whnf = self.whnf_impl(&other_type, ctx);
        match &other_type_whnf.kind {
            ExprKind::Pi(bi, pi_domain, _) => {
                let new_s = Expr::lam(
                    *bi,
                    pi_domain.as_ref().clone(),
                    Expr::app(other.lift_from(0, 1), Expr::bvar(0)),
                );
                self.def_eq_impl(lam_expr, &new_s, ctx)
            }
            _ => false,
        }
    }

    // ════════════════════════════════════════════════════════════════════
    // NOT A TRANSCRIPTION — the p0 probe pair. `_probe` is the
    // lazy_delta_reduction transcription text with the production
    // `iterations` counter SURFACED through an out-param (the loop-top
    // hooks omitted: the probe scenario space is Const-vs-Const with no
    // fvars/Nat/monad heads, where every hook is None — asserted by the
    // agreement with the real lazy_delta_reduction verdict). `_swapped`
    // additionally INVERTS the hint comparison: the <0 and >0 arm BODIES
    // are exchanged — the armed order-falsification control. The verdict
    // must AGREE (confluence) while the surfaced iteration count DIFFERS —
    // the hint-order observable, native==JIT on both.
    // ════════════════════════════════════════════════════════════════════
    fn lazy_delta_reduction_probe(
        &self,
        a: &Expr,
        b: &Expr,
        ctx: &mut LocalContext,
        out_iterations: &mut u64,
    ) -> Result<bool, (Expr, Expr)> {
        const MAX_LAZY_DELTA_ITERATIONS: u32 = 10_000;
        let mut t = a.clone();
        let mut s = b.clone();
        let mut iterations = 0u32;
        loop {
            iterations += 1;
            *out_iterations = iterations as u64;
            if iterations > MAX_LAZY_DELTA_ITERATIONS {
                return Ok(false);
            }
            match self.lazy_delta_reduction_step(&mut t, &mut s, ctx) {
                ReductionStatus::Continue => {}
                ReductionStatus::DefEqual => return Ok(true),
                ReductionStatus::DefUnknown => return Err((t, s)),
                ReductionStatus::DefDiff => return Ok(false),
            }
        }
    }

    fn lazy_delta_reduction_swapped(
        &self,
        a: &Expr,
        b: &Expr,
        ctx: &mut LocalContext,
        out_iterations: &mut u64,
    ) -> Result<bool, (Expr, Expr)> {
        const MAX_LAZY_DELTA_ITERATIONS: u32 = 10_000;
        let mut t = a.clone();
        let mut s = b.clone();
        let mut iterations = 0u32;
        loop {
            iterations += 1;
            *out_iterations = iterations as u64;
            if iterations > MAX_LAZY_DELTA_ITERATIONS {
                return Ok(false);
            }
            match self.lazy_delta_step_swapped(&mut t, &mut s, ctx) {
                ReductionStatus::Continue => {}
                ReductionStatus::DefEqual => return Ok(true),
                ReductionStatus::DefUnknown => return Err((t, s)),
                ReductionStatus::DefDiff => return Ok(false),
            }
        }
    }

    /// THE ARMED DIFFERENCE: compare < 0 unfolds the OTHER side first,
    /// > 0 unfolds SELF first — the production arms exchanged.
    fn lazy_delta_step_swapped(
        &self,
        t: &mut Expr,
        s: &mut Expr,
        ctx: &mut LocalContext,
    ) -> ReductionStatus {
        let t_delta = self.get_delta_const(t);
        let s_delta = self.get_delta_const(s);
        let status = match (t_delta, s_delta) {
            (Some(t_const), Some(s_const)) => {
                let (t_name, t_levels, t_red) = t_const;
                let (s_name, s_levels, s_red) = s_const;
                let ord = t_red.compare(&s_red);
                if ord < 0 {
                    // SWAPPED: unfold s first.
                    if self.try_unfold_const_in_place(s, &s_name, &s_levels, ctx)
                        || self.try_unfold_const_in_place(t, &t_name, &t_levels, ctx)
                    {
                        ReductionStatus::Continue
                    } else {
                        ReductionStatus::DefUnknown
                    }
                } else if ord > 0 {
                    // SWAPPED: unfold t first.
                    if self.try_unfold_const_in_place(t, &t_name, &t_levels, ctx)
                        || self.try_unfold_const_in_place(s, &s_name, &s_levels, ctx)
                    {
                        ReductionStatus::Continue
                    } else {
                        ReductionStatus::DefUnknown
                    }
                } else {
                    self.lazy_delta_step_equal(t, s, (t_name, t_levels, t_red), (s_name, s_levels), ctx)
                }
            }
            (Some((t_name, t_levels, _)), None) => {
                self.lazy_delta_step_left_only(t, s, t_name, t_levels, ctx)
            }
            (None, Some((s_name, s_levels, _))) => {
                self.lazy_delta_step_right_only(t, s, s_name, s_levels, ctx)
            }
            (None, None) => self.lazy_delta_step_no_consts(t, s),
        };
        if matches!(status, ReductionStatus::Continue) {
            return self.finish_lazy_delta_reduction_step(t, s, ctx);
        }
        status
    }

    // ── structural_eq — the R6-landed pillar comparator, retained for the
    // R10-CONFIG control's fast path (the aware chain no longer consults
    // it: production P0 is the syntactic Expr::PartialEq). level_eq inside
    // is the full Level::is_def_eq, names via production name_eq. ──
    fn structural_eq(&self, a: &Expr, b: &Expr) -> bool {
        match (&a.kind, &b.kind) {
            (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
            (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => self.level_eq(l1, l2),
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => name_eq(n1, n2) && self.level_vec_eq(ls1, ls2),
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => self.structural_eq(f1, f2) && self.structural_eq(a1, a2),
            (ExprKind::Lam(_b1, ty1, b1), ExprKind::Lam(_b2, ty2, b2))
            | (ExprKind::Pi(_b1, ty1, b1), ExprKind::Pi(_b2, ty2, b2)) => self.structural_eq(ty1, ty2) && self.structural_eq(b1, b2),
            (ExprKind::Let(_, ty1, v1, b1, _), ExprKind::Let(_, ty2, v2, b2, _)) => self.structural_eq(ty1, ty2) && self.structural_eq(v1, v2) && self.structural_eq(b1, b2),
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => name_eq(n1, n2) && i1 == i2 && self.structural_eq(e1, e2),
            (ExprKind::MData(_, in1), ExprKind::MData(_, in2)) => self.structural_eq(in1, in2),
            _ => false,
        }
    }
    // ════════════════════════════════════════════════════════════════════
    // R9 NEW — THE PROOF-IRRELEVANCE FAMILY (tc/def_eq/proof_irrel.rs),
    // transcribed VERBATIM on the B5 core. The CleanMode Cubical/Directed
    // early-out (:36-38) is structurally absent — mode is fixed Classical
    // (B5); the quick_infer_cache consult (:126-141) is elided ([C-cache2]);
    // stack_safe and the escaping-BVar debug_assert are B4 pass-throughs.
    // ════════════════════════════════════════════════════════════════════

    /// proof_irrel.rs:16-53 — is_def_eq_proof_irrel. `?`-on-Option and
    /// `!(..)?` → match [B9]; `is_def_eq_impl(&ty_a, &ty_b)` is the pillar
    /// def_eq on the SAME context.
    fn is_def_eq_proof_irrel(&self, a: &Expr, b: &Expr, ctx: &mut LocalContext) -> Option<bool> {
        let ty_a = match self.infer_type_quick_or_full(a, ctx) {
            Some(t) => t,
            None => return None,
        };
        // Fast path (:39-47): if ty_a is quickly known to NOT be in Prop,
        // skip the expensive type_is_proof_irrelevant check entirely.
        if self.type_is_quickly_not_in_prop(&ty_a) {
            return None;
        }
        match self.type_is_proof_irrelevant(&ty_a, ctx) {
            Some(true) => {}
            Some(false) => return None,
            None => return None,
        }
        let ty_b = match self.infer_type_quick_or_full(b, ctx) {
            Some(t) => t,
            None => return None,
        };
        Some(self.def_eq_impl(&ty_a, &ty_b, ctx))
    }

    /// proof_irrel.rs:65-73 — quick inference, else the FULL infer-only
    /// fallback ([C-inferonly]); `.ok()` → match [B9].
    fn infer_type_quick_or_full(&self, e: &Expr, ctx: &mut LocalContext) -> Option<Expr> {
        match self.try_infer_type_quick(e, ctx) {
            Some(ty) => Some(ty),
            None => match self.infer_type_infer_only_core(e, ctx) {
                Ok(t) => Some(t),
                Err(_) => None,
            },
        }
    }

    /// proof_irrel.rs:75-88 — type_is_proof_irrelevant: whnf the type; a
    /// Sort is QUICK-REJECTED (its type is Sort(succ) — never Prop); else
    /// the type-of-type must whnf to Sort 0. The SProp disjunct (:86) is
    /// structurally absent (B5).
    fn type_is_proof_irrelevant(&self, ty: &Expr, ctx: &mut LocalContext) -> Option<bool> {
        let ty_whnf = self.whnf_impl(ty, ctx);
        if matches!(&ty_whnf.kind, ExprKind::Sort(_)) {
            return Some(false);
        }
        let ty_of_ty = match self.infer_type_quick_or_full(&ty_whnf, ctx) {
            Some(t) => t,
            None => return None,
        };
        let ty_of_ty_whnf = self.whnf_impl(&ty_of_ty, ctx);
        match &ty_of_ty_whnf.kind {
            ExprKind::Sort(l) => Some(l.is_zero()),
            _ => Some(false),
        }
    }

    /// proof_irrel.rs:105-115 — the pure pre-filter. The Const arm's
    /// `*name == *NAME_NAT || *name == *NAME_STRING` is the production
    /// Name::eq against the interned Nat/String constants — name_eq against
    /// the same per-call-built names here (B11). Match guard → nested if
    /// [B9].
    fn type_is_quickly_not_in_prop(&self, ty: &Expr) -> bool {
        match &ty.kind {
            // Sort(l) : Sort(succ(l)) — always in a Sort above Prop.
            ExprKind::Sort(_) => true,
            // Literal types: Nat and String are both in Type 0, not Prop.
            ExprKind::Const(name, levels) => {
                if levels.len() == 0 {
                    name_eq(name, &nat_type_name()) || name_eq(name, &str_type_name())
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    /// proof_irrel.rs:117-143 wrapper (cache elided [C-cache2], stack_safe +
    /// debug_assert B4) over :145-187 try_infer_type_quick_inner — the
    /// quick arms VERBATIM on the B5 core. Read-only context.
    fn try_infer_type_quick(&self, e: &Expr, ctx: &LocalContext) -> Option<Expr> {
        self.try_infer_type_quick_inner(e, ctx)
    }
    fn try_infer_type_quick_inner(&self, e: &Expr, ctx: &LocalContext) -> Option<Expr> {
        match &e.kind {
            // :147 — THE NAMED LINE: the FVar TYPE comes from the context.
            // `self.ctx.borrow().get(*id).map(|d| d.type_.clone())` — map →
            // match [B9] [C-refcell].
            ExprKind::FVar(id) => match ctx.get(*id) {
                Some(d) => Some(d.type_.clone()),
                None => None,
            },
            // :148 — production `self.env.instantiate_type(name, levels)`;
            // B1 env model (a const's type = inferred type of its value),
            // B10 (no level instantiation on the modeled env).
            ExprKind::Const(name, _levels) => self.const_type(name),
            // :149.
            ExprKind::Sort(l) => Some(Expr::from_kind(ExprKind::Sort(Level::succ(l.clone())))),
            // :150-157 — quick fn type, whnf, Pi-result instantiate.
            ExprKind::App(f, a) => {
                let f_type = match self.try_infer_type_quick(f, ctx) {
                    Some(t) => t,
                    None => return None,
                };
                let f_type_whnf = self.whnf_impl(&f_type, ctx);
                match &f_type_whnf.kind {
                    ExprKind::Pi(_, _, result_type) => Some(result_type.instantiate(a)),
                    _ => None,
                }
            }
            // :158-161 — quick body type wrapped in Pi (NO opening: quick
            // inference bails to None on any loose BVar via the catch-all).
            ExprKind::Lam(bi, ty, body) => {
                let body_type = match self.try_infer_type_quick(body, ctx) {
                    Some(t) => t,
                    None => return None,
                };
                Some(Expr::pi(*bi, ty.as_ref().clone(), body_type))
            }
            // :162-165 — B11 names.
            ExprKind::Lit(lit) => Some(match lit {
                Literal::Nat(_) => Expr::cnst(nat_type_name()),
                Literal::Str(_) => Expr::cnst(str_type_name()),
            }),
            // :166.
            ExprKind::MData(_, inner) => self.try_infer_type_quick(inner, ctx),
            // :181-184 Proj — [C-proj-quick]: production consults
            // infer_proj_type_from_quick; modeled None (no live Proj on the
            // quick path this round). :167-180 Squash absent (B5).
            ExprKind::Proj(_, _, _) => None,
            // :185 — the production catch-all (BVar, Pi, Let, ...).
            _ => None,
        }
    }

    /// tc/infer.rs:193-198 infer_type_infer_only — the proof-irrel FULL
    /// fallback. Production saves/sets/restores the `infer_only` Cell and
    /// calls the SHARED :322-648 arms; transcribed as a DEDICATED fn whose
    /// arms are that text with the `if !self.infer_only.get()` blocks
    /// STATICALLY SKIPPED ([C-inferonly], [B9]): the Sort check_level
    /// (:340), Const level/safety checks (:369), App ARGUMENT CHECK (:423),
    /// Lam DOMAIN-SORT gate (:486), and Let TYPE/VALUE gates (:556) are
    /// OFF. The open→infer→close binder discipline is IDENTICAL to the
    /// check-mode core (SAME shared context — the counter advances).
    fn infer_type_infer_only_core(
        &self,
        e: &Expr,
        ctx: &mut LocalContext,
    ) -> Result<Expr, TypeError> {
        match &e.kind {
            ExprKind::BVar(idx) => Err(TypeError::UnboundVariable(*idx)),
            ExprKind::FVar(id) => match ctx.get(*id) {
                Some(d) => Ok(d.type_.clone()),
                None => Err(TypeError::UnknownFVar(*id)),
            },
            ExprKind::Sort(l) => Ok(Expr::sort(Level::succ(l.clone()))),
            ExprKind::Const(name, _levels) => match self.const_type(name) {
                Some(ty) => Ok(ty),
                None => Err(TypeError::UnknownConst(name.clone())),
            },
            // :399-478 with the :423 infer_only=false block SKIPPED: the
            // argument is NOT inferred and NOT def_eq-checked in infer-only
            // mode (Lean 4 infer_app parity).
            ExprKind::App(f, a) => {
                let f_type = self.infer_type_infer_only_core(f, ctx)?;
                let f_type_whnf = self.whnf_impl(&f_type, ctx);
                match &f_type_whnf.kind {
                    ExprKind::Pi(_, _expected_arg_type, result_type) => {
                        Ok(result_type.instantiate(a))
                    }
                    _ => Err(TypeError::NotAPi { ty: Arc::new(f_type) }),
                }
            }
            // :479-517 with the :486 domain-sort gate SKIPPED.
            ExprKind::Lam(bi, arg_type, body) => {
                let fvar_id = ctx.push(name_anon(), arg_type.as_ref().clone(), *bi);
                let body_with_fvar = self.open_bvar(body, fvar_id);
                let body_type = self.infer_type_infer_only_core(&body_with_fvar, ctx);
                ctx.pop();
                let body_type = body_type?;
                let body_type_abstract = body_type.abstract_fvar(fvar_id);
                Ok(Expr::from_kind(ExprKind::Pi(
                    *bi,
                    arg_type.clone(),
                    Arc::new(body_type_abstract),
                )))
            }
            // :518-549 — Pi has no infer_only gate (identical to check mode).
            ExprKind::Pi(bi, arg_type, body) => {
                let arg_sort = self.infer_type_infer_only_core(arg_type, ctx)?;
                let arg_sort_whnf = self.whnf_impl(&arg_sort, ctx);
                let l1 = match &arg_sort_whnf.kind {
                    ExprKind::Sort(l) => l.clone(),
                    _ => return Err(TypeError::ExpectedSort { ty: Arc::new(arg_sort) }),
                };
                let fvar_id = ctx.push(name_anon(), arg_type.as_ref().clone(), *bi);
                let body_with_fvar = self.open_bvar(body, fvar_id);
                let body_sort = self.infer_type_infer_only_core(&body_with_fvar, ctx);
                ctx.pop();
                let body_sort = body_sort?;
                let body_sort_whnf = self.whnf_impl(&body_sort, ctx);
                let l2 = match &body_sort_whnf.kind {
                    ExprKind::Sort(l) => l.clone(),
                    _ => return Err(TypeError::ExpectedSort { ty: Arc::new(body_sort) }),
                };
                Ok(Expr::sort(Level::imax(l1, l2)))
            }
            // :551-609 with the :556 type/value gates SKIPPED.
            ExprKind::Let(let_name, ty, val, body, _nondep) => {
                let fvar_id =
                    ctx.push_let(let_name.clone(), ty.as_ref().clone(), val.as_ref().clone());
                let body_with_fvar = self.open_bvar(body, fvar_id);
                let body_type = self.infer_type_infer_only_core(&body_with_fvar, ctx);
                ctx.pop();
                let body_type = body_type?;
                Ok(body_type.subst_fvar(fvar_id, val))
            }
            ExprKind::Lit(lit) => Ok(match lit {
                Literal::Nat(_) => Expr::cnst(nat_type_name()),
                Literal::Str(_) => Expr::cnst(str_type_name()),
            }),
            ExprKind::MData(_, inner) => self.infer_type_infer_only_core(inner, ctx),
            _ => Err(TypeError::Unsupported),
        }
    }

    // ── INFER-TYPE pillar (tc/infer.rs:322-648 infer_type_fast_inner) — the
    // R8 DE-MODELING OF B3: the Lam/Pi/Let arms now run the PRODUCTION
    // open-with-FVar discipline (ctx_push a fresh FVar carrying the binder
    // domain → open_bvar instantiates the body with it → infer over the
    // CLOSED opened body → ctx_pop → abstract_fvar / subst_fvar to close),
    // the FVar arm is the production context lookup, and the BVar arm is the
    // production HARD ERROR. [C-refcell]: &mut LocalContext threading in
    // place of TypeChecker.ctx: RefCell<LocalContext>. ──
    fn infer_type(&self, e: &Expr) -> Result<Expr, TypeError> {
        // Fresh context per entry: used by const_type's B1 model and the
        // closed-term probes. (Production infer_type runs on self.ctx; the
        // decl gate creates that context once per decl — see
        // check_decl_readonly, which threads ONE context through §5+§7.)
        let mut ctx = LocalContext::new();
        self.infer_type_core(e, &mut ctx)
    }

    /// tc/eta.rs:196-199 — VERBATIM: "Replace BVar(0) with FVar(id)". The
    /// OPEN half of the binder discipline, reusing the VERIFIED instantiate
    /// (FVar is closed, so the instantiate lift is the identity on it).
    fn open_bvar(&self, e: &Expr, id: FVarId) -> Expr {
        e.instantiate(&Expr::from_kind(ExprKind::FVar(id)))
    }

    fn infer_type_core(&self, e: &Expr, ctx: &mut LocalContext) -> Result<Expr, TypeError> {
        match &e.kind {
            // tc/infer.rs:324 — PRODUCTION: a dangling BVar is an ERROR (the
            // opened path never sees one; R6's de-Bruijn lookup is GONE).
            ExprKind::BVar(idx) => Err(TypeError::UnboundVariable(*idx)),

            // tc/infer.rs:325-332 — FVar types come from the CONTEXT LOOKUP;
            // map/ok_or → match [B9].
            ExprKind::FVar(id) => match ctx.get(*id) {
                Some(d) => Ok(d.type_.clone()),
                None => Err(TypeError::UnknownFVar(*id)),
            },

            // Sort(l) : Sort(succ l) — the FULL Level succ (tc/infer.rs:334).
            ExprKind::Sort(l) => Ok(Expr::sort(Level::succ(l.clone()))),

            ExprKind::Const(name, _levels) => match self.const_type(name) {
                Some(ty) => Ok(ty),
                None => Err(TypeError::UnknownConst(name.clone())),
            },

            ExprKind::App(f, a) => {
                let f_type = self.infer_type_core(f, ctx)?;
                let f_type_whnf = self.whnf_impl(&f_type, ctx);
                match &f_type_whnf.kind {
                    ExprKind::Pi(_, expected_arg_type, result_type) => {
                        let arg_type = self.infer_type_core(a, ctx)?;
                        if !self.is_def_eq(&arg_type, expected_arg_type, ctx) {
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

            // tc/infer.rs:479-517 — Lam: the check-mode domain-sort gate
            // (infer_only=false on the gate surface — B4), then THE
            // PRODUCTION OPEN → INFER → CLOSE:
            //   ctx_push(Name::anon(), domain, *bi)   (:503)
            //   open_bvar(body, fvar_id)              (:504)
            //   infer over the opened (closed) body   (:506)
            //   ctx_pop()                             (:509)
            //   body_type.abstract_fvar(fvar_id)      (:511)
            //   Pi(*bi, domain, abstracted)           (:512-516)
            ExprKind::Lam(bi, arg_type, body) => {
                let arg_sort = self.infer_type_core(arg_type, ctx)?;
                let arg_sort_whnf = self.whnf_impl(&arg_sort, ctx);
                match &arg_sort_whnf.kind {
                    ExprKind::Sort(_) => {}
                    _ => return Err(TypeError::ExpectedSort { ty: Arc::new(arg_sort) }),
                }
                let fvar_id = ctx.push(name_anon(), arg_type.as_ref().clone(), *bi);
                let body_with_fvar = self.open_bvar(body, fvar_id);
                let body_type = self.infer_type_core(&body_with_fvar, ctx);
                ctx.pop();
                let body_type = body_type?;
                let body_type_abstract = body_type.abstract_fvar(fvar_id);
                Ok(Expr::from_kind(ExprKind::Pi(
                    *bi,
                    arg_type.clone(),
                    Arc::new(body_type_abstract),
                )))
            }

            // tc/infer.rs:518-549 — Pi: domain sort, OPEN the body with a
            // fresh FVar, infer ITS sort (which may be recovered by looking
            // the opened FVar's type up in the context), pop, imax.
            // let-else (:524/:541) → match [B9].
            ExprKind::Pi(bi, arg_type, body) => {
                let arg_sort = self.infer_type_core(arg_type, ctx)?;
                let arg_sort_whnf = self.whnf_impl(&arg_sort, ctx);
                let l1 = match &arg_sort_whnf.kind {
                    ExprKind::Sort(l) => l.clone(),
                    _ => return Err(TypeError::ExpectedSort { ty: Arc::new(arg_sort) }),
                };
                let fvar_id = ctx.push(name_anon(), arg_type.as_ref().clone(), *bi);
                let body_with_fvar = self.open_bvar(body, fvar_id);
                let body_sort = self.infer_type_core(&body_with_fvar, ctx);
                ctx.pop();
                let body_sort = body_sort?;
                let body_sort_whnf = self.whnf_impl(&body_sort, ctx);
                let l2 = match &body_sort_whnf.kind {
                    ExprKind::Sort(l) => l.clone(),
                    _ => return Err(TypeError::ExpectedSort { ty: Arc::new(body_sort) }),
                };
                Ok(Expr::sort(Level::imax(l1, l2)))
            }

            // tc/infer.rs:551-609 — Let: the check-mode type/value gates,
            // then ctx_push_let(let_name.clone(), ty, val) (:596-597), open
            // (:598), infer, pop (:603), and ZETA — subst_fvar(fvar_id, val)
            // directly (:605-609: "Lean 4 abstracts then reconstructs Let
            // binders, but single-variable subst_fvar is equivalent" — the
            // production comment).
            ExprKind::Let(let_name, ty, val, body, _nondep) => {
                let ty_sort = self.infer_type_core(ty, ctx)?;
                let ty_sort_whnf = self.whnf_impl(&ty_sort, ctx);
                match &ty_sort_whnf.kind {
                    ExprKind::Sort(_) => {}
                    _ => return Err(TypeError::ExpectedSort { ty: Arc::new(ty_sort) }),
                }
                let val_type = self.infer_type_core(val, ctx)?;
                if !self.is_def_eq(&val_type, ty, ctx) {
                    return Err(TypeError::TypeMismatch {
                        expected: Arc::new(ty.as_ref().clone()),
                        inferred: Arc::new(val_type),
                    });
                }
                let fvar_id =
                    ctx.push_let(let_name.clone(), ty.as_ref().clone(), val.as_ref().clone());
                let body_with_fvar = self.open_bvar(body, fvar_id);
                let body_type = self.infer_type_core(&body_with_fvar, ctx);
                ctx.pop();
                let body_type = body_type?;
                Ok(body_type.subst_fvar(fvar_id, val))
            }

            // B11: the Lit type names are REAL Names built from literal parts
            // (production references interned Nat/String constants —
            // value-identical, zero residual cache boundary).
            ExprKind::Lit(lit) => Ok(match lit {
                Literal::Nat(_) => Expr::cnst(nat_type_name()),
                Literal::Str(_) => Expr::cnst(str_type_name()),
            }),

            ExprKind::MData(_, inner) => self.infer_type_core(inner, ctx),

            // Proj inference deferred here (verified separately in the
            // infer_ext rung) — the decl gate cases never reach it.
            _ => Err(TypeError::Unsupported),
        }
    }

    // ── §5: infer_sort (tc/infer.rs:735-742 / :765-800 infer_sort_inner) —
    // VERBATIM control flow; the Pi fallback arm now OPENS the body with a
    // fresh FVar exactly like production (:786-791). The context is the
    // CALLER's (production: self.ctx on the shared per-decl TypeChecker).
    // B4 pass-throughs (stack_safe / infer_only save-restore) elided. ──
    const INFER_SORT_MAX_DEPTH: u32 = 64;

    fn infer_sort(&self, e: &Expr, ctx: &mut LocalContext) -> Result<Level, TypeError> {
        self.infer_sort_inner(e, 0, ctx)
    }

    fn infer_sort_inner(
        &self,
        e: &Expr,
        depth: u32,
        ctx: &mut LocalContext,
    ) -> Result<Level, TypeError> {
        let ty = self.infer_type_core(e, ctx)?;
        let ty_whnf = self.whnf_impl(&ty, ctx);
        match &ty_whnf.kind {
            ExprKind::Sort(l) => Ok(l.clone()),
            ExprKind::Pi(bd, arg_type, body) => {
                if depth >= Self::INFER_SORT_MAX_DEPTH {
                    // SOUNDNESS (tc/infer.rs:776-784): under-reporting a deep
                    // universe as Prop would defeat the theorem-is-Prop gate.
                    return Err(TypeError::SortDepthExceeded { depth });
                }
                let arg_level = self.infer_sort_inner(arg_type, depth + 1, ctx)?;
                let fvar_id = ctx.push(name_anon(), arg_type.as_ref().clone(), *bd);
                let body_with_fvar = self.open_bvar(body, fvar_id);
                let body_level_result = self.infer_sort_inner(&body_with_fvar, depth + 1, ctx);
                ctx.pop();
                let body_level = body_level_result?;
                Ok(Level::imax(arg_level, body_level))
            }
            _ => Err(TypeError::ExpectedSort {
                ty: Arc::new(ty),
            }),
        }
    }

    // ── §7: check_type (tc/infer.rs:670-695) — VERBATIM minus infer_only/
    // heartbeat plumbing (B4); runs on the SHARED gate context ([C-refcell]:
    // production check() infers via the SAME TypeChecker self.ctx that §5's
    // infer_sort used — the FVarId counter continues across the steps). ──
    fn check_type(
        &self,
        e: &Expr,
        expected: &Expr,
        ctx: &mut LocalContext,
    ) -> Result<(), TypeError> {
        let inferred = self.infer_type_core(e, ctx)?;
        if self.is_def_eq(&inferred, expected, ctx) {
            Ok(())
        } else {
            Err(TypeError::TypeMismatch {
                expected: Arc::new(expected.clone()),
                inferred: Arc::new(inferred),
            })
        }
    }
}
// ── env/types.rs Declaration (:338) — all 4 variants, VERBATIM field shape
// except type_/value are Arc<Expr> (B6). Variant order VERBATIM
// (Definition=0, Axiom=1, Theorem=2, Opaque=3). Names are REAL. ──
#[derive(Clone, Debug)]
pub enum Declaration {
    Definition {
        name: Name,
        level_params: Vec<Name>,
        type_: Arc<Expr>,
        value: Arc<Expr>,
        is_reducible: bool,
    },
    Axiom {
        name: Name,
        level_params: Vec<Name>,
        type_: Arc<Expr>,
    },
    Theorem {
        name: Name,
        level_params: Vec<Name>,
        type_: Arc<Expr>,
        value: Arc<Expr>,
    },
    Opaque {
        name: Name,
        level_params: Vec<Name>,
        type_: Arc<Expr>,
        value: Arc<Expr>,
    },
}

// ── env/types.rs EnvError (:388) — the 6 variants check_decl_readonly can
// reach, in the REAL enum's source order (subset discriminants 0..5). ──
#[derive(Clone, Debug)]
pub enum EnvError {
    TypeCheckFailed { name: Name, source: TypeError },
    DuplicateLevelParam { name: Name, param: Name },
    TheoremTypeNotProp { name: Name, sort: Level },
    ContainsFreeVar { name: Name },
    ContainsMetavar { name: Name },
    UndefinedLevelParam { name: Name, param: Name },
}

// ── env/decl_add.rs:64 find_undef_level_param_in_level — VERBATIM; the generic
// `allowed.contains(n)` (core slice body) rewritten as an index loop whose
// element equality is the PRODUCTION name_eq (B9; production `[Name]::contains`
// uses exactly `Name::eq`). The Max/IMax push arms are the universe-polymorphic
// §4 surface. ──
fn find_undef_level_param_in_level(l: &Level, allowed: &[Name]) -> Option<Name> {
    let mut level_stack: Vec<&Level> = vec![l];
    while let Some(curr) = level_stack.pop() {
        match curr {
            Level::Zero => {}
            Level::Param(n) => {
                let mut found = false;
                let mut k: usize = 0;
                while k < allowed.len() {
                    if name_eq(&allowed[k], n) {
                        found = true;
                        break;
                    }
                    k += 1;
                }
                if !found {
                    return Some(n.clone());
                }
            }
            Level::Succ(inner) => level_stack.push(inner),
            Level::Max(a, b) | Level::IMax(a, b) => {
                level_stack.push(b);
                level_stack.push(a);
            }
        }
    }
    None
}

// ── env/decl_add.rs:88 find_undef_level_param — VERBATIM over the slice's
// 11-variant ExprKind core (B5); the Const-levels `for` loop rewritten as an
// index loop (B9). ──
fn find_undef_level_param(e: &Expr, allowed: &[Name]) -> Option<Name> {
    let mut expr_stack: Vec<&Expr> = vec![e];
    while let Some(curr) = expr_stack.pop() {
        match curr.kind() {
            ExprKind::Sort(l) => {
                if let Some(undef) = find_undef_level_param_in_level(l, allowed) {
                    return Some(undef);
                }
            }
            ExprKind::Const(_, levels) => {
                let mut li: usize = 0;
                while li < levels.len() {
                    if let Some(undef) = find_undef_level_param_in_level(&levels[li], allowed) {
                        return Some(undef);
                    }
                    li += 1;
                }
            }
            ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Lit(_) => {}
            ExprKind::App(f, a) => {
                expr_stack.push(a);
                expr_stack.push(f);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                expr_stack.push(body);
                expr_stack.push(ty);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                expr_stack.push(body);
                expr_stack.push(val);
                expr_stack.push(ty);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
                expr_stack.push(inner);
            }
        }
    }
    None
}

impl<'env> Verifier<'env> {
    // ── THE UNIVERSAL DECL GATE: env/decl_add.rs:229 check_decl_readonly —
    // VERBATIM steps §2(dup level params — REAL name_eq), §3(no mvar/fvar),
    // §4(level-param closure — REAL name_eq), §5(infer_sort), §6(theorem-is-
    // Prop), §7(check_type). Elided (B4): the TypeChecker construction /
    // heartbeat / cache-limit / profiler / loc plumbing. REWRITES (B9): the §2
    // `iter().enumerate()` + prefix `contains` -> index loops with identical
    // first-hit semantics (element equality = production Name::eq); `map_err`
    // -> match with identical control flow. Name payload copies are real
    // clones. ──
    pub fn check_decl_readonly(&self, decl: &Declaration) -> Result<(), EnvError> {
        // Phase-1 field extraction — exactly as add_decl's.
        let (name, level_params, type_, opt_value, is_theorem): (
            &Name,
            &Vec<Name>,
            &Arc<Expr>,
            Option<&Arc<Expr>>,
            bool,
        ) = match decl {
            Declaration::Definition {
                name,
                level_params,
                type_,
                value,
                ..
            } => (name, level_params, type_, Some(value), false),
            Declaration::Axiom {
                name,
                level_params,
                type_,
            } => (name, level_params, type_, None, false),
            Declaration::Theorem {
                name,
                level_params,
                type_,
                value,
            } => (name, level_params, type_, Some(value), true),
            Declaration::Opaque {
                name,
                level_params,
                type_,
                value,
            } => (name, level_params, type_, Some(value), false),
        };

        // (2) Duplicate universe level parameters — REAL name_eq detection.
        {
            let n = level_params.len();
            let mut i: usize = 0;
            while i < n {
                let mut j: usize = 0;
                while j < i {
                    if name_eq(&level_params[j], &level_params[i]) {
                        return Err(EnvError::DuplicateLevelParam {
                            name: name.clone(),
                            param: level_params[i].clone(),
                        });
                    }
                    j += 1;
                }
                i += 1;
            }
        }

        // (3) Reject metavariables and free variables in type and value.
        if type_.has_expr_mvar_quick() || type_.has_level_mvar_quick() {
            return Err(EnvError::ContainsMetavar { name: name.clone() });
        }
        if type_.has_fvar_quick() {
            return Err(EnvError::ContainsFreeVar { name: name.clone() });
        }
        if let Some(value) = opt_value {
            if value.has_expr_mvar_quick() || value.has_level_mvar_quick() {
                return Err(EnvError::ContainsMetavar { name: name.clone() });
            }
            if value.has_fvar_quick() {
                return Err(EnvError::ContainsFreeVar { name: name.clone() });
            }
        }

        // (4) All Level::Param references must be in the declared level_params.
        if let Some(undef) = find_undef_level_param(type_, level_params) {
            return Err(EnvError::UndefinedLevelParam {
                name: name.clone(),
                param: undef,
            });
        }
        if let Some(value) = opt_value {
            if let Some(undef) = find_undef_level_param(value, level_params) {
                return Err(EnvError::UndefinedLevelParam {
                    name: name.clone(),
                    param: undef,
                });
            }
        }

        // (5)-(7): production constructs ONE per-call TypeChecker
        // (decl_add.rs:409-434) whose LocalContext — and its monotonic
        // FVarId counter — is SHARED across §5 infer_sort and §7 check_type,
        // never reset between the steps. Transcribed as one LocalContext
        // threaded through both calls [C-refcell].
        let mut tc_ctx = LocalContext::new();

        // (5) The type must be well-formed: infer_sort yields a Sort.
        let sort = match self.infer_sort(type_, &mut tc_ctx) {
            Ok(s) => s,
            Err(e) => {
                return Err(EnvError::TypeCheckFailed {
                    name: name.clone(),
                    source: e,
                })
            }
        };

        // (6) For theorems: type must live in Prop (Sort 0) — over the FULL
        // Level, is_zero recurses Max/IMax children.
        if is_theorem && !sort.is_zero() {
            return Err(EnvError::TheoremTypeNotProp {
                name: name.clone(),
                sort,
            });
        }

        // (7) For value-bearing decls: value must have the declared type.
        if let Some(value) = opt_value {
            match self.check_type(value, type_, &mut tc_ctx) {
                Ok(()) => {}
                Err(e) => {
                    return Err(EnvError::TypeCheckFailed {
                        name: name.clone(),
                        source: e,
                    })
                }
            }
        }

        Ok(())
    }
}

// ════════════════════════════════════════════════════════════════════════════
// THE R10-CONFIG CONTROL — NOT A PRODUCTION TRANSCRIPTION. This is the
// R10-LANDED def_eq configuration (e2e_binding_defeq.rs / the landed
// clean_binding_defeq_slice.rs aware chain) kept VERBATIM as the divergence
// CONTROL: EAGER FULL-DELTA WHNF up front, meta+structural fast path,
// binding dispatch at the whnf'd congruence position, proof-irrel consult,
// raw congruence arms, the OLD lift-and-apply eta. Adapted ONLY to the R11
// EnvEntry env shape: unfold_const_blind returns ANY Some(value) — ignoring
// kind / reducibility / the #1277 arity gate, exactly the R10 semantics
// (hint fields did not exist in the R10 model) — and const_type_blind reads
// the stored type_ (B1', shared with the aware chain so the control
// isolates the DEF_EQ difference, not the env model). Its whnf is a
// SEPARATE _blind copy this round: the aware whnf gained the production
// unfold gate [B-whnf-gate]; the control must keep blasting through Opaque
// values — that is the falsification lever of case 23.
// ld_blind_root runs the same 28 decl cases through this chain: it must
// AGREE with ld_gate_root on 0..22 (the R10 verdicts) and on 24-27, and
// ACCEPT case 23 (which the aware/production gate REJECTS) — divergence set
// EXACTLY {23}.
// ════════════════════════════════════════════════════════════════════════════

impl<'env> Verifier<'env> {
    /// The R10 unfold semantics: ANY stored value unfolds (no kind /
    /// reducibility / arity gates — they did not exist in the R10 model).
    fn unfold_const_blind(&self, name: &Name) -> Option<Expr> {
        match self.find_entry(name) {
            Some(info) => info.value.clone(),
            None => None,
        }
    }

    /// B1' stored type (shared model — see the header note).
    fn const_type_blind(&self, name: &Name) -> Option<Expr> {
        match self.find_entry(name) {
            Some(info) => Some(info.type_.clone()),
            None => None,
        }
    }

    // ── The R10 whnf text VERBATIM (context-aware zeta, EAGER Const
    // unfolding via unfold_const_blind). ──
    fn whnf_impl_blind(&self, e: &Expr, ctx: &LocalContext) -> Expr { self.whnf_inner_blind(e, ctx) }
    fn whnf_inner_blind(&self, e: &Expr, ctx: &LocalContext) -> Expr {
        match &e.kind {
            ExprKind::App(f, a) => {
                let f_whnf = self.whnf_impl_blind(f, ctx);
                match &f_whnf.kind {
                    ExprKind::Lam(_, _, body) => { let reduced = body.instantiate(a); self.whnf_impl_blind(&reduced, ctx) }
                    _ => {
                        let app = Expr::from_kind(ExprKind::App(Arc::new(f_whnf), a.clone()));
                        if let Some(reduced) = self.try_iota_reduction(&app) { return self.whnf_impl_blind(&reduced, ctx); }
                        if let Some(reduced) = self.try_quot_reduction(&app) { return self.whnf_impl_blind(&reduced, ctx); }
                        app
                    }
                }
            }
            ExprKind::Let(_, _, val, body, _) => { let reduced = body.instantiate(val); self.whnf_impl_blind(&reduced, ctx) }
            ExprKind::Const(name, _levels) => match self.unfold_const_blind(name) {
                Some(val) => self.whnf_impl_blind(&val, ctx),
                None => e.clone(),
            },
            ExprKind::FVar(id) => {
                let val_opt: Option<Expr> = match ctx.get(*id) {
                    Some(d) => d.value.clone(),
                    None => None,
                };
                match val_opt {
                    Some(val) => self.whnf_impl_blind(&val, ctx),
                    None => e.clone(),
                }
            }
            ExprKind::Proj(struct_name, idx, expr) => self.reduce_proj_blind(struct_name, *idx, expr, ctx),
            ExprKind::MData(_, inner) => self.whnf_impl_blind(inner, ctx),
            _ => e.clone(),
        }
    }
    fn reduce_proj_blind(&self, struct_name: &Name, idx: u32, expr: &Expr, ctx: &LocalContext) -> Expr {
        let expr_whnf = self.whnf_impl_blind(expr, ctx);
        let head = expr_whnf.get_app_fn();
        if let ExprKind::Const(ctor_name, _) = &head.kind {
            if let Some(num_params) = self.get_constructor_num_params(ctor_name) {
                let args = expr_whnf.get_app_args();
                let field_idx = num_params as usize + idx as usize;
                if field_idx < args.len() { return self.whnf_impl_blind(&args[field_idx], ctx); }
            }
        }
        Expr::from_kind(ExprKind::Proj(struct_name.clone(), idx, Arc::new(expr_whnf)))
    }

    // ── The R10 aware def_eq text VERBATIM, routed blind: eager whnf both
    // sides; meta+structural fast path; BINDING dispatch on the whnf'd
    // binder pair; proof-irrel consult; raw congruence; the old eta. ──
    fn is_def_eq_blind(&self, a: &Expr, b: &Expr, ctx: &mut LocalContext) -> bool { self.def_eq_blind_inner(a, b, ctx) }
    fn def_eq_blind_impl(&self, a: &Expr, b: &Expr, ctx: &mut LocalContext) -> bool { self.def_eq_blind_inner(a, b, ctx) }
    fn def_eq_blind_inner(&self, a: &Expr, b: &Expr, ctx: &mut LocalContext) -> bool {
        let a_whnf = self.whnf_impl_blind(a, ctx);
        let b_whnf = self.whnf_impl_blind(b, ctx);
        if a_whnf.meta().raw() == b_whnf.meta().raw() && self.structural_eq(&a_whnf, &b_whnf) {
            return true;
        }
        match (&a_whnf.kind, &b_whnf.kind) {
            (ExprKind::Lam(..), ExprKind::Lam(..))
            | (ExprKind::Pi(..), ExprKind::Pi(..)) => {
                return self.is_def_eq_binding_blind(&a_whnf, &b_whnf, ctx);
            }
            _ => {}
        }
        let proof_irrel = self.is_def_eq_proof_irrel_blind(&a_whnf, &b_whnf, ctx);
        match proof_irrel {
            Some(true) => return true,
            _ => {}
        }
        let matched = match (&a_whnf.kind, &b_whnf.kind) {
            (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
            (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => self.level_eq(l1, l2),
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => name_eq(n1, n2) && self.level_vec_eq(ls1, ls2),
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => self.def_eq_blind_impl(f1, f2, ctx) && self.def_eq_blind_impl(a1, a2, ctx),
            (ExprKind::Let(_, ty1, v1, b1, _), ExprKind::Let(_, ty2, v2, b2, _)) => self.def_eq_blind_impl(ty1, ty2, ctx) && self.def_eq_blind_impl(v1, v2, ctx) && self.def_eq_blind_impl(b1, b2, ctx),
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => name_eq(n1, n2) && i1 == i2 && self.def_eq_blind_impl(e1, e2, ctx),
            (ExprKind::MData(_, in1), ExprKind::MData(_, in2)) => self.def_eq_blind_impl(in1, in2, ctx),
            _ => false,
        };
        if matched { return true; }
        self.try_eta_blind(&a_whnf, &b_whnf, ctx)
    }
    fn try_eta_blind(&self, a: &Expr, b: &Expr, ctx: &mut LocalContext) -> bool {
        match (&a.kind, &b.kind) {
            (ExprKind::Lam(_, _ty, body), _) => {
                let other_lifted = b.lift_from(0, 1);
                let other_applied = Expr::app(other_lifted, Expr::bvar(0));
                self.def_eq_blind_impl(body, &other_applied, ctx)
            }
            (_, ExprKind::Lam(_, _ty, body)) => {
                let other_lifted = a.lift_from(0, 1);
                let other_applied = Expr::app(other_lifted, Expr::bvar(0));
                self.def_eq_blind_impl(body, &other_applied, ctx)
            }
            _ => false,
        }
    }

    /// The R10 is_def_eq_binding text routed to the blind def_eq (the
    /// shared expr_syntactic_eq pre-check, has_loose_bvars fast path,
    /// shared-FVar opening and truncate_to are byte-identical machinery).
    fn is_def_eq_binding_blind(&self, a: &Expr, b: &Expr, ctx: &mut LocalContext) -> bool {
        let save_len = ctx.len();
        let binder_is_lam = matches!(&a.kind, ExprKind::Lam(_, _, _));
        let mut a = a.clone();
        let mut b = b.clone();

        loop {
            let (ty1, body1): (Arc<Expr>, Arc<Expr>) = match &a.kind {
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    (ty.clone(), body.clone())
                }
                _ => return false,
            };
            let (bi2, ty2, body2): (BinderData, Arc<Expr>, Arc<Expr>) = match &b.kind {
                ExprKind::Lam(bi, ty, body) | ExprKind::Pi(bi, ty, body) => {
                    (*bi, ty.clone(), body.clone())
                }
                _ => return false,
            };

            if !expr_syntactic_eq(&ty1, &ty2) && !self.def_eq_blind_impl(&ty1, &ty2, ctx) {
                ctx.truncate_to(save_len);
                return false;
            }

            if !body1.has_loose_bvars() && !body2.has_loose_bvars() {
                let result = self.def_eq_blind_impl(&body1, &body2, ctx);
                ctx.truncate_to(save_len);
                return result;
            }

            let local_id = ctx.push(name_anon(), ty2.as_ref().clone(), bi2);
            let a_next = self.open_bvar(&body1, local_id);
            let b_next = self.open_bvar(&body2, local_id);
            let a_same = if binder_is_lam {
                matches!(&a_next.kind, ExprKind::Lam(_, _, _))
            } else {
                matches!(&a_next.kind, ExprKind::Pi(_, _, _))
            };
            let b_same = if binder_is_lam {
                matches!(&b_next.kind, ExprKind::Lam(_, _, _))
            } else {
                matches!(&b_next.kind, ExprKind::Pi(_, _, _))
            };
            if a_same && b_same {
                a = a_next;
                b = b_next;
                continue;
            }

            let result = self.def_eq_blind_impl(&a_next, &b_next, ctx);
            ctx.truncate_to(save_len);
            return result;
        }
    }

    // ── The R10 proof-irrel blind chain (self-contained; whnf routed to
    // the blind copy; type_is_quickly_not_in_prop is pure and shared). ──
    fn is_def_eq_proof_irrel_blind(
        &self,
        a: &Expr,
        b: &Expr,
        ctx: &mut LocalContext,
    ) -> Option<bool> {
        let ty_a = match self.infer_type_quick_or_full_blind(a, ctx) {
            Some(t) => t,
            None => return None,
        };
        if self.type_is_quickly_not_in_prop(&ty_a) {
            return None;
        }
        match self.type_is_proof_irrelevant_blind(&ty_a, ctx) {
            Some(true) => {}
            Some(false) => return None,
            None => return None,
        }
        let ty_b = match self.infer_type_quick_or_full_blind(b, ctx) {
            Some(t) => t,
            None => return None,
        };
        Some(self.def_eq_blind_impl(&ty_a, &ty_b, ctx))
    }

    fn infer_type_quick_or_full_blind(&self, e: &Expr, ctx: &mut LocalContext) -> Option<Expr> {
        match self.try_infer_type_quick_blind(e, ctx) {
            Some(ty) => Some(ty),
            None => match self.infer_type_infer_only_core_blind(e, ctx) {
                Ok(t) => Some(t),
                Err(_) => None,
            },
        }
    }

    fn type_is_proof_irrelevant_blind(&self, ty: &Expr, ctx: &mut LocalContext) -> Option<bool> {
        let ty_whnf = self.whnf_impl_blind(ty, ctx);
        if matches!(&ty_whnf.kind, ExprKind::Sort(_)) {
            return Some(false);
        }
        let ty_of_ty = match self.infer_type_quick_or_full_blind(&ty_whnf, ctx) {
            Some(t) => t,
            None => return None,
        };
        let ty_of_ty_whnf = self.whnf_impl_blind(&ty_of_ty, ctx);
        match &ty_of_ty_whnf.kind {
            ExprKind::Sort(l) => Some(l.is_zero()),
            _ => Some(false),
        }
    }

    fn try_infer_type_quick_blind(&self, e: &Expr, ctx: &LocalContext) -> Option<Expr> {
        self.try_infer_type_quick_inner_blind(e, ctx)
    }
    fn try_infer_type_quick_inner_blind(&self, e: &Expr, ctx: &LocalContext) -> Option<Expr> {
        match &e.kind {
            ExprKind::FVar(id) => match ctx.get(*id) {
                Some(d) => Some(d.type_.clone()),
                None => None,
            },
            ExprKind::Const(name, _levels) => self.const_type_blind(name),
            ExprKind::Sort(l) => Some(Expr::from_kind(ExprKind::Sort(Level::succ(l.clone())))),
            ExprKind::App(f, a) => {
                let f_type = match self.try_infer_type_quick_blind(f, ctx) {
                    Some(t) => t,
                    None => return None,
                };
                let f_type_whnf = self.whnf_impl_blind(&f_type, ctx);
                match &f_type_whnf.kind {
                    ExprKind::Pi(_, _, result_type) => Some(result_type.instantiate(a)),
                    _ => None,
                }
            }
            ExprKind::Lam(bi, ty, body) => {
                let body_type = match self.try_infer_type_quick_blind(body, ctx) {
                    Some(t) => t,
                    None => return None,
                };
                Some(Expr::pi(*bi, ty.as_ref().clone(), body_type))
            }
            ExprKind::Lit(lit) => Some(match lit {
                Literal::Nat(_) => Expr::cnst(nat_type_name()),
                Literal::Str(_) => Expr::cnst(str_type_name()),
            }),
            ExprKind::MData(_, inner) => self.try_infer_type_quick_blind(inner, ctx),
            ExprKind::Proj(_, _, _) => None,
            _ => None,
        }
    }

    fn infer_type_infer_only_core_blind(
        &self,
        e: &Expr,
        ctx: &mut LocalContext,
    ) -> Result<Expr, TypeError> {
        match &e.kind {
            ExprKind::BVar(idx) => Err(TypeError::UnboundVariable(*idx)),
            ExprKind::FVar(id) => match ctx.get(*id) {
                Some(d) => Ok(d.type_.clone()),
                None => Err(TypeError::UnknownFVar(*id)),
            },
            ExprKind::Sort(l) => Ok(Expr::sort(Level::succ(l.clone()))),
            ExprKind::Const(name, _levels) => match self.const_type_blind(name) {
                Some(ty) => Ok(ty),
                None => Err(TypeError::UnknownConst(name.clone())),
            },
            ExprKind::App(f, a) => {
                let f_type = self.infer_type_infer_only_core_blind(f, ctx)?;
                let f_type_whnf = self.whnf_impl_blind(&f_type, ctx);
                match &f_type_whnf.kind {
                    ExprKind::Pi(_, _expected_arg_type, result_type) => {
                        Ok(result_type.instantiate(a))
                    }
                    _ => Err(TypeError::NotAPi { ty: Arc::new(f_type) }),
                }
            }
            ExprKind::Lam(bi, arg_type, body) => {
                let fvar_id = ctx.push(name_anon(), arg_type.as_ref().clone(), *bi);
                let body_with_fvar = self.open_bvar(body, fvar_id);
                let body_type = self.infer_type_infer_only_core_blind(&body_with_fvar, ctx);
                ctx.pop();
                let body_type = body_type?;
                let body_type_abstract = body_type.abstract_fvar(fvar_id);
                Ok(Expr::from_kind(ExprKind::Pi(
                    *bi,
                    arg_type.clone(),
                    Arc::new(body_type_abstract),
                )))
            }
            ExprKind::Pi(bi, arg_type, body) => {
                let arg_sort = self.infer_type_infer_only_core_blind(arg_type, ctx)?;
                let arg_sort_whnf = self.whnf_impl_blind(&arg_sort, ctx);
                let l1 = match &arg_sort_whnf.kind {
                    ExprKind::Sort(l) => l.clone(),
                    _ => return Err(TypeError::ExpectedSort { ty: Arc::new(arg_sort) }),
                };
                let fvar_id = ctx.push(name_anon(), arg_type.as_ref().clone(), *bi);
                let body_with_fvar = self.open_bvar(body, fvar_id);
                let body_sort = self.infer_type_infer_only_core_blind(&body_with_fvar, ctx);
                ctx.pop();
                let body_sort = body_sort?;
                let body_sort_whnf = self.whnf_impl_blind(&body_sort, ctx);
                let l2 = match &body_sort_whnf.kind {
                    ExprKind::Sort(l) => l.clone(),
                    _ => return Err(TypeError::ExpectedSort { ty: Arc::new(body_sort) }),
                };
                Ok(Expr::sort(Level::imax(l1, l2)))
            }
            ExprKind::Let(let_name, ty, val, body, _nondep) => {
                let fvar_id =
                    ctx.push_let(let_name.clone(), ty.as_ref().clone(), val.as_ref().clone());
                let body_with_fvar = self.open_bvar(body, fvar_id);
                let body_type = self.infer_type_infer_only_core_blind(&body_with_fvar, ctx);
                ctx.pop();
                let body_type = body_type?;
                Ok(body_type.subst_fvar(fvar_id, val))
            }
            ExprKind::Lit(lit) => Ok(match lit {
                Literal::Nat(_) => Expr::cnst(nat_type_name()),
                Literal::Str(_) => Expr::cnst(str_type_name()),
            }),
            ExprKind::MData(_, inner) => self.infer_type_infer_only_core_blind(inner, ctx),
            _ => Err(TypeError::Unsupported),
        }
    }

    // ── The R10 infer/gate chain routed blind (whnf → the blind copy;
    // inference discipline byte-identical). ──
    fn infer_type_blind(&self, e: &Expr) -> Result<Expr, TypeError> {
        let mut ctx = LocalContext::new();
        self.infer_type_core_blind(e, &mut ctx)
    }
    fn infer_type_core_blind(&self, e: &Expr, ctx: &mut LocalContext) -> Result<Expr, TypeError> {
        match &e.kind {
            ExprKind::BVar(idx) => Err(TypeError::UnboundVariable(*idx)),
            ExprKind::FVar(id) => match ctx.get(*id) {
                Some(d) => Ok(d.type_.clone()),
                None => Err(TypeError::UnknownFVar(*id)),
            },
            ExprKind::Sort(l) => Ok(Expr::sort(Level::succ(l.clone()))),
            ExprKind::Const(name, _levels) => match self.const_type_blind(name) {
                Some(ty) => Ok(ty),
                None => Err(TypeError::UnknownConst(name.clone())),
            },
            ExprKind::App(f, a) => {
                let f_type = self.infer_type_core_blind(f, ctx)?;
                let f_type_whnf = self.whnf_impl_blind(&f_type, ctx);
                match &f_type_whnf.kind {
                    ExprKind::Pi(_, expected_arg_type, result_type) => {
                        let arg_type = self.infer_type_core_blind(a, ctx)?;
                        if !self.is_def_eq_blind(&arg_type, expected_arg_type, ctx) {
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
                let arg_sort = self.infer_type_core_blind(arg_type, ctx)?;
                let arg_sort_whnf = self.whnf_impl_blind(&arg_sort, ctx);
                match &arg_sort_whnf.kind {
                    ExprKind::Sort(_) => {}
                    _ => return Err(TypeError::ExpectedSort { ty: Arc::new(arg_sort) }),
                }
                let fvar_id = ctx.push(name_anon(), arg_type.as_ref().clone(), *bi);
                let body_with_fvar = self.open_bvar(body, fvar_id);
                let body_type = self.infer_type_core_blind(&body_with_fvar, ctx);
                ctx.pop();
                let body_type = body_type?;
                let body_type_abstract = body_type.abstract_fvar(fvar_id);
                Ok(Expr::from_kind(ExprKind::Pi(
                    *bi,
                    arg_type.clone(),
                    Arc::new(body_type_abstract),
                )))
            }
            ExprKind::Pi(bi, arg_type, body) => {
                let arg_sort = self.infer_type_core_blind(arg_type, ctx)?;
                let arg_sort_whnf = self.whnf_impl_blind(&arg_sort, ctx);
                let l1 = match &arg_sort_whnf.kind {
                    ExprKind::Sort(l) => l.clone(),
                    _ => return Err(TypeError::ExpectedSort { ty: Arc::new(arg_sort) }),
                };
                let fvar_id = ctx.push(name_anon(), arg_type.as_ref().clone(), *bi);
                let body_with_fvar = self.open_bvar(body, fvar_id);
                let body_sort = self.infer_type_core_blind(&body_with_fvar, ctx);
                ctx.pop();
                let body_sort = body_sort?;
                let body_sort_whnf = self.whnf_impl_blind(&body_sort, ctx);
                let l2 = match &body_sort_whnf.kind {
                    ExprKind::Sort(l) => l.clone(),
                    _ => return Err(TypeError::ExpectedSort { ty: Arc::new(body_sort) }),
                };
                Ok(Expr::sort(Level::imax(l1, l2)))
            }
            ExprKind::Let(let_name, ty, val, body, _nondep) => {
                let ty_sort = self.infer_type_core_blind(ty, ctx)?;
                let ty_sort_whnf = self.whnf_impl_blind(&ty_sort, ctx);
                match &ty_sort_whnf.kind {
                    ExprKind::Sort(_) => {}
                    _ => return Err(TypeError::ExpectedSort { ty: Arc::new(ty_sort) }),
                }
                let val_type = self.infer_type_core_blind(val, ctx)?;
                if !self.is_def_eq_blind(&val_type, ty, ctx) {
                    return Err(TypeError::TypeMismatch {
                        expected: Arc::new(ty.as_ref().clone()),
                        inferred: Arc::new(val_type),
                    });
                }
                let fvar_id =
                    ctx.push_let(let_name.clone(), ty.as_ref().clone(), val.as_ref().clone());
                let body_with_fvar = self.open_bvar(body, fvar_id);
                let body_type = self.infer_type_core_blind(&body_with_fvar, ctx);
                ctx.pop();
                let body_type = body_type?;
                Ok(body_type.subst_fvar(fvar_id, val))
            }
            ExprKind::Lit(lit) => Ok(match lit {
                Literal::Nat(_) => Expr::cnst(nat_type_name()),
                Literal::Str(_) => Expr::cnst(str_type_name()),
            }),
            ExprKind::MData(_, inner) => self.infer_type_core_blind(inner, ctx),
            _ => Err(TypeError::Unsupported),
        }
    }

    fn infer_sort_blind(&self, e: &Expr, ctx: &mut LocalContext) -> Result<Level, TypeError> {
        self.infer_sort_inner_blind(e, 0, ctx)
    }
    fn infer_sort_inner_blind(
        &self,
        e: &Expr,
        depth: u32,
        ctx: &mut LocalContext,
    ) -> Result<Level, TypeError> {
        let ty = self.infer_type_core_blind(e, ctx)?;
        let ty_whnf = self.whnf_impl_blind(&ty, ctx);
        match &ty_whnf.kind {
            ExprKind::Sort(l) => Ok(l.clone()),
            ExprKind::Pi(bd, arg_type, body) => {
                if depth >= Self::INFER_SORT_MAX_DEPTH {
                    return Err(TypeError::SortDepthExceeded { depth });
                }
                let arg_level = self.infer_sort_inner_blind(arg_type, depth + 1, ctx)?;
                let fvar_id = ctx.push(name_anon(), arg_type.as_ref().clone(), *bd);
                let body_with_fvar = self.open_bvar(body, fvar_id);
                let body_level_result = self.infer_sort_inner_blind(&body_with_fvar, depth + 1, ctx);
                ctx.pop();
                let body_level = body_level_result?;
                Ok(Level::imax(arg_level, body_level))
            }
            _ => Err(TypeError::ExpectedSort {
                ty: Arc::new(ty),
            }),
        }
    }
    fn check_type_blind(
        &self,
        e: &Expr,
        expected: &Expr,
        ctx: &mut LocalContext,
    ) -> Result<(), TypeError> {
        let inferred = self.infer_type_core_blind(e, ctx)?;
        if self.is_def_eq_blind(&inferred, expected, ctx) {
            Ok(())
        } else {
            Err(TypeError::TypeMismatch {
                expected: Arc::new(expected.clone()),
                inferred: Arc::new(inferred),
            })
        }
    }

    /// The R10 gate text with §5/§7 routed to the blind chain (§2-§4/§6
    /// are pillar-free and shared verbatim).
    pub fn check_decl_readonly_blind(&self, decl: &Declaration) -> Result<(), EnvError> {
        let (name, level_params, type_, opt_value, is_theorem): (
            &Name,
            &Vec<Name>,
            &Arc<Expr>,
            Option<&Arc<Expr>>,
            bool,
        ) = match decl {
            Declaration::Definition {
                name,
                level_params,
                type_,
                value,
                ..
            } => (name, level_params, type_, Some(value), false),
            Declaration::Axiom {
                name,
                level_params,
                type_,
            } => (name, level_params, type_, None, false),
            Declaration::Theorem {
                name,
                level_params,
                type_,
                value,
            } => (name, level_params, type_, Some(value), true),
            Declaration::Opaque {
                name,
                level_params,
                type_,
                value,
            } => (name, level_params, type_, Some(value), false),
        };

        {
            let n = level_params.len();
            let mut i: usize = 0;
            while i < n {
                let mut j: usize = 0;
                while j < i {
                    if name_eq(&level_params[j], &level_params[i]) {
                        return Err(EnvError::DuplicateLevelParam {
                            name: name.clone(),
                            param: level_params[i].clone(),
                        });
                    }
                    j += 1;
                }
                i += 1;
            }
        }

        if type_.has_expr_mvar_quick() || type_.has_level_mvar_quick() {
            return Err(EnvError::ContainsMetavar { name: name.clone() });
        }
        if type_.has_fvar_quick() {
            return Err(EnvError::ContainsFreeVar { name: name.clone() });
        }
        if let Some(value) = opt_value {
            if value.has_expr_mvar_quick() || value.has_level_mvar_quick() {
                return Err(EnvError::ContainsMetavar { name: name.clone() });
            }
            if value.has_fvar_quick() {
                return Err(EnvError::ContainsFreeVar { name: name.clone() });
            }
        }

        if let Some(undef) = find_undef_level_param(type_, level_params) {
            return Err(EnvError::UndefinedLevelParam {
                name: name.clone(),
                param: undef,
            });
        }
        if let Some(value) = opt_value {
            if let Some(undef) = find_undef_level_param(value, level_params) {
                return Err(EnvError::UndefinedLevelParam {
                    name: name.clone(),
                    param: undef,
                });
            }
        }

        let mut tc_ctx = LocalContext::new();

        let sort = match self.infer_sort_blind(type_, &mut tc_ctx) {
            Ok(s) => s,
            Err(e) => {
                return Err(EnvError::TypeCheckFailed {
                    name: name.clone(),
                    source: e,
                })
            }
        };

        if is_theorem && !sort.is_zero() {
            return Err(EnvError::TheoremTypeNotProp {
                name: name.clone(),
                sort,
            });
        }

        if let Some(value) = opt_value {
            match self.check_type_blind(value, type_, &mut tc_ctx) {
                Ok(()) => {}
                Err(e) => {
                    return Err(EnvError::TypeCheckFailed {
                        name: name.clone(),
                        source: e,
                    })
                }
            }
        }

        Ok(())
    }
}
// ════════════════════════════════════════════════════════════════════════════
// IN-MODULE NAMES — every Name the harness scenarios use, built from literal
// parts ([T-unroll]: `from_string_uncached` unrolled), exactly as production
// `Name::from_string` folds them. No host-marshalled Name inputs.
// ════════════════════════════════════════════════════════════════════════════

fn nm1(a: &str) -> Name {
    fold_step(name_anon(), a)
}
fn nm2(a: &str, b: &str) -> Name {
    fold_step(fold_step(name_anon(), a), b)
}

/// Level params u, v.
fn nm_u() -> Name { nm1("u") }
fn nm_v() -> Name { nm1("v") }
/// The env constant.
fn nm_c() -> Name { nm1("c") }
/// The Lit-rule type names (B11).
fn nat_type_name() -> Name { nm1("Nat") }
fn str_type_name() -> Name { nm1("String") }
/// R11 — the is_def_eq_offset interned names (B11: per-call two-part
/// builds of the production names::NAT_ZERO / names::NAT_SUCC).
fn nat_zero_name() -> Name { nm2("Nat", "zero") }
fn nat_succ_name() -> Name { nm2("Nat", "succ") }
/// R11 — the lazy-delta env constant names.
fn nm_gg() -> Name { nm1("gg") }
fn nm_ff() -> Name { nm1("ff") }
fn nm_e1() -> Name { nm1("e1") }
fn nm_e2() -> Name { nm1("e2") }
fn nm_opq1() -> Name { nm1("opq1") }
fn nm_opq2() -> Name { nm1("opq2") }
fn nm_fap() -> Name { nm1("fap") }
fn nm_fdep() -> Name { nm1("fdep") }
fn nm_ax1() -> Name { nm1("ax1") }
fn nm_ax2() -> Name { nm1("ax2") }
fn nm_fa1() -> Name { nm1("fa1") }
fn nm_fa2() -> Name { nm1("fa2") }
fn nm_pax() -> Name { nm1("pax") }
fn nm_thm1() -> Name { nm1("thm1") }
fn nm_thm2() -> Name { nm1("thm2") }
fn nm_lp() -> Name { nm1("lp") }
fn nm_mk() -> Name { nm1("mk") }
fn nm_fmk1() -> Name { nm1("fmk1") }
fn nm_fmk2() -> Name { nm1("fmk2") }
fn nm_sname() -> Name { nm1("S") }

// ════════════════════════════════════════════════════════════════════════════
// IN-MODULE SCENARIOS — the landed T1 case set (same universe coverage, same
// gate paths), decl names now REAL dotted Names; + case 14 (§4 undef param
// inside Const LEVELS — the find_undef_level_param Const-levels loop, live)
// + case 15 (§2 dup on a decl name carrying a REAL Num component — "thm.42").
// RAW (non-simplifying) level constructors so normalize does the work.
// ════════════════════════════════════════════════════════════════════════════

fn bdm() -> BinderData {
    BinderData { info: 0, mult: 2 }
}
/// R10 — alpha-question binder data: production BinderInfo Implicit /
/// InstImplicit under the modeled u8 (the exact values are never read
/// semantically by def_eq — that IS the fact under test).
fn bd_i() -> BinderData {
    BinderData { info: 1, mult: 2 }
}
fn bd_s() -> BinderData {
    BinderData { info: 3, mult: 2 }
}
fn pu() -> Level { Level::Param(nm_u()) }
fn pv() -> Level { Level::Param(nm_v()) }
fn rmax(a: Level, b: Level) -> Level { Level::Max(level_arc(a), level_arc(b)) }
fn rimax(a: Level, b: Level) -> Level { Level::IMax(level_arc(a), level_arc(b)) }
fn rsucc(a: Level) -> Level { Level::Succ(level_arc(a)) }

fn params0() -> Vec<Name> { Vec::new() }
fn params1(a: Name) -> Vec<Name> {
    let mut p: Vec<Name> = Vec::new();
    p.push(a);
    p
}
fn params2(a: Name, b: Name) -> Vec<Name> {
    let mut p: Vec<Name> = Vec::new();
    p.push(a);
    p.push(b);
    p
}
fn params3(a: Name, b: Name, c: Name) -> Vec<Name> {
    let mut p: Vec<Name> = Vec::new();
    p.push(a);
    p.push(b);
    p.push(c);
    p
}

/// EnvEntry builder (B1' — the ConstantInfo field shape).
fn ee(
    name: Name,
    level_params: Vec<Name>,
    type_: Expr,
    value: Option<Expr>,
    reducibility: Reducibility,
    kind: ConstantKind,
) -> EnvEntry {
    EnvEntry { name, level_params, type_, value, reducibility, kind }
}

/// The modeled environment (B1'), now ConstantInfo-shaped. The R10 entry
/// `c` keeps its R10 semantics (Definition, Regular height 1; its stored
/// type_ IS the R10 inferred-type-of-value Π(_:Sort 0). Sort 0 — verdicts
/// on cases 0..22 unchanged). New entries drive the lazy-delta scenarios:
///   gg := Sort 0                    Regular(1)  Definition   (case 24/26 base)
///   ff := Const gg                  Regular(2)  Definition   (height chain)
///   e1/e2 := Sort 0                 Regular(3)  Definition   (equal hints)
///   opq1/opq2 := Sort 0 (hidden)    Opaque      Opaque       (case 23 lever)
///   fap := λ(y:Sort 1). Sort 0      Regular(1)  Definition   (args-only)
///   fdep := λ(y:Sort 1). y          Regular(1)  Definition   (args-only FALSE)
///   ax1/ax2 : Sort 1, NO value      Regular(0)  Axiom        (delta exhaust)
///   fa1/fa2 := Const ax1/ax2        Regular(1)  Definition   (case 27)
///   pax : Sort 0, NO value          Regular(0)  Axiom        (a Prop)
///   thm1/thm2 : pax, value Sort 0   Opaque      Theorem      (#3305 probe)
///   lp := Sort 0, level_params [u]  Regular(1)  Definition   (#1277 probe)
///   fmk1 := App(mk, Sort 0)         Regular(1)  Definition   (proj probes)
///   fmk2 := App(mk, (λz.z) Sort 0)  Regular(1)  Definition   (proj probes)
/// (`mk` itself lives in the CTOR table only — its head is env-stuck.)
pub fn build_env() -> Vec<EnvEntry> {
    let sort1 = Expr::sort(rsucc(Level::Zero));
    let mut env: Vec<EnvEntry> = Vec::new();
    env.push(ee(
        nm_c(),
        params0(),
        Expr::pi(bdm(), Expr::sort0(), Expr::sort0()),
        Some(Expr::lam(bdm(), Expr::sort0(), Expr::bvar(0))),
        Reducibility::Regular(1),
        ConstantKind::Definition,
    ));
    env.push(ee(nm_gg(), params0(), sort1.clone(), Some(Expr::sort0()),
        Reducibility::Regular(1), ConstantKind::Definition));
    env.push(ee(nm_ff(), params0(), sort1.clone(), Some(Expr::cnst(nm_gg())),
        Reducibility::Regular(2), ConstantKind::Definition));
    env.push(ee(nm_e1(), params0(), sort1.clone(), Some(Expr::sort0()),
        Reducibility::Regular(3), ConstantKind::Definition));
    env.push(ee(nm_e2(), params0(), sort1.clone(), Some(Expr::sort0()),
        Reducibility::Regular(3), ConstantKind::Definition));
    env.push(ee(nm_opq1(), params0(), sort1.clone(), Some(Expr::sort0()),
        Reducibility::Opaque, ConstantKind::Opaque));
    env.push(ee(nm_opq2(), params0(), sort1.clone(), Some(Expr::sort0()),
        Reducibility::Opaque, ConstantKind::Opaque));
    env.push(ee(
        nm_fap(),
        params0(),
        Expr::pi(bdm(), sort1.clone(), sort1.clone()),
        Some(Expr::lam(bdm(), sort1.clone(), Expr::sort0())),
        Reducibility::Regular(1),
        ConstantKind::Definition,
    ));
    env.push(ee(
        nm_fdep(),
        params0(),
        Expr::pi(bdm(), sort1.clone(), sort1.clone()),
        Some(Expr::lam(bdm(), sort1.clone(), Expr::bvar(0))),
        Reducibility::Regular(1),
        ConstantKind::Definition,
    ));
    env.push(ee(nm_ax1(), params0(), sort1.clone(), None,
        Reducibility::Regular(0), ConstantKind::Axiom));
    env.push(ee(nm_ax2(), params0(), sort1.clone(), None,
        Reducibility::Regular(0), ConstantKind::Axiom));
    env.push(ee(nm_fa1(), params0(), sort1.clone(), Some(Expr::cnst(nm_ax1())),
        Reducibility::Regular(1), ConstantKind::Definition));
    env.push(ee(nm_fa2(), params0(), sort1.clone(), Some(Expr::cnst(nm_ax2())),
        Reducibility::Regular(1), ConstantKind::Definition));
    env.push(ee(nm_pax(), params0(), Expr::sort0(), None,
        Reducibility::Regular(0), ConstantKind::Axiom));
    env.push(ee(nm_thm1(), params0(), Expr::cnst(nm_pax()), Some(Expr::sort0()),
        Reducibility::Opaque, ConstantKind::Theorem));
    env.push(ee(nm_thm2(), params0(), Expr::cnst(nm_pax()), Some(Expr::sort0()),
        Reducibility::Opaque, ConstantKind::Theorem));
    env.push(ee(nm_lp(), params1(nm_u()), sort1.clone(), Some(Expr::sort0()),
        Reducibility::Regular(1), ConstantKind::Definition));
    env.push(ee(
        nm_fmk1(),
        params0(),
        sort1.clone(),
        Some(Expr::app(Expr::cnst(nm_mk()), Expr::sort0())),
        Reducibility::Regular(1),
        ConstantKind::Definition,
    ));
    env.push(ee(
        nm_fmk2(),
        params0(),
        sort1.clone(),
        Some(Expr::app(
            Expr::cnst(nm_mk()),
            Expr::app(Expr::lam(bdm(), sort1.clone(), Expr::bvar(0)), Expr::sort0()),
        )),
        Reducibility::Regular(1),
        ConstantKind::Definition,
    ));
    env
}

/// The POISONED env (probe p1 — NOT a transcription): identical except
/// ff's VALUE is Sort 1 instead of Const gg — the lazy-delta unfold of ff
/// now lands on a Sort that quick-DefDiffs against gg's Sort 0 unfold.
pub fn build_env_poisoned() -> Vec<EnvEntry> {
    let mut env = build_env();
    let mut i: usize = 0;
    while i < env.len() {
        if name_eq(&env[i].name, &nm_ff()) {
            env[i].value = Some(Expr::sort(rsucc(Level::Zero)));
        }
        i += 1;
    }
    env
}

/// The probe ctor table: mk is a structure constructor with 0 params.
pub fn build_ctors() -> Vec<(Name, u32)> {
    let mut c: Vec<(Name, u32)> = Vec::new();
    c.push((nm_mk(), 0));
    c
}

/// The Prop tower: T0 = ∀(α:Sort0). α → α : Sort(imax(1, imax(0,0))) = Sort 0.
fn prop_ty() -> Expr {
    Expr::pi(bdm(), Expr::sort0(), Expr::pi(bdm(), Expr::bvar(0), Expr::bvar(1)))
}
fn prop_proof() -> Expr {
    Expr::lam(bdm(), Expr::sort0(), Expr::lam(bdm(), Expr::bvar(0), Expr::bvar(0)))
}
/// The polymorphic tower: Tu = ∀(α:Sort u). α → α : Sort(IMax(succ u, u)) — a
/// REAL IMax produced by inference.
fn poly_ty() -> Expr {
    Expr::pi(bdm(), Expr::sort(pu()), Expr::pi(bdm(), Expr::bvar(0), Expr::bvar(1)))
}
fn poly_proof() -> Expr {
    Expr::lam(bdm(), Expr::sort(pu()), Expr::lam(bdm(), Expr::bvar(0), Expr::bvar(0)))
}
/// Pi with body at Succ level: ∀(α:Sort u). ∀(x:α). Sort v — drives
/// imax(_,Succ..)=Max then flatten/sort/DEDUP-SAME-BASE in §7.
fn maxy_val() -> Expr {
    Expr::pi(
        bdm(),
        Expr::sort(pu()),
        Expr::pi(bdm(), Expr::bvar(0), Expr::sort(pv())),
    )
}

/// The 28 in-module declarations: the R10 23-case set UNCHANGED (0..22) +
/// the five R11 lazy-delta cases. AWARE (production-phase) ACCEPTs: 0, 4,
/// 6, 7, 11, 12, 16, 17, 18, 19, 20, 21, 22 (the R10 pattern) + 24(hint
/// order), 25(args-only), 26(equal-hint both-unfold) = 16. REJECTs: 1(§6),
/// 2(§4), 3(§2), 5(§6 IMax), 8(§7), 9(§5), 10(§3), 13(§4 value), 14(§4
/// Const-levels), 15(§2 Num-name) + 23(OPAQUE hint gate) + 27(delta
/// exhaust) = 12. The R10-CONFIG control (eager-whnf def_eq) ACCEPTS case
/// 23 (its whnf blasts through the Opaque values) and agrees everywhere
/// else — the R11 divergence set is EXACTLY {23}.
pub fn build_decl_case(case: u64) -> Declaration {
    if case == 0 {
        // ACCEPT: poly axiom at Sort(max u v) — §5 over a Max level.
        return Declaration::Axiom {
            name: nm2("ax", "polymax"),
            level_params: params2(nm_u(), nm_v()),
            type_: Arc::new(Expr::sort(rmax(pu(), pv()))),
        };
    }
    if case == 1 {
        // REJECT §6: theorem at Sort(max u v) — sort = Succ(Max(u,v)), not Prop.
        return Declaration::Theorem {
            name: nm2("thm", "polymax"),
            level_params: params2(nm_u(), nm_v()),
            type_: Arc::new(Expr::sort(rmax(pu(), pv()))),
            value: Arc::new(Expr::sort0()),
        };
    }
    if case == 2 {
        // REJECT §4: params {u} but the type mentions v NESTED in Max(u, IMax(v,u)).
        return Declaration::Axiom {
            name: nm2("ax", "nested"),
            level_params: params1(nm_u()),
            type_: Arc::new(Expr::sort(rmax(pu(), rimax(pv(), pu())))),
        };
    }
    if case == 3 {
        // REJECT §2: duplicate level param u — detected by REAL name_eq.
        return Declaration::Axiom {
            name: nm2("ax", "dup"),
            level_params: params3(nm_u(), nm_v(), nm_u()),
            type_: Arc::new(Expr::sort(rmax(pu(), pv()))),
        };
    }
    if case == 4 {
        // ACCEPT (theorem): the imax(_,0)=0 EDGE — T0 : Sort 0, §7 def_eq towers.
        return Declaration::Theorem {
            name: nm2("thm", "prop"),
            level_params: params0(),
            type_: Arc::new(prop_ty()),
            value: Arc::new(prop_proof()),
        };
    }
    if case == 5 {
        // REJECT §6 (REAL IMax): Tu's sort is IMax(succ u, u) — not zero.
        return Declaration::Theorem {
            name: nm2("thm", "poly"),
            level_params: params1(nm_u()),
            type_: Arc::new(poly_ty()),
            value: Arc::new(poly_proof()),
        };
    }
    if case == 6 {
        // ACCEPT §7 Max COMMUTATIVITY: Sort(succ(max v u)) := Sort(max u v).
        return Declaration::Definition {
            name: nm2("def", "commute"),
            level_params: params2(nm_u(), nm_v()),
            type_: Arc::new(Expr::sort(rsucc(rmax(pv(), pu())))),
            value: Arc::new(Expr::sort(rmax(pu(), pv()))),
            is_reducible: false,
        };
    }
    if case == 7 {
        // ACCEPT §7 DEDUP-SAME-BASE: Max(succ u, Max(u, succ v)) -> Max(succ u, succ v).
        return Declaration::Definition {
            name: nm2("def", "dedup"),
            level_params: params2(nm_u(), nm_v()),
            type_: Arc::new(Expr::sort(rmax(rsucc(pu()), rsucc(pv())))),
            value: Arc::new(maxy_val()),
            is_reducible: false,
        };
    }
    if case == 8 {
        // REJECT §7 WRONG UNIVERSE: Sort(max u v) := Sort(max v u) — inferred
        // succ(max) != max; TypeMismatch payload deep-compared by the harness.
        return Declaration::Definition {
            name: nm2("def", "wrong"),
            level_params: params2(nm_u(), nm_v()),
            type_: Arc::new(Expr::sort(rmax(pu(), pv()))),
            value: Arc::new(Expr::sort(rmax(pv(), pu()))),
            is_reducible: false,
        };
    }
    if case == 9 {
        // REJECT §5: declared type is not a type (Nat literal) — the
        // ExpectedSort payload carries the JIT-built Const("Nat") (B11 name).
        return Declaration::Axiom {
            name: nm2("ax", "notatype"),
            level_params: params0(),
            type_: Arc::new(Expr::nat(7)),
        };
    }
    if case == 10 {
        // REJECT §3: type contains an FVar (meta quick-bit path).
        return Declaration::Axiom {
            name: nm2("ax", "fvar"),
            level_params: params0(),
            type_: Arc::new(Expr::from_kind(ExprKind::FVar(FVarId(5)))),
        };
    }
    if case == 11 {
        // ACCEPT: Opaque (value-bearing, non-theorem) at a poly type.
        return Declaration::Opaque {
            name: nm2("opq", "poly"),
            level_params: params1(nm_u()),
            type_: Arc::new(Expr::sort(rsucc(pu()))),
            value: Arc::new(Expr::sort(pu())),
        };
    }
    if case == 12 {
        // ACCEPT: type is a Const — env unfold (name_eq HIT) + infer_sort's
        // Pi-recursion arm.
        return Declaration::Axiom {
            name: nm2("ax", "constty"),
            level_params: params0(),
            type_: Arc::new(Expr::cnst(nm_c())),
        };
    }
    if case == 13 {
        // REJECT §4 in the VALUE: value mentions u, params only {v}.
        return Declaration::Definition {
            name: nm2("def", "valundef"),
            level_params: params1(nm_v()),
            type_: Arc::new(Expr::sort(rsucc(pv()))),
            value: Arc::new(Expr::sort(pu())),
            is_reducible: false,
        };
    }
    if case == 14 {
        // REJECT §4 inside Const LEVELS: type = Const(c, [IMax(v, u)]) with
        // params {u} — the undef param v is found by the Const-levels index
        // loop of find_undef_level_param (LIVE here; the landed T1 cases only
        // walked Sort-level trees). Also gives the FIXED Const meta arm a
        // non-empty levels_hash in the type-probe comparison.
        let mut levels: Vec<Level> = Vec::new();
        levels.push(rimax(pv(), pu()));
        return Declaration::Axiom {
            name: nm2("ax", "constlvls"),
            level_params: params1(nm_u()),
            type_: Arc::new(Expr::const_(nm_c(), levels)),
        };
    }
    if case == 15 {
        // REJECT §2 with a decl name carrying a REAL Num component — "thm.42"
        // = Str("thm") -> Num(42) (parse_u64_ascii success path +
        // name_num_part LIVE). Duplicate param u.
        return Declaration::Theorem {
            name: nm2("thm", "42"),
            level_params: params2(nm_u(), nm_u()),
            type_: Arc::new(Expr::sort0()),
            value: Arc::new(Expr::sort0()),
        };
    }
    if case == 16 {
        // R8 NEW — ACCEPT (THE ZETA/LET FVAR PATH): value =
        //   let x : Sort 1 := Sort 0 in (λ (y : x). y)
        // §7's Let arm runs ctx_push_let (a VALUE-BEARING LocalDecl with the
        // REAL in-module name "x"), opens the let body with FVar(x̂), infers
        // the inner λ whose DOMAIN IS THAT FVAR (its sort = the context
        // lookup: Sort 1), closes it back to Pi(FVar(x̂), FVar(x̂)) via
        // abstract_fvar (a no-op close over the foreign FVar), and
        // ZETA-substitutes subst_fvar(x̂ → Sort 0) INSIDE the rebuilt Pi —
        // the declared type Pi(Sort 0, Sort 0) matches IFF the substitution
        // really ran on the machine-code path.
        return Declaration::Definition {
            name: nm2("def", "zeta"),
            level_params: params0(),
            type_: Arc::new(Expr::pi(bdm(), Expr::sort0(), Expr::sort0())),
            value: Arc::new(Expr::lett(
                nm1("x"),
                Expr::sort(rsucc(Level::Zero)),
                Expr::sort0(),
                Expr::lam(bdm(), Expr::bvar(0), Expr::bvar(0)),
                false,
            )),
            is_reducible: false,
        };
    }
    if case == 17 {
        // R8 — ACCEPT (THE SHADOWING CASE): value = λ (α : Sort u).
        // λ (α : Sort v). α-OUTER (de Bruijn Lam(Su, Lam(Sv, BVar(1)))).
        // Production opens BOTH binders with Name::anon() — literally the
        // same binder name — so ONLY FVarId freshness separates them;
        // inferring the opened body FVar(α̂-outer) must scan PAST the
        // innermost context decl to find Sort u.
        return Declaration::Definition {
            name: nm2("def", "shadow"),
            level_params: params2(nm_u(), nm_v()),
            type_: Arc::new(Expr::pi(
                bdm(),
                Expr::sort(pu()),
                Expr::pi(bdm(), Expr::sort(pv()), Expr::sort(pu())),
            )),
            value: Arc::new(Expr::lam(
                bdm(),
                Expr::sort(pu()),
                Expr::lam(bdm(), Expr::sort(pv()), Expr::bvar(1)),
            )),
            is_reducible: false,
        };
    }
    if case == 18 {
        // R9 NEW — ACCEPT IFF whnf's FVar-ZETA ARM CONSULTS THE CONTEXT
        // INSIDE §7's def_eq:
        //   value = let T : Sort 1 := Sort 0 in
        //           ((λ (g : Π(_:T). Sort 1). g) (λ (x : Sort 0). Sort 0))
        //   type  = Π(_:Sort 0). Sort 1
        // §7 opens the let with a VALUE-BEARING decl T̂ ↦ Sort 0, then the
        // App-arm def_eq compares the argument's inferred type
        // Π(_:Sort 0).Sort 1 against the expected Π(_:T̂).Sort 1: the Pi
        // congruence descends to Sort 0 =?= T̂, decided ONLY by whnf
        // zeta-substituting T̂'s context value (tc/whnf.rs:455-461). The
        // context-blind pillar leaves T̂ stuck ⇒ TypeMismatch ⇒ REJECT.
        // (The zeta subst_fvar then rewrites the App's result type
        // Π(_:T̂).Sort 1 to the declared Π(_:Sort 0).Sort 1.)
        return Declaration::Definition {
            name: nm2("def", "zeta2"),
            level_params: params0(),
            type_: Arc::new(Expr::pi(
                bdm(),
                Expr::sort0(),
                Expr::sort(rsucc(Level::Zero)),
            )),
            value: Arc::new(Expr::lett(
                nm1("T"),
                Expr::sort(rsucc(Level::Zero)),
                Expr::sort0(),
                Expr::app(
                    Expr::lam(
                        bdm(),
                        Expr::pi(bdm(), Expr::bvar(0), Expr::sort(rsucc(Level::Zero))),
                        Expr::bvar(0),
                    ),
                    Expr::lam(bdm(), Expr::sort0(), Expr::sort0()),
                ),
                false,
            )),
            is_reducible: false,
        };
    }
    if case == 19 {
        return build_decl_case_19();
    }
    if case == 20 {
        // R10 NEW — "def.birrel": ACCEPT IFF equality-under-a-binder is
        // decided by PROOF IRRELEVANCE OVER THE OPENED DOMAIN.
        //   value = λ(P:Sort 0). λ(C:Π(_:P).Sort 1). λ(hp:P).
        //           ((λ (f : Π(h:P). Π(_:C hp). Sort 1). Sort 0)
        //            (λ (h:P). λ (u:C h). Sort 0))
        //   type  = Π(P:Sort 0). Π(C:Π(_:P).Sort 1). Π(hp:P). Sort 1
        // The App-arm def_eq compares the argument's inferred type
        // Π(h:P̂).Π(u:Ĉ #0).Sort 1 against the expected Π(h:P̂).Π(_:Ĉ ĥp̂).
        // Sort 1: is_def_eq_binding opens ĥ:P̂ (ONE shared id), telescopes,
        // and the iter-2 domain compare Ĉ ĥ =?= Ĉ ĥp̂ descends to
        // ĥ =?= ĥp̂ — equal ONLY by proof irrelevance with ĥ TYPED BY THE
        // CONTEXT ENTRY BINDING PUSHED. The R9-landed raw congruence faces
        // #0 =?= ĥp̂ (untypeable loose BVar) ⇒ REJECT.
        let sort1 = Expr::sort(rsucc(Level::Zero));
        let f_dom = Expr::pi(
            bdm(),
            Expr::bvar(2),
            Expr::pi(bdm(), Expr::app(Expr::bvar(2), Expr::bvar(1)), sort1.clone()),
        );
        let arg = Expr::lam(
            bdm(),
            Expr::bvar(2),
            Expr::lam(bdm(), Expr::app(Expr::bvar(2), Expr::bvar(0)), Expr::sort0()),
        );
        return Declaration::Definition {
            name: nm2("def", "birrel"),
            level_params: params0(),
            type_: Arc::new(Expr::pi(
                bdm(),
                Expr::sort0(),
                Expr::pi(
                    bdm(),
                    Expr::pi(bdm(), Expr::bvar(0), sort1.clone()),
                    Expr::pi(bdm(), Expr::bvar(1), sort1.clone()),
                ),
            )),
            value: Arc::new(Expr::lam(
                bdm(),
                Expr::sort0(),
                Expr::lam(
                    bdm(),
                    Expr::pi(bdm(), Expr::bvar(0), sort1.clone()),
                    Expr::lam(
                        bdm(),
                        Expr::bvar(1),
                        Expr::app(Expr::lam(bdm(), f_dom, Expr::sort0()), arg),
                    ),
                ),
            )),
            is_reducible: false,
        };
    }
    if case == 21 {
        // R10 NEW — "def.bzeta": ACCEPT IFF the let pushed OUTSIDE
        // zeta-composes with the binder opened INSIDE by binding.
        //   value = λ(P:Sort 0). λ(C:Π(_:P).Sort 1). λ(hp:P).
        //           let T : Sort 0 := P in
        //           ((λ (f : Π(h:T). Π(_:C hp). Sort 1). Sort 0)
        //            (λ (h:T). λ (u:C h). Sort 0))
        //   type  = Π(P:Sort 0). Π(C:Π(_:P).Sort 1). Π(hp:P). Sort 1
        // §7's Let arm pushes T̂ ↦ P̂ (value-bearing) OUTSIDE; the App-arm
        // def_eq telescopes through binding, opening ĥ:T̂ INSIDE; the
        // proof-irrel consult types ĥ as T̂ and its Prop-ness AND the
        // ty-def_eq T̂ =?= P̂ are decided by whnf ZETA through the context.
        // The R9-landed raw congruence faces #0 =?= ĥp̂ again ⇒ REJECT.
        let sort1 = Expr::sort(rsucc(Level::Zero));
        let f_dom = Expr::pi(
            bdm(),
            Expr::bvar(0),
            Expr::pi(bdm(), Expr::app(Expr::bvar(3), Expr::bvar(2)), sort1.clone()),
        );
        let arg = Expr::lam(
            bdm(),
            Expr::bvar(0),
            Expr::lam(bdm(), Expr::app(Expr::bvar(3), Expr::bvar(0)), Expr::sort0()),
        );
        return Declaration::Definition {
            name: nm2("def", "bzeta"),
            level_params: params0(),
            type_: Arc::new(Expr::pi(
                bdm(),
                Expr::sort0(),
                Expr::pi(
                    bdm(),
                    Expr::pi(bdm(), Expr::bvar(0), sort1.clone()),
                    Expr::pi(bdm(), Expr::bvar(1), sort1.clone()),
                ),
            )),
            value: Arc::new(Expr::lam(
                bdm(),
                Expr::sort0(),
                Expr::lam(
                    bdm(),
                    Expr::pi(bdm(), Expr::bvar(0), sort1.clone()),
                    Expr::lam(
                        bdm(),
                        Expr::bvar(1),
                        Expr::lett(
                            nm1("T"),
                            Expr::sort0(),
                            Expr::bvar(2),
                            Expr::app(Expr::lam(bdm(), f_dom, Expr::sort0()), arg),
                            false,
                        ),
                    ),
                ),
            )),
            is_reducible: false,
        };
    }
    if case == 22 {
        // R10 — "def.alpha": binder ATTRS must not affect equality (clean's
        // Lam/Pi carry NO names — BinderData only; binding.rs ignores the
        // lhs bi and pushes bi2 with Name::anon()). UNCHANGED from R10.
        return Declaration::Definition {
            name: nm2("def", "alpha"),
            level_params: params0(),
            type_: Arc::new(Expr::pi(
                bd_i(),
                Expr::sort0(),
                Expr::pi(
                    bd_s(),
                    Expr::bvar(0),
                    Expr::app(
                        Expr::lam(bdm(), Expr::sort0(), Expr::bvar(0)),
                        Expr::bvar(1),
                    ),
                ),
            )),
            value: Arc::new(Expr::lam(
                bdm(),
                Expr::sort0(),
                Expr::lam(bdm(), Expr::bvar(0), Expr::bvar(0)),
            )),
            is_reducible: false,
        };
    }
    if case == 23 {
        // R11 NEW — "def.opq": THE HINT-GATED REJECT. §7's binding domain
        // compare is Const(opq2) =?= Const(opq1): two ConstantKind::Opaque
        // constants with IDENTICAL hidden values (Sort 0). Production
        // def_eq must NOT unfold them — get_delta_const's kind/reducibility
        // gates exclude both sides, the loop returns DefUnknown on iter 1,
        // and P3 (names differ) / P6 (Const arm) REJECT. The R10-config
        // control's eager whnf unfolds both to Sort 0 and ACCEPTS — the
        // round's divergence case (exactly {23}).
        let sort1 = Expr::sort(rsucc(Level::Zero));
        return Declaration::Definition {
            name: nm2("def", "opq"),
            level_params: params0(),
            type_: Arc::new(Expr::pi(bdm(), Expr::cnst(nm_opq1()), sort1.clone())),
            value: Arc::new(Expr::lam(bdm(), Expr::cnst(nm_opq2()), Expr::sort0())),
            is_reducible: false,
        };
    }
    if case == 24 {
        // R11 NEW — "def.hgt": HINT-ORDERED UNFOLDING. Domain compare
        // Const(gg) =?= Const(ff), gg Regular(1), ff Regular(2), ff := gg:
        // compare => Greater => the TALLER side (ff) unfolds FIRST — one
        // step to Const gg, then finish's syntactic t==s fires. ACCEPT in
        // both configs; the step-count order observable is probe p0.
        let sort1 = Expr::sort(rsucc(Level::Zero));
        return Declaration::Definition {
            name: nm2("def", "hgt"),
            level_params: params0(),
            type_: Arc::new(Expr::pi(bdm(), Expr::cnst(nm_ff()), sort1.clone())),
            value: Arc::new(Expr::lam(bdm(), Expr::cnst(nm_gg()), Expr::sort0())),
            is_reducible: false,
        };
    }
    if case == 25 {
        // R11 NEW — "def.args": SAME-HEAD ARGS-ONLY. Domain compare
        // App(fap, (λ(z:Sort 1). z) Sort 0) =?= App(fap, Sort 0): both
        // heads fap/Regular(1) => Ordering Equal => same name+Regular =>
        // is_def_eq_args_only — the arg pair decided by the recursive
        // def_eq's P1 beta => DefEqual. ACCEPT in both configs.
        let sort1 = Expr::sort(rsucc(Level::Zero));
        let redex = Expr::app(
            Expr::lam(bdm(), sort1.clone(), Expr::bvar(0)),
            Expr::sort0(),
        );
        return Declaration::Definition {
            name: nm2("def", "args"),
            level_params: params0(),
            type_: Arc::new(Expr::pi(
                bdm(),
                Expr::app(Expr::cnst(nm_fap()), Expr::sort0()),
                sort1.clone(),
            )),
            value: Arc::new(Expr::lam(
                bdm(),
                Expr::app(Expr::cnst(nm_fap()), redex),
                Expr::sort0(),
            )),
            is_reducible: false,
        };
    }
    if case == 26 {
        // R11 NEW — "def.eqh": HINT-EQUAL BOTH-UNFOLD. Domain compare
        // Const(e2) =?= Const(e1), both Regular(3), different names =>
        // Ordering::Equal, the same-name args block SKIPPED, BOTH sides
        // unfold in ONE step (t_changed && s_changed) => Sort 0 == Sort 0.
        // ACCEPT in both configs.
        let sort1 = Expr::sort(rsucc(Level::Zero));
        return Declaration::Definition {
            name: nm2("def", "eqh"),
            level_params: params0(),
            type_: Arc::new(Expr::pi(bdm(), Expr::cnst(nm_e1()), sort1.clone())),
            value: Arc::new(Expr::lam(bdm(), Expr::cnst(nm_e2()), Expr::sort0())),
            is_reducible: false,
        };
    }
    // case 27 (and the never-taken out-of-range guard) — R11 NEW —
    // "def.axstuck": DELTA EXHAUST. Domain compare Const(fa2) =?= Const(fa1)
    // (both Regular(1), := distinct AXIOMS ax2/ax1 with NO value): the
    // equal-hint arm unfolds both once; iteration 2 sees (None,None) —
    // axioms fail get_delta_const's value.is_some() — => DefUnknown =>
    // Err((Const ax2, Const ax1)) => P3 names differ => P5 no change => P6
    // Const arm false => REJECT, TypeMismatch pinning the ORIGINAL Pi pair.
    // BOTH configs reject (the control's eager whnf also sticks on the
    // value-less axioms) — agreement through the exhaust path.
    let sort1 = Expr::sort(rsucc(Level::Zero));
    Declaration::Definition {
        name: nm2("def", "axstuck"),
        level_params: params0(),
        type_: Arc::new(Expr::pi(bdm(), Expr::cnst(nm_fa1()), sort1.clone())),
        value: Arc::new(Expr::lam(bdm(), Expr::cnst(nm_fa2()), Expr::sort0())),
        is_reducible: false,
    }
}

/// case 19 — R9 — ACCEPT IFF PROOF IRRELEVANCE DECIDES §7's def_eq
/// (unchanged; split out so 20-22 can follow in build_decl_case):
    //   value = λ(P:Sort 0). λ(C:Π(_:P).Sort 0). λ(h1:P). λ(h2:P).
    //           λ(f:Π(_:C h2).Sort 0). λ(a:C h1). f a
    //   type  = the matching Π-telescope ending in Sort 0
    // Inferring `f a` compares the STUCK applications C ĥ1 =?= C ĥ2 (Ĉ is
    // a non-let FVar — whnf's stuck arm); App congruence descends to
    // ĥ1 =?= ĥ2, distinct FVars equal ONLY by proof irrelevance: their
    // types are BOTH the context lookup P̂ (proof_irrel.rs:147), and P̂'s
    // type is the context lookup Sort 0 ⇒ is_prop ⇒ Some(true). (R10 note:
    // the R10 binding-blind control ACCEPTS this case — it kept the R9
    // proof-irrel consult.)
fn build_decl_case_19() -> Declaration {
    Declaration::Definition {
        name: nm2("def", "irrel"),
        level_params: params0(),
        type_: Arc::new(Expr::pi(
            bdm(),
            Expr::sort0(),
            Expr::pi(
                bdm(),
                Expr::pi(bdm(), Expr::bvar(0), Expr::sort0()),
                Expr::pi(
                    bdm(),
                    Expr::bvar(1),
                    Expr::pi(
                        bdm(),
                        Expr::bvar(2),
                        Expr::pi(
                            bdm(),
                            Expr::pi(
                                bdm(),
                                Expr::app(Expr::bvar(2), Expr::bvar(0)),
                                Expr::sort0(),
                            ),
                            Expr::pi(
                                bdm(),
                                Expr::app(Expr::bvar(3), Expr::bvar(2)),
                                Expr::sort0(),
                            ),
                        ),
                    ),
                ),
            ),
        )),
        value: Arc::new(Expr::lam(
            bdm(),
            Expr::sort0(),
            Expr::lam(
                bdm(),
                Expr::pi(bdm(), Expr::bvar(0), Expr::sort0()),
                Expr::lam(
                    bdm(),
                    Expr::bvar(1),
                    Expr::lam(
                        bdm(),
                        Expr::bvar(2),
                        Expr::lam(
                            bdm(),
                            Expr::pi(
                                bdm(),
                                Expr::app(Expr::bvar(2), Expr::bvar(0)),
                                Expr::sort0(),
                            ),
                            Expr::lam(
                                bdm(),
                                Expr::app(Expr::bvar(3), Expr::bvar(2)),
                                Expr::app(Expr::bvar(1), Expr::bvar(0)),
                            ),
                        ),
                    ),
                ),
            ),
        )),
        is_reducible: false,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// MONO ROOT A (#[no_mangle]) — the LAZY-DELTA-AWARE gate (the production
// phase ordering) over in-module-built decls: case scalar in; the gate
// Result AND the built declared type (for the meta-bit-identity
// differential on JIT-constructed inputs) out through sret pointers. Same
// shape as the landed R8-R10 roots.
// ════════════════════════════════════════════════════════════════════════════

#[no_mangle]
pub extern "C" fn ld_gate_root(
    out_res: *mut Result<(), EnvError>,
    out_ty: *mut Expr,
    case: u64,
) {
    let env = build_env();
    let ctors: Vec<(Name, u32)> = Vec::new();
    let verifier = Verifier {
        env: &env,
        ctors: &ctors,
    };
    let decl = build_decl_case(case);
    let ty: Expr = match &decl {
        Declaration::Definition { type_, .. } => type_.as_ref().clone(),
        Declaration::Axiom { type_, .. } => type_.as_ref().clone(),
        Declaration::Theorem { type_, .. } => type_.as_ref().clone(),
        Declaration::Opaque { type_, .. } => type_.as_ref().clone(),
    };
    let res = verifier.check_decl_readonly(&decl);
    unsafe {
        std::ptr::write(out_ty, ty);
        std::ptr::write(out_res, res);
    }
}

// ════════════════════════════════════════════════════════════════════════════
// MONO ROOT B (#[no_mangle]) — the R10-CONFIG CONTROL gate (eager-whnf
// def_eq, binding-aware, context-aware) over the SAME 28 cases. Divergence
// contract: agrees with ld_gate_root everywhere EXCEPT case 23, which it
// ACCEPTS (its whnf unfolds the Opaque constants the production def_eq
// must leave stuck).
// ════════════════════════════════════════════════════════════════════════════

#[no_mangle]
pub extern "C" fn ld_blind_root(
    out_res: *mut Result<(), EnvError>,
    out_ty: *mut Expr,
    case: u64,
) {
    let env = build_env();
    let ctors: Vec<(Name, u32)> = Vec::new();
    let verifier = Verifier {
        env: &env,
        ctors: &ctors,
    };
    let decl = build_decl_case(case);
    let ty: Expr = match &decl {
        Declaration::Definition { type_, .. } => type_.as_ref().clone(),
        Declaration::Axiom { type_, .. } => type_.as_ref().clone(),
        Declaration::Theorem { type_, .. } => type_.as_ref().clone(),
        Declaration::Opaque { type_, .. } => type_.as_ref().clone(),
    };
    let res = verifier.check_decl_readonly_blind(&decl);
    unsafe {
        std::ptr::write(out_ty, ty);
        std::ptr::write(out_res, res);
    }
}

// ════════════════════════════════════════════════════════════════════════════
// MONO ROOT C (#[no_mangle]) — THE LAZY-DELTA PROBES. Built ONLY from the
// production pieces (the phase-engine def_eq, the lazy-delta loop + its
// direct entry, get_delta_const, whnf_core_no_delta, the P4/P5 proj
// machinery, quick_is_def_eq, is_def_eq_offset) plus the clearly-marked
// NON-transcription controls: the R10-config blind def_eq (p2/p6), the
// counting probe pair lazy_delta_reduction_probe/_swapped (p0), and the
// poisoned env (p1). Outputs: a Result<Expr, TypeError> (deep-compared
// native==JIT) + scalar observables in ProbeIds.
//   idx 0: HINT ORDER IS OBSERVABLE — ff(h2) vs gg(h1), ff := gg:
//          production order unfolds the TALLER ff first and closes in ONE
//          iteration; the SWAPPED control (hint comparison inverted)
//          unfolds gg first and needs THREE. Verdicts EQUAL (confluence),
//          iteration counters 1 vs 3 — bit0 normal Ok(true); bit1 normal
//          iters==1; bit2 swapped Ok(true); bit3 swapped iters==3; bit4
//          the real (hook-bearing) lazy_delta_reduction agrees Ok(true).
//          ids.id0/id1 = the two counters (native==JIT).
//   idx 1: POISONED-ENV-VALUE — def_eq(Const ff, Const gg): correct env
//          TRUE (bit0); poisoned env (ff := Sort 1) FALSE (bit1); the
//          poisoned direct loop returns Ok(false) via finish's
//          quick-Sort-DefDiff arm — DefDiff live (bit2). res = the aware
//          whnf of Const ff under the poisoned env (= Sort 1, deep-compared).
//   idx 2: THE OPAQUE/THEOREM DISCIPLINE — aware def_eq(opq1, opq2) FALSE
//          (bit0: hint-gated, values identical); def_eq(opq1, opq1) TRUE
//          (bit1: P0 syntactic — equal only by name); the R10-config blind
//          def_eq(opq1, opq2) TRUE (bit2: pair-level divergence in ONE
//          module); aware def_eq(thm1, thm2) TRUE via PROOF IRRELEVANCE
//          (bit3: theorems are Opaque-hinted — rescued by irrel, not
//          delta); the direct loop on (thm1, thm2) returns Err/DefUnknown
//          (bit4: #3305 — theorems NEVER delta-unfold); get_delta_const on
//          the arity-mismatched lp (declared [u], referenced []) is None
//          (bit5: #1277 live) and aware def_eq(lp, Sort 0) FALSE (bit6)
//          while the R10-config blind (no arity gate) TRUE (bit7).
//   idx 3: SAME-NAME ARGS PATHS — aware def_eq(App(fdep,S0), App(fdep,S1))
//          FALSE (bit0: args-only fails, both unfold, beta exposes the
//          Sort mismatch — DefDiff); aware def_eq(App(fap,S0), App(fap,S1))
//          TRUE (bit1: args-only fails but fap DROPS its argument — the
//          both-unfold step reconverges); aware def_eq(App(fap,redex),
//          App(fap,S0)) TRUE (bit2: args-only SUCCEEDS — DefEqual).
//   idx 4: THE PROJ PHASES — aware def_eq(Proj(S,0,Const fmk1), Const gg)
//          TRUE (bit0: the ASYMMETRIC try_unfold_proj_app arm — full-proj
//          whnf_core extracts Sort 0 while the other side delta-unfolds);
//          aware def_eq(Proj(S,0,fmk1), Proj(S,0,fmk2)) TRUE (bit1: P4
//          lazy_delta_proj_reduction — both unfold, (None,None), then the
//          reduce_proj_core extraction fallback + beta); aware
//          def_eq(Proj(S,0,fmk1), Sort 0) TRUE (bit2: P5 — cheap proj is
//          STUCK on the Const operand, the second FULL-proj whnf_core
//          moves, recursion closes).
//   idx 5: QUICK COMPLETION + OFFSET — MData asym strip TRUE (bit0), MData
//          sym (TAGS IGNORED — inners compared) TRUE (bit1), Lit equal
//          TRUE (bit2), Lit unequal Some(false) fast REJECT (bit3); the
//          direct loop: (Lit 2, Lit 2) Ok(true) via offset succ-peeling
//          (bit4), (Lit 0, Lit 0) Ok(true) via the zero arm (bit5),
//          (Lit 1, Lit 0) Err — offset None, hooks pass, (None,None)
//          DefUnknown (bit6).
//   idx 6: BINDING∘LAZY-DELTA COMPOSITION — aware def_eq on the case-24
//          Pi PAIR directly (binding opens, the domain compare runs the
//          loop) TRUE (bit0); the same pair under the poisoned env FALSE
//          (bit1); the R10-config blind agrees TRUE on the good pair
//          (bit2 — divergence is case 23's Opaque gate, not the loop).
// ════════════════════════════════════════════════════════════════════════════

/// Plain scalar observables out of each probe.
#[derive(Clone, Copy, Debug)]
pub struct ProbeIds {
    pub id0: u64,
    pub id1: u64,
    pub guard_trips: u64,
    pub flags: u64,
}

#[no_mangle]
pub extern "C" fn ld_probe_root(
    out_res: *mut Result<Expr, TypeError>,
    out_ids: *mut ProbeIds,
    idx: u64,
) {
    let env = build_env();
    let env_poisoned = build_env_poisoned();
    let ctors = build_ctors();
    let v = Verifier {
        env: &env,
        ctors: &ctors,
    };
    let vp = Verifier {
        env: &env_poisoned,
        ctors: &ctors,
    };
    let mut ids = ProbeIds {
        id0: u64::MAX,
        id1: u64::MAX,
        guard_trips: 0,
        flags: 0,
    };
    let res: Result<Expr, TypeError>;
    let sort1 = Expr::sort(rsucc(Level::Zero));
    if idx == 0 {
        // HINT ORDER: ff (Regular 2) vs gg (Regular 1).
        let mut ctx = LocalContext::new();
        let a = Expr::cnst(nm_ff());
        let b = Expr::cnst(nm_gg());
        let mut flags = 0u64;
        let mut iters_normal: u64 = 0;
        match v.lazy_delta_reduction_probe(&a, &b, &mut ctx, &mut iters_normal) {
            Ok(true) => flags |= 1,
            _ => {}
        }
        if iters_normal == 1 {
            flags |= 2;
        }
        let mut iters_swapped: u64 = 0;
        match v.lazy_delta_reduction_swapped(&a, &b, &mut ctx, &mut iters_swapped) {
            Ok(true) => flags |= 4,
            _ => {}
        }
        if iters_swapped == 3 {
            flags |= 8;
        }
        match v.lazy_delta_reduction(&a, &b, &mut ctx) {
            Ok(true) => flags |= 16,
            _ => {}
        }
        ids.id0 = iters_normal;
        ids.id1 = iters_swapped;
        ids.guard_trips = ctx.guard_trips;
        ids.flags = flags;
        res = Ok(a);
    } else if idx == 1 {
        // POISONED ENV VALUE.
        let mut ctx = LocalContext::new();
        let a = Expr::cnst(nm_ff());
        let b = Expr::cnst(nm_gg());
        let mut flags = 0u64;
        if v.is_def_eq(&a, &b, &mut ctx) {
            flags |= 1;
        }
        if !vp.is_def_eq(&a, &b, &mut ctx) {
            flags |= 2;
        }
        match vp.lazy_delta_reduction(&a, &b, &mut ctx) {
            Ok(false) => flags |= 4,
            _ => {}
        }
        ids.id0 = ctx.next_id;
        ids.guard_trips = ctx.guard_trips;
        ids.flags = flags;
        res = Ok(vp.whnf_impl(&a, &ctx));
    } else if idx == 2 {
        // OPAQUE / THEOREM / ARITY discipline.
        let mut ctx = LocalContext::new();
        let o1 = Expr::cnst(nm_opq1());
        let o2 = Expr::cnst(nm_opq2());
        let mut flags = 0u64;
        if !v.is_def_eq(&o1, &o2, &mut ctx) {
            flags |= 1;
        }
        if v.is_def_eq(&o1, &Expr::cnst(nm_opq1()), &mut ctx) {
            flags |= 2;
        }
        if v.is_def_eq_blind(&o1, &o2, &mut ctx) {
            flags |= 4;
        }
        let t1 = Expr::cnst(nm_thm1());
        let t2 = Expr::cnst(nm_thm2());
        if v.is_def_eq(&t1, &t2, &mut ctx) {
            flags |= 8;
        }
        match v.lazy_delta_reduction(&t1, &t2, &mut ctx) {
            Err(_) => flags |= 16,
            _ => {}
        }
        let lp = Expr::cnst(nm_lp());
        if v.get_delta_const(&lp).is_none() {
            flags |= 32;
        }
        if !v.is_def_eq(&lp, &Expr::sort0(), &mut ctx) {
            flags |= 64;
        }
        if v.is_def_eq_blind(&lp, &Expr::sort0(), &mut ctx) {
            flags |= 128;
        }
        ids.id0 = ctx.next_id;
        ids.guard_trips = ctx.guard_trips;
        ids.flags = flags;
        res = Ok(t1);
    } else if idx == 3 {
        // SAME-NAME ARGS PATHS.
        let mut ctx = LocalContext::new();
        let mut flags = 0u64;
        let dep_a = Expr::app(Expr::cnst(nm_fdep()), Expr::sort0());
        let dep_b = Expr::app(Expr::cnst(nm_fdep()), sort1.clone());
        if !v.is_def_eq(&dep_a, &dep_b, &mut ctx) {
            flags |= 1;
        }
        let drop_a = Expr::app(Expr::cnst(nm_fap()), Expr::sort0());
        let drop_b = Expr::app(Expr::cnst(nm_fap()), sort1.clone());
        if v.is_def_eq(&drop_a, &drop_b, &mut ctx) {
            flags |= 2;
        }
        let redex = Expr::app(
            Expr::lam(bdm(), sort1.clone(), Expr::bvar(0)),
            Expr::sort0(),
        );
        let args_a = Expr::app(Expr::cnst(nm_fap()), redex);
        let args_b = Expr::app(Expr::cnst(nm_fap()), Expr::sort0());
        if v.is_def_eq(&args_a, &args_b, &mut ctx) {
            flags |= 4;
        }
        ids.id0 = ctx.next_id;
        ids.guard_trips = ctx.guard_trips;
        ids.flags = flags;
        res = Ok(dep_a);
    } else if idx == 4 {
        // THE PROJ PHASES (ctors table live: mk / 0 params).
        let mut ctx = LocalContext::new();
        let mut flags = 0u64;
        let p1 = Expr::proj(nm_sname(), 0, Expr::cnst(nm_fmk1()));
        if v.is_def_eq(&p1, &Expr::cnst(nm_gg()), &mut ctx) {
            flags |= 1;
        }
        let p2 = Expr::proj(nm_sname(), 0, Expr::cnst(nm_fmk2()));
        if v.is_def_eq(&p1, &p2, &mut ctx) {
            flags |= 2;
        }
        if v.is_def_eq(&p1, &Expr::sort0(), &mut ctx) {
            flags |= 4;
        }
        ids.id0 = ctx.next_id;
        ids.guard_trips = ctx.guard_trips;
        ids.flags = flags;
        res = Ok(p1);
    } else if idx == 5 {
        // QUICK COMPLETION + OFFSET.
        let mut ctx = LocalContext::new();
        let mut flags = 0u64;
        if v.is_def_eq(&Expr::mdata(1, Expr::sort0()), &Expr::sort0(), &mut ctx) {
            flags |= 1;
        }
        if v.is_def_eq(
            &Expr::mdata(1, Expr::sort0()),
            &Expr::mdata(2, Expr::sort0()),
            &mut ctx,
        ) {
            flags |= 2;
        }
        if v.is_def_eq(&Expr::nat(7), &Expr::nat(7), &mut ctx) {
            flags |= 4;
        }
        if !v.is_def_eq(&Expr::nat(7), &Expr::nat(8), &mut ctx) {
            flags |= 8;
        }
        match v.lazy_delta_reduction(&Expr::nat(2), &Expr::nat(2), &mut ctx) {
            Ok(true) => flags |= 16,
            _ => {}
        }
        match v.lazy_delta_reduction(&Expr::nat(0), &Expr::nat(0), &mut ctx) {
            Ok(true) => flags |= 32,
            _ => {}
        }
        match v.lazy_delta_reduction(&Expr::nat(1), &Expr::nat(0), &mut ctx) {
            Err(_) => flags |= 64,
            _ => {}
        }
        ids.id0 = ctx.next_id;
        ids.guard_trips = ctx.guard_trips;
        ids.flags = flags;
        res = Ok(Expr::nat(2));
    } else {
        // idx 6: BINDING ∘ LAZY-DELTA COMPOSITION.
        let mut ctx = LocalContext::new();
        let mut flags = 0u64;
        let a = Expr::pi(bdm(), Expr::cnst(nm_gg()), sort1.clone());
        let b = Expr::pi(bdm(), Expr::cnst(nm_ff()), sort1.clone());
        if v.is_def_eq(&a, &b, &mut ctx) {
            flags |= 1;
        }
        if !vp.is_def_eq(&a, &b, &mut ctx) {
            flags |= 2;
        }
        if v.is_def_eq_blind(&a, &b, &mut ctx) {
            flags |= 4;
        }
        ids.id0 = ctx.next_id;
        ids.guard_trips = ctx.guard_trips;
        ids.flags = flags;
        res = Ok(a);
    }
    unsafe {
        std::ptr::write(out_ids, ids);
        std::ptr::write(out_res, res);
    }
}

// ── standalone smoke harness (native only; NOT part of any emitted root) ──

fn main() {
    let mut ok = true;

    // Aware gate: 16 accepts / 12 rejects over the 28 cases.
    let mut accepts = 0usize;
    let mut rejects = 0usize;
    let mut aware_verdicts: Vec<bool> = Vec::new();
    for case in 0u64..28 {
        let mut res_slot = std::mem::MaybeUninit::<Result<(), EnvError>>::uninit();
        let mut ty_slot = std::mem::MaybeUninit::<Expr>::uninit();
        let res = unsafe {
            ld_gate_root(res_slot.as_mut_ptr(), ty_slot.as_mut_ptr(), case);
            let _ty = ty_slot.assume_init();
            res_slot.assume_init()
        };
        match &res {
            Ok(()) => {
                accepts += 1;
                aware_verdicts.push(true);
                println!("aware case {case}: ACCEPT");
            }
            Err(e) => {
                rejects += 1;
                aware_verdicts.push(false);
                println!("aware case {case}: REJECT {e:?}");
            }
        }
    }
    println!("aware accepts={accepts} rejects={rejects}");
    ok = ok && accepts == 16 && rejects == 12;
    // The R10 verdict pattern must reproduce on 0..22.
    let r10_accepts = [0usize, 4, 6, 7, 11, 12, 16, 17, 18, 19, 20, 21, 22];
    for case in 0..23usize {
        if aware_verdicts[case] != r10_accepts.contains(&case) {
            println!("case {case}: R10 verdict NOT reproduced");
            ok = false;
        }
    }
    let r11_expect = [false, true, true, true, false];
    for case in 23..28usize {
        if aware_verdicts[case] != r11_expect[case - 23] {
            println!("case {case}: R11 verdict wrong");
            ok = false;
        }
    }

    // R10-config control gate: 17 accepts / 11 rejects; divergence EXACTLY {23}.
    let mut baccepts = 0usize;
    let mut brejects = 0usize;
    for case in 0u64..28 {
        let mut res_slot = std::mem::MaybeUninit::<Result<(), EnvError>>::uninit();
        let mut ty_slot = std::mem::MaybeUninit::<Expr>::uninit();
        let res = unsafe {
            ld_blind_root(res_slot.as_mut_ptr(), ty_slot.as_mut_ptr(), case);
            let _ty = ty_slot.assume_init();
            res_slot.assume_init()
        };
        let verdict = res.is_ok();
        if verdict {
            baccepts += 1;
        } else {
            brejects += 1;
        }
        let expect_diverge = case == 23;
        let diverged = verdict != aware_verdicts[case as usize];
        if diverged != expect_diverge {
            println!("blind case {case}: DIVERGENCE CONTRACT VIOLATED (diverged={diverged})");
            ok = false;
        }
    }
    println!("blind accepts={baccepts} rejects={brejects}");
    ok = ok && baccepts == 17 && brejects == 11;

    // Probes.
    for idx in 0u64..7 {
        let mut res_slot = std::mem::MaybeUninit::<Result<Expr, TypeError>>::uninit();
        let mut ids_slot = std::mem::MaybeUninit::<ProbeIds>::uninit();
        let (res, ids) = unsafe {
            ld_probe_root(res_slot.as_mut_ptr(), ids_slot.as_mut_ptr(), idx);
            (res_slot.assume_init(), ids_slot.assume_init())
        };
        println!(
            "probe {idx}: ids=({},{}) trips={} flags={} ok={}",
            ids.id0,
            ids.id1,
            ids.guard_trips,
            ids.flags,
            res.is_ok()
        );
        let good = match idx {
            0 => res.is_ok() && ids.flags == 31 && ids.id0 == 1 && ids.id1 == 3,
            1 => res.is_ok() && ids.flags == 7,
            2 => res.is_ok() && ids.flags == 255,
            3 => res.is_ok() && ids.flags == 7,
            4 => res.is_ok() && ids.flags == 7,
            5 => res.is_ok() && ids.flags == 127,
            _ => res.is_ok() && ids.flags == 7,
        };
        if !good {
            println!("probe {idx}: EXPECTATION FAILED");
        }
        ok = ok && good;
    }
    std::process::exit((!ok) as i32);
}
