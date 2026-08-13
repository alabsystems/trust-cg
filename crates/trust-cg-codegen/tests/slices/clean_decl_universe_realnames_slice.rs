// R6 — THE UNIVERSAL DECL GATE OVER REAL NAMES: the landed
// clean_decl_universe_slice.rs (T1 FLAGSHIP, verified native==JIT) with its
// Name(u32) B2 model REPLACED by the production `Name` (NameInner Anon/Str/Num,
// Arc parent chain, Arc<str> payload, construction-time `cached_hash` via the
// real murmur/mix chain) — the round-5 de-modeling pattern applied to the
// flagship: check_decl_readonly (all six steps §2..§7), infer_sort, check_type,
// and the FULL production Level {Zero,Succ,Max,IMax,Param} universe machinery,
// with Level::Param now carrying REAL Names through normalize/is_def_eq.
//
// WHAT CHANGED vs the landed clean_decl_universe_slice.rs (each at its site):
//   * `Name`/`NameInner` — VERBATIM the production declarations (name.rs:150-159,
//     233-239) + the production `Hash for Name` (name.rs:461-465: O(1), writes
//     cached_hash). Construction chain (`name_anon`/`name_str_part`/
//     `name_num_part`), `murmur_hash_64a_idx` [T-murmur-idx], `parse_u64_ascii`
//     [T-parse], `fold_step` (from_string_uncached's fold body), `str_bytes_eq`
//     + `name_eq` [T-eq-iter] — ALL VERBATIM the round-4/5 transcriptions
//     (harness-proved bit-identical to the real clean-kernel).
//   * EVERY Name comparison the gate performs is now the PRODUCTION `Name::eq`
//     (hash fast-path + full structural walk) via `name_eq`:
//       - §2 duplicate-level-param detection (check_decl_readonly),
//       - §4 level-param closure (`find_undef_level_param_in_level`'s
//         `allowed.contains` scan — Level::Param carries Names),
//       - env lookups (`unfold_const` / `get_constructor_num_params` slice-scan),
//       - def_eq/structural_eq Const-name and Proj-name arms,
//       - Level PartialEq's Param arm (the eq feeding max/imax/normalize/is_geq).
//   * `is_norm_lt`'s Param arm (`n1 < n2`, the normalize canonical sort) is the
//     PRODUCTION `Ord for Name` (name.rs:399-458, Lean cmp_core) transcribed as
//     `name_cmp_is_lt` [T-ord] — components root-to-leaf, Num-before-Str,
//     numeric / lexicographic (str::cmp == bytewise-then-length), shorter
//     prefix first. SmallVec<[_;8]> -> Vec<&Name> node stacks (each chain node
//     IS one component; pop order == root-to-leaf).
//   * THE DECLARED T1 NUANCE IS FIXED: `compute_meta`'s Const arm is now the
//     PRODUCTION arm (expr/kind.rs:567-581) — it mixes
//     `mix_hash(5, mix_hash(name_hash, levels_hash))` and derives
//     has_level_param / has_level_mvar from the levels (the landed T1 model
//     hashed only the name and pinned the flags false). `hash_levels`
//     transcribes `hash_to_u64(levels)`'s `<Vec<Level> as Hash>` sequence
//     (length prefix then per-element Level hash) as an explicit loop [B9].
//   * Decl names, level-param names (u, v), the env-const name and the
//     Lit-rule type names (Nat/String) are constructed IN-MODULE from literal
//     parts (`from_string_uncached` unrolled — [T-unroll]); the root takes only
//     a case scalar — no host-marshalled Name inputs at all. One decl name
//     ("thm.42") carries a REAL Num component, making `parse_u64_ascii`'s
//     success path + `name_num_part` LIVE in the gate module (they were
//     runtime-dead on round 5's all-Str harness names).
//
// MODELED BOUNDARIES that REMAIN (unchanged from the landed T1 slice except
// B2, which is CLOSED, and the Const-meta nuance, which is FIXED):
//   B1. env/cache: slice-scan over &[(Name, Option<Expr>)]; a const's TYPE is
//       the inferred type of its value; no hashbrown, no tc caches.
//   B3. binder opening: de-Bruijn Vec<Expr> local context (real tc opens with
//       FVars). Same boundary as the verified infer_type rung.
//   B4. stack_safe / heartbeats / caches / profiler / options / infer_only:
//       pass-throughs or resource-limit config, elided (as prior rungs).
//   B5. ExprKind is the 11-variant production core; SProp/Squash/Cubical*/ZFC*
//       arms structurally absent; infer_sort's SProp=>0 arm elided with them.
//   B6. Declaration carries Arc<Expr> for type_/value (real: Expr by value).
//   B7. ExprMeta payload hashes run through the KaniHasher model (clean's own
//       cfg(kani) hasher selection; production non-kani uses DefaultHasher/
//       SipHash13 — meta.rs:367-374). NOW the Name hash CONTENT flowing
//       through it is the real production cached_hash, and the Const arm
//       STRUCTURE is production-verbatim. Full de-modeling needs SipHash13.
//       <Arc<Level> as Hash> stays an extern leaf (child recursion completes
//       natively — the landed B7 convention).
//   B8. whnf iota/quot reduction leaves cut to None (verified separately).
//   B9. REWRITES (semantics-preserving, lowering-driven, documented inline):
//       sort_by -> stable insertion sort w/ identical is_norm_lt order;
//       contains/enumerate/any -> index loops with identical predicates;
//       map_err(..)? -> match; for _ in 0..n -> counter while; vec![..] ->
//       new+push; <[Level] as Hash> -> explicit length-prefix+element loop.
//   B10. delta-unfold ignores Const levels (env values universe-monomorphic
//       here; Const-level instantiation verified in the infer_ext rung).
//   B11. The Lit typing rule's type names are built per-call from literal
//       parts ("Nat"/"String") where production references interned constants
//       — value-identical Names (from_string == from_string_uncached,
//       name.rs:578; zero residual cache boundary — the round-5 finding).
//   Arc<str> crossings (Arc::<str>::from / deref / clone) and Arc<Name>/
//   Arc<Level>/Arc<Expr> clones lower to extern decls bound to FAITHFUL host
//   shims (the landed convention); Arc::new + Arc deref are INLINED (RUNG 5/6).
//   Drops are not emitted (leak model — every Name/Expr immortal).
//
// SOURCES (verbatim transcription targets in $HOME/clean/crates/clean-kernel/src):
//   name.rs             — NameInner (:150), Name (:233), Ord (:399 cmp_core),
//                         Hash (:461), anon/str/num+compute_hash (:339-364,
//                         483-527), from_string_uncached fold (:557-565).
//   env/native_reducers_string.rs — murmur_hash_64a (:357-393).
//   level/mod.rs        — Level enum (:81), PartialEq (cfg(kani) iterative,
//                         :142), Hash (production impl), zero/succ/max/imax
//                         (:259-359), is_zero/is_nonzero (:367-389), get_offset
//                         (:399), add_offset (:416), normalize (:433), kind_ord
//                         (:441), is_norm_lt (:459 kani-iterative; Param arm =
//                         Name Ord), push_max_args (:530), mk_max_from_args
//                         (:558), is_explicit (:577), normalize_impl (:593),
//                         normalize_max (:644), subsume_max_args (:727),
//                         dedup_max_args (:775), is_geq (:840), is_geq_core
//                         (:871 kani-iterative), is_geq_leaf (:920),
//                         has_params_impl (:1245).
//   expr/meta.rs        — ExprMeta bit-packing, mix_hash, KaniHasher,
//                         hash_to_u64, level_has_mvar.
//   expr/kind.rs        — compute_meta (:486; Const arm :567-581 now VERBATIM).
//   cert/reduction.rs   — whnf_impl (BETA/DELTA/ZETA/proj-iota; iota/quot cut).
//   cert/expr_eq.rs     — def_eq_impl (level_eq = Level::is_def_eq, :34).
//   tc/infer.rs         — infer_type_fast_inner rules (:735 infer_sort,
//                         :765 infer_sort_inner, :670 check_type).
//   env/decl_add.rs     — find_undef_level_param_in_level (:64),
//                         find_undef_level_param (:88), check_decl_readonly (:229).
//   env/types.rs        — Declaration (:338), EnvError (:388, reachable 6).
//
// Crate name is load-bearing (appears in the mangled extern-leaf symbols the
// JIT binds): it MUST stay `clean_decl_universe_realnames_slice`.
//
// REGEN (one module per root; trust-ir main >= 375c800 — NO frontend changes
// this round):
//   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//   cd $HOME/trust-ir/frontend
//   env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//     $S/bin/cargo run --bin trust_ir_mir -- \
//     ../../trust-cg/crates/trust-cg-codegen/tests/slices/clean_decl_universe_realnames_slice.rs \
//     --crate-type=lib --mir-emit-closure <root> <out.tir>
//   roots: decl_gate_realnames_root | declnames_probe_root

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

// ── Modeled environment (B1): slice-scan. Layout identical to the verified
// whnf/def_eq/infer/decl rungs (2 fat-pointer fields, 4 words). ──
pub struct Verifier<'env> {
    pub env: &'env [(Name, Option<Expr>)],
    pub ctors: &'env [(Name, u32)],
}

// ── The slice TypeError (tc/infer.rs TypeError, reachable subset in source
// shape; carries the offending Expr/Name directly — no format!/String). ──
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

impl<'env> Verifier<'env> {
    // Env lookups: the entry-name equality is the PRODUCTION name_eq (the
    // slice-scan `entry.0 == *name` — B1 shape, real Name comparison).
    fn unfold_const(&self, name: &Name) -> Option<Expr> {
        let mut i: usize = 0;
        let n = self.env.len();
        while i < n {
            let entry = &self.env[i];
            if name_eq(&entry.0, name) { return entry.1.clone(); }
            i += 1;
        }
        None
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
    // Modeled env type lookup (B1): a const's TYPE is the inferred type of its
    // unfolding value (faithful for non-recursive defs). B10: no level-param
    // instantiation on the modeled env (env values universe-monomorphic here).
    fn const_type(&self, name: &Name) -> Option<Expr> {
        match self.unfold_const(name) {
            Some(val) => match self.infer_type(&val) {
                Ok(ty) => Some(ty),
                Err(_) => None,
            },
            None => None,
        }
    }
    fn try_iota_reduction(&self, _e: &Expr) -> Option<Expr> { None } // B8
    fn try_quot_reduction(&self, _e: &Expr) -> Option<Expr> { None } // B8

    // ── WHNF pillar (cert/reduction.rs whnf_impl) — VERBATIM, as verified. ──
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
        Expr::from_kind(ExprKind::Proj(struct_name.clone(), idx, Arc::new(expr_whnf)))
    }

    // ── DEF-EQ pillar (cert/expr_eq.rs) — VERBATIM; THE UNIVERSE INTEGRATION:
    // `level_eq` is the REAL `Level::is_def_eq` (cert/expr_eq.rs:34-36) — the
    // full Max/IMax normalization machinery. Const/Proj name equality is the
    // PRODUCTION name_eq. ──
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
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => name_eq(n1, n2) && self.level_vec_eq(ls1, ls2),
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => self.def_eq_impl(f1, f2) && self.def_eq_impl(a1, a2),
            (ExprKind::Lam(_b1, ty1, b1), ExprKind::Lam(_b2, ty2, b2))
            | (ExprKind::Pi(_b1, ty1, b1), ExprKind::Pi(_b2, ty2, b2)) => self.def_eq_impl(ty1, ty2) && self.def_eq_impl(b1, b2),
            (ExprKind::Let(_, ty1, v1, b1, _), ExprKind::Let(_, ty2, v2, b2, _)) => self.def_eq_impl(ty1, ty2) && self.def_eq_impl(v1, v2) && self.def_eq_impl(b1, b2),
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => name_eq(n1, n2) && i1 == i2 && self.def_eq_impl(e1, e2),
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

    // ── INFER-TYPE pillar (tc/infer.rs infer_type_fast_inner) — VERBATIM as
    // verified; the Sort/Pi rules construct FULL Levels (succ / imax). B3:
    // de-Bruijn Vec<Expr> local context. ──
    fn infer_type(&self, e: &Expr) -> Result<Expr, TypeError> {
        let mut ctx: Vec<Expr> = Vec::new();
        self.infer_type_core(e, &mut ctx)
    }

    fn infer_type_core(&self, e: &Expr, ctx: &mut Vec<Expr>) -> Result<Expr, TypeError> {
        match &e.kind {
            // Sort(l) : Sort(succ l) — the FULL Level succ.
            ExprKind::Sort(l) => Ok(Expr::sort(Level::succ(l.clone()))),

            ExprKind::BVar(idx) => {
                let depth = ctx.len();
                if (*idx as usize) >= depth {
                    return Err(TypeError::UnboundVariable(*idx));
                }
                let pos = depth - 1 - (*idx as usize);
                let raw = ctx[pos].clone();
                Ok(raw.lift_at(0, idx.saturating_add(1)))
            }

            ExprKind::Const(name, _levels) => match self.const_type(name) {
                Some(ty) => Ok(ty),
                None => Err(TypeError::UnknownConst(name.clone())),
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

            // Pi(A, B) : Sort(imax u v) — the FULL Level imax (Max/IMax smart
            // constructor, incl. the imax(_,0)=0 and imax(_,Succ..)=max collapses).
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
                Ok(body_type.instantiate(val))
            }

            // B11: the Lit type names are REAL Names built from literal parts
            // (production references interned Nat/String constants —
            // value-identical, zero residual cache boundary).
            ExprKind::Lit(lit) => Ok(match lit {
                Literal::Nat(_) => Expr::cnst(nat_type_name()),
                Literal::Str(_) => Expr::cnst(str_type_name()),
            }),

            ExprKind::MData(_, inner) => self.infer_type_core(inner, ctx),

            // Proj/FVar inference deferred here (verified separately in the
            // infer_ext rung) — the decl gate cases never reach them.
            _ => Err(TypeError::Unsupported),
        }
    }

    // ── §5: infer_sort (tc/infer.rs:735 / :765 infer_sort_inner) — VERBATIM
    // control flow. B3 ctx; B4 pass-throughs; B5: no SProp arm. The Pi arm's
    // Ok is the FULL Level::imax. ──
    const INFER_SORT_MAX_DEPTH: u32 = 64;

    fn infer_sort(&self, e: &Expr) -> Result<Level, TypeError> {
        let mut ctx: Vec<Expr> = Vec::new();
        self.infer_sort_inner(e, 0, &mut ctx)
    }

    fn infer_sort_inner(&self, e: &Expr, depth: u32, ctx: &mut Vec<Expr>) -> Result<Level, TypeError> {
        let ty = self.infer_type_core(e, ctx)?;
        let ty_whnf = self.whnf_impl(&ty);
        match &ty_whnf.kind {
            ExprKind::Sort(l) => Ok(l.clone()),
            ExprKind::Pi(_bd, arg_type, body) => {
                if depth >= Self::INFER_SORT_MAX_DEPTH {
                    // SOUNDNESS (tc/infer.rs:784): under-reporting a deep universe
                    // as Prop would defeat the theorem-is-Prop gate. Hard error.
                    return Err(TypeError::SortDepthExceeded { depth });
                }
                let arg_level = self.infer_sort_inner(arg_type, depth + 1, ctx)?;
                ctx.push(arg_type.as_ref().clone());
                let body_level_result = self.infer_sort_inner(body, depth + 1, ctx);
                ctx.pop();
                let body_level = body_level_result?;
                Ok(Level::imax(arg_level, body_level))
            }
            _ => Err(TypeError::ExpectedSort {
                ty: Arc::new(ty),
            }),
        }
    }

    // ── §7: check_type (tc/infer.rs:670) — VERBATIM minus infer_only/heartbeat
    // plumbing (B4). ──
    fn check_type(&self, e: &Expr, expected: &Expr) -> Result<(), TypeError> {
        let inferred = self.infer_type(e)?;
        if self.is_def_eq(&inferred, expected) {
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

        // (5) The type must be well-formed: infer_sort yields a Sort.
        let sort = match self.infer_sort(type_) {
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
            match self.check_type(value, type_) {
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

/// The modeled environment (B1): c := λ(_:Sort 0). #0, so Const(c)'s type is
/// Pi(Sort0, Sort0) — drives infer_sort's Pi-recursion arm through the env
/// unfold (case 12), and env MISSES exercise name_eq's hash fast-path
/// (Nat lookups in case 9).
pub fn build_env() -> Vec<(Name, Option<Expr>)> {
    let mut env: Vec<(Name, Option<Expr>)> = Vec::new();
    env.push((nm_c(), Some(Expr::lam(bdm(), Expr::sort0(), Expr::bvar(0)))));
    env
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

/// The 16 in-module declarations. ACCEPTs: 0, 4, 6, 7, 11, 12.
/// REJECTs: 1(§6), 2(§4), 3(§2), 5(§6 IMax), 8(§7), 9(§5), 10(§3), 13(§4
/// value), 14(§4 Const-levels), 15(§2 Num-name).
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
    // case 15 (and the never-taken out-of-range guard): REJECT §2 with a decl
    // name carrying a REAL Num component — "thm.42" = Str("thm") -> Num(42)
    // (parse_u64_ascii success path + name_num_part LIVE). Duplicate param u.
    Declaration::Theorem {
        name: nm2("thm", "42"),
        level_params: params2(nm_u(), nm_u()),
        type_: Arc::new(Expr::sort0()),
        value: Arc::new(Expr::sort0()),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// MONO ROOT A (#[no_mangle]) — the gate over in-module-built decls: case
// scalar in; the gate Result AND the built declared type (for the meta-bit-
// identity differential on JIT-constructed inputs) out through sret pointers.
// ════════════════════════════════════════════════════════════════════════════

#[no_mangle]
pub extern "C" fn decl_gate_realnames_root(
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
// MONO ROOT B (#[no_mangle]) — the NAME PROBE: returns (sret) one of the REAL
// Names the scenario construction produces, read OFF the built structures, so
// the harness can decode it raw and pin cached_hash BIT-IDENTICAL to the real
// clean-kernel goldens:
//   idx 0 ..= 15 : the decl name of build_decl_case(idx)
//   idx 16 / 17  : the level-param names u / v
//   idx 18       : the env-const name (read off build_env()'s first entry)
//   idx 19 / 20  : the Lit-rule type names Nat / String
//   idx 21+      : anon (never asked)
// ════════════════════════════════════════════════════════════════════════════

fn probe_pick(idx: u64) -> Name {
    if idx <= 15 {
        let d = build_decl_case(idx);
        return match &d {
            Declaration::Definition { name, .. } => name.clone(),
            Declaration::Axiom { name, .. } => name.clone(),
            Declaration::Theorem { name, .. } => name.clone(),
            Declaration::Opaque { name, .. } => name.clone(),
        };
    }
    if idx == 16 {
        return nm_u();
    }
    if idx == 17 {
        return nm_v();
    }
    if idx == 18 {
        let env = build_env();
        return env[0].0.clone();
    }
    if idx == 19 {
        return nat_type_name();
    }
    if idx == 20 {
        return str_type_name();
    }
    name_anon()
}

#[no_mangle]
pub extern "C" fn declnames_probe_root(out: *mut Name, idx: u64) {
    let name = probe_pick(idx);
    unsafe {
        std::ptr::write(out, name);
    }
}

// ── standalone smoke harness (native only; NOT part of either emitted root) ──

fn main() {
    let mut accepts = 0usize;
    let mut rejects = 0usize;
    for case in 0u64..16 {
        let mut res_slot = std::mem::MaybeUninit::<Result<(), EnvError>>::uninit();
        let mut ty_slot = std::mem::MaybeUninit::<Expr>::uninit();
        let res = unsafe {
            decl_gate_realnames_root(res_slot.as_mut_ptr(), ty_slot.as_mut_ptr(), case);
            let _ty = ty_slot.assume_init();
            res_slot.assume_init()
        };
        match &res {
            Ok(()) => {
                accepts += 1;
                println!("case {case}: ACCEPT");
            }
            Err(e) => {
                rejects += 1;
                println!("case {case}: REJECT {e:?}");
            }
        }
    }
    println!("accepts={accepts} rejects={rejects}");
    for idx in 0u64..21 {
        let mut slot = std::mem::MaybeUninit::<Name>::uninit();
        let n = unsafe {
            declnames_probe_root(slot.as_mut_ptr(), idx);
            slot.assume_init()
        };
        println!("probe {idx}: {:#018x}", n.cached_hash);
    }
    std::process::exit((accepts != 6 || rejects != 10) as i32);
}
