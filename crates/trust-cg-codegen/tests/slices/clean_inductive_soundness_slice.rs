// R17 — THE INDUCTIVE-SOUNDNESS GATE, re-composed on the full modern stack.
//
// The soundness-critical HEART of the kernel for inductive types — the three
// checks whose correctness IS the consistency of the logic — transcribed
// VERBATIM at their production positions and COMPOSED with the modern stack
// (real Names with murmur cached_hash + name_eq; the full production Level with
// Max/IMax + is_zero/is_nonzero; production compute_meta; the FVar LocalContext
// binder discipline threading whnf / def_eq / infer_type / infer_sort):
//
//   1. STRICT POSITIVITY          — inductive/mod.rs:409/451/490/661/698
//   2. LARGE-ELIM-FROM-PROP       — env/elim_analysis.rs:38 + tc/infer.rs:808
//   3. CTOR-RETURN (is_valid_ind_app, lean4#2125) — inductive/mod.rs:854/752/710
//
// The MACHINERY below (Name, Level, ExprMeta/compute_meta, Expr, LocalContext,
// Verifier: whnf / def_eq / infer_type / infer_sort / check_type) is the R6/R8
// modern stack, reused VERBATIM from the landed clean_fvar_opening_slice.rs
// (itself R6's real-Name / full-Level / production-meta stack + R8's FVar
// open->infer->close discipline). The THREE inductive checks + their scenarios
// + roots are appended at the bottom. See the appended R17 banner for the full
// per-check provenance and boundary ledger.
//
// Crate name is load-bearing (it appears in the mangled extern-leaf symbols the
// JIT binds): it MUST stay `clean_inductive_soundness_slice`.
//
// REGEN (one module per root; trust-ir main — NO frontend changes this round):
//   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//   cd $HOME/trust-ir/frontend
//   env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//     $S/bin/cargo run --bin trust_ir_mir -- \
//     ../../trust-cg/crates/trust-cg-codegen/tests/slices/clean_inductive_soundness_slice.rs \
//     --crate-type=lib --mir-emit-closure <root> <out.tir>
//   roots: positivity_root | ctor_return_root | elim_root
//
// Per-process under `perl -e 'alarm 600; exec @ARGV' -- <bin> --test-threads=1`.

#![allow(dead_code)]
#![allow(clippy::all)]
#![allow(unused_variables)]

#[allow(unused_imports)]
use std::convert::TryFrom;
use std::hash::{Hash, Hasher};
use std::sync::Arc; // pre-2021 prelude (the MIR driver's edition)

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
            let x_composite = matches!(x.get_offset().0, Level::Max(_, _) | Level::IMax(_, _));

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
pub enum Literal {
    Nat(u64),
    Str(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BinderData {
    pub info: u8,
    pub mult: u8,
}

// ════════════════════════════════════════════════════════════════════════════
// expr/meta.rs — KaniHasher (B7 payload-hasher model; the Name/Level content
// flowing through it is now the REAL production cached_hash chain) + the
// monomorphic per-type hashers.
// ════════════════════════════════════════════════════════════════════════════

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
fn level_has_mvar(_l: &Level) -> bool {
    false
}

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
pub struct Expr {
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
    // The O(1) metadata quick checks (expr/mod.rs:289-303) — VERBATIM.
    fn has_fvar_quick(&self) -> bool {
        self.meta.has_fvar()
    }
    fn has_expr_mvar_quick(&self) -> bool {
        self.meta.has_expr_mvar()
    }
    fn has_level_mvar_quick(&self) -> bool {
        self.meta.has_level_mvar()
    }
    fn bvar(idx: u32) -> Self {
        Expr::from_kind(ExprKind::BVar(idx))
    }
    fn cnst(name: Name) -> Self {
        Expr::from_kind(ExprKind::Const(name, Vec::new()))
    }
    fn const_(name: Name, levels: LevelVec) -> Self {
        Expr::from_kind(ExprKind::Const(name, levels))
    }
    fn sort0() -> Self {
        Expr::from_kind(ExprKind::Sort(Level::Zero))
    }
    fn sort(l: Level) -> Self {
        Expr::from_kind(ExprKind::Sort(l))
    }
    fn nat(n: u64) -> Self {
        Expr::from_kind(ExprKind::Lit(Literal::Nat(n)))
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
    fn mdata(tag: u32, e: Expr) -> Self {
        Expr::from_kind(ExprKind::MData(tag, Arc::new(e)))
    }

    // VERBATIM lift_at (verified substitution core).
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
    fn lift_from(&self, start: u32, amount: u32) -> Expr {
        self.lift_at(start, amount)
    }
    // VERBATIM instantiate / instantiate_at (the beta primitive). Name copies
    // are now real Name clones (Arc bumps) — the production text.
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
                name.clone(),
                ty.instantiate_at(val, depth),
                val_e.instantiate_at(val, depth),
                body.instantiate_at(val, depth.saturating_add(1)),
                *nondep,
            ),
            ExprKind::Proj(name, idx, e) => {
                Expr::proj(name.clone(), *idx, e.instantiate_at(val, depth))
            }
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
            ExprKind::App(f, a) => {
                Expr::app(f.abstract_fvar_at(id, depth), a.abstract_fvar_at(id, depth))
            }
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
            ExprKind::App(f, a) => {
                Expr::app(f.subst_fvar(id, replacement), a.subst_fvar(id, replacement))
            }
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
            let next = match &current.kind {
                ExprKind::App(f, _) => f.as_ref().clone(),
                _ => return current,
            };
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

    /// ARMED-CONTROL ONLY (probe 4) — NOT a production transcription: force a
    /// caller-chosen (REUSED) id through the same guard+append path, modeling
    /// a broken freshness allocator. Production `push_with_id` (:299-320)
    /// would PANIC on both asserts here; the guard_trips are the observable.
    /// The next_id update is production push_with_id's (`max(next_id, id+1)`
    /// — a reused LOW id never advances the counter).
    pub fn push_forced_id_control(
        &mut self,
        id: FVarId,
        name: Name,
        type_: Expr,
        bi: BinderData,
    ) -> FVarId {
        self.freshness_guard(id);
        self.decls.push(LocalDecl {
            id,
            name,
            type_,
            value: None,
            bi,
        });
        if id.0 >= self.next_id {
            self.next_id = id.0 + 1;
        }
        id
    }

    /// `pop` (:189-193) — VERBATIM minus the index-map removal ([C-idx]: the
    /// backward scan never sees popped entries). The popped decl is dropped
    /// (leak model). Popped ids are NEVER re-minted (next_id is monotonic).
    pub fn pop(&mut self) {
        let _decl = self.decls.pop();
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
    /// tc/type_error.rs:41-43 — FVar id not found in the local context: the
    /// production error the FVar-arm lookup mints. NEW reachable this round
    /// (the B3 de-modeling); placed in the production position (right after
    /// UnboundVariable).
    UnknownFVar(FVarId),
    UnknownConst(Name),
    TypeMismatch {
        expected: Arc<Expr>,
        inferred: Arc<Expr>,
    },
    NotAPi {
        ty: Arc<Expr>,
    },
    ExpectedSort {
        ty: Arc<Expr>,
    },
    SortDepthExceeded {
        depth: u32,
    },
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
            if name_eq(&entry.0, name) {
                return entry.1.clone();
            }
            i += 1;
        }
        None
    }
    fn get_constructor_num_params(&self, name: &Name) -> Option<u32> {
        let mut i: usize = 0;
        let n = self.ctors.len();
        while i < n {
            let entry = &self.ctors[i];
            if name_eq(&entry.0, name) {
                return Some(entry.1);
            }
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
    fn try_iota_reduction(&self, _e: &Expr) -> Option<Expr> {
        None
    } // B8
    fn try_quot_reduction(&self, _e: &Expr) -> Option<Expr> {
        None
    } // B8

    // ── WHNF pillar (cert/reduction.rs whnf_impl) — VERBATIM, as verified. ──
    fn whnf_impl(&self, e: &Expr) -> Expr {
        self.whnf_inner(e)
    }
    fn whnf_inner(&self, e: &Expr) -> Expr {
        match &e.kind {
            ExprKind::App(f, a) => {
                let f_whnf = self.whnf_impl(f);
                match &f_whnf.kind {
                    ExprKind::Lam(_, _, body) => {
                        let reduced = body.instantiate(a);
                        self.whnf_impl(&reduced)
                    }
                    _ => {
                        let app = Expr::from_kind(ExprKind::App(Arc::new(f_whnf), a.clone()));
                        if let Some(reduced) = self.try_iota_reduction(&app) {
                            return self.whnf_impl(&reduced);
                        }
                        if let Some(reduced) = self.try_quot_reduction(&app) {
                            return self.whnf_impl(&reduced);
                        }
                        app
                    }
                }
            }
            ExprKind::Let(_, _, val, body, _) => {
                let reduced = body.instantiate(val);
                self.whnf_impl(&reduced)
            }
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
                if field_idx < args.len() {
                    return self.whnf_impl(&args[field_idx]);
                }
            }
        }
        Expr::from_kind(ExprKind::Proj(
            struct_name.clone(),
            idx,
            Arc::new(expr_whnf),
        ))
    }

    // ── DEF-EQ pillar (cert/expr_eq.rs) — VERBATIM; THE UNIVERSE INTEGRATION:
    // `level_eq` is the REAL `Level::is_def_eq` (cert/expr_eq.rs:34-36) — the
    // full Max/IMax normalization machinery. Const/Proj name equality is the
    // PRODUCTION name_eq. ──
    fn level_eq(&self, l1: &Level, l2: &Level) -> bool {
        Level::is_def_eq(l1, l2)
    }
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
    fn structural_eq(&self, a: &Expr, b: &Expr) -> bool {
        match (&a.kind, &b.kind) {
            (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
            (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => self.level_eq(l1, l2),
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => {
                name_eq(n1, n2) && self.level_vec_eq(ls1, ls2)
            }
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.structural_eq(f1, f2) && self.structural_eq(a1, a2)
            }
            (ExprKind::Lam(_b1, ty1, b1), ExprKind::Lam(_b2, ty2, b2))
            | (ExprKind::Pi(_b1, ty1, b1), ExprKind::Pi(_b2, ty2, b2)) => {
                self.structural_eq(ty1, ty2) && self.structural_eq(b1, b2)
            }
            (ExprKind::Let(_, ty1, v1, b1, _), ExprKind::Let(_, ty2, v2, b2, _)) => {
                self.structural_eq(ty1, ty2)
                    && self.structural_eq(v1, v2)
                    && self.structural_eq(b1, b2)
            }
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
                name_eq(n1, n2) && i1 == i2 && self.structural_eq(e1, e2)
            }
            (ExprKind::MData(_, in1), ExprKind::MData(_, in2)) => self.structural_eq(in1, in2),
            _ => false,
        }
    }
    fn is_def_eq(&self, a: &Expr, b: &Expr) -> bool {
        self.def_eq_inner(a, b)
    }
    fn def_eq_impl(&self, a: &Expr, b: &Expr) -> bool {
        self.def_eq_inner(a, b)
    }
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
            (ExprKind::Const(n1, ls1), ExprKind::Const(n2, ls2)) => {
                name_eq(n1, n2) && self.level_vec_eq(ls1, ls2)
            }
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.def_eq_impl(f1, f2) && self.def_eq_impl(a1, a2)
            }
            (ExprKind::Lam(_b1, ty1, b1), ExprKind::Lam(_b2, ty2, b2))
            | (ExprKind::Pi(_b1, ty1, b1), ExprKind::Pi(_b2, ty2, b2)) => {
                self.def_eq_impl(ty1, ty2) && self.def_eq_impl(b1, b2)
            }
            (ExprKind::Let(_, ty1, v1, b1, _), ExprKind::Let(_, ty2, v2, b2, _)) => {
                self.def_eq_impl(ty1, ty2) && self.def_eq_impl(v1, v2) && self.def_eq_impl(b1, b2)
            }
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
                name_eq(n1, n2) && i1 == i2 && self.def_eq_impl(e1, e2)
            }
            (ExprKind::MData(_, in1), ExprKind::MData(_, in2)) => self.def_eq_impl(in1, in2),
            _ => false,
        };
        if matched {
            return true;
        }
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
                    _ => Err(TypeError::NotAPi {
                        ty: Arc::new(f_type),
                    }),
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
                let arg_sort_whnf = self.whnf_impl(&arg_sort);
                match &arg_sort_whnf.kind {
                    ExprKind::Sort(_) => {}
                    _ => {
                        return Err(TypeError::ExpectedSort {
                            ty: Arc::new(arg_sort),
                        });
                    }
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
                let arg_sort_whnf = self.whnf_impl(&arg_sort);
                let l1 = match &arg_sort_whnf.kind {
                    ExprKind::Sort(l) => l.clone(),
                    _ => {
                        return Err(TypeError::ExpectedSort {
                            ty: Arc::new(arg_sort),
                        });
                    }
                };
                let fvar_id = ctx.push(name_anon(), arg_type.as_ref().clone(), *bi);
                let body_with_fvar = self.open_bvar(body, fvar_id);
                let body_sort = self.infer_type_core(&body_with_fvar, ctx);
                ctx.pop();
                let body_sort = body_sort?;
                let body_sort_whnf = self.whnf_impl(&body_sort);
                let l2 = match &body_sort_whnf.kind {
                    ExprKind::Sort(l) => l.clone(),
                    _ => {
                        return Err(TypeError::ExpectedSort {
                            ty: Arc::new(body_sort),
                        });
                    }
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
                let ty_sort_whnf = self.whnf_impl(&ty_sort);
                match &ty_sort_whnf.kind {
                    ExprKind::Sort(_) => {}
                    _ => {
                        return Err(TypeError::ExpectedSort {
                            ty: Arc::new(ty_sort),
                        });
                    }
                }
                let val_type = self.infer_type_core(val, ctx)?;
                if !self.is_def_eq(&val_type, ty) {
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
        let ty_whnf = self.whnf_impl(&ty);
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
            _ => Err(TypeError::ExpectedSort { ty: Arc::new(ty) }),
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

// ════════════════════════════════════════════════════════════════════════════
// R17 — THE INDUCTIVE-SOUNDNESS GATE, re-composed on the modern stack.
//
// The three soundness-critical inductive checks — whose correctness IS the
// consistency of the logic for inductive types — transcribed VERBATIM at their
// production positions and COMPOSED with the R6/R8 modern stack above (real
// Names + murmur cached_hash + name_eq; the full production Level with Max/IMax
// + is_zero/is_nonzero; production compute_meta; the FVar `LocalContext` binder
// discipline threading whnf/def_eq/infer_type/infer_sort):
//
//   1. STRICT POSITIVITY (the Reynolds-paradox guard) — inductive/mod.rs:409
//      check_positivity → :451 check_positivity_in_ctor_type_impl → :490
//      check_strictly_positive_impl → :661 check_no_negative_occurrence → :698
//      mentions_name. A constructor argument in which the inductive occurs to
//      the LEFT of an arrow ((I -> X) -> I) must be REJECTED — else Reynolds's
//      paradox is encodable and False is provable.
//   2. LARGE-ELIMINATION-FROM-PROP — env/elim_analysis.rs:38
//      elim_only_at_universe_zero + tc/infer.rs:808 ctor_field_sort_levels.
//      A Prop inductive may eliminate into a larger universe ONLY for the
//      recognized subsingleton cases; a general Prop doing large elim extracts
//      data from a proof -> unsound. THE MODERN FORM uses `Level::is_nonzero()`
//      (Lean `is_not_zero`, inductive.cpp:246-248/:481-484 — the [R1] fix: a
//      possibly-zero `Sort u` must run the restriction analysis), which is a
//      GENUINE use of the full production Level not available in the R1 model.
//   3. CTOR-RETURN WELL-FORMEDNESS (is_valid_ind_app, incl. lean4#2125) —
//      inductive/mod.rs:854 validate_ctor_return_type + :752 get_return_type +
//      :710 count_pi_args. Each constructor must RETURN the inductive applied
//      to exactly the declared params (as fixed-param BVars) and block-free
//      indices; a wrong head / wrong param / index-mentions-inductive (#2125)
//      is a route to False and is REJECTED.
//
// THE LOAD-BEARING PROOF (centerpiece): a BLIND control that DROPS the
// soundness-critical sub-check of each gate ACCEPTS the corresponding unsound
// declaration where the AWARE (production) gate REJECTS — proven native == JIT
// for each of positivity / large-elim / ctor-return, so each check is
// soundness-critical in compiled machine code.
//
// BOUNDARIES (inherited + this round):
//   * [B5] the 11-variant ExprKind core (no Cubical*/ZFC*/SProp/Squash arms):
//     the positivity / ctor_return / mentions_name transcriptions therefore
//     omit those arms (structurally absent, exactly as R8's find_undef walk).
//     Those arms are conservative recursions NEVER taken by an ordinary
//     inductive (whose ctor types use only BVar/FVar/Sort/Const/App/Pi/Lam/
//     Let/Lit/Proj/MData) — precisely why the R1 slices flagged them
//     never-constructed. The CubicalPath ctor-return branch is likewise absent.
//   * [C-refcell] ctor_field_sort_levels threads a fresh per-call LocalContext
//     (production uses the shared TypeChecker self.ctx; R8's [C-refcell]).
//   * def_eq is the pillar engine (whnf + structural + eta + Level::is_def_eq);
//     the lazy-delta / cache / reducers / SProp phases (R11-R15) are NOT
//     exercised by these three checks (the field-sort compares are leaf/Const).
//   * NESTED / mutual inductives beyond the single-sibling positivity case are
//     OUT OF SCOPE this round (single-type and one mutual sibling modeled).
// ════════════════════════════════════════════════════════════════════════════

// ── In-module Names (real murmur cached_hash; from_string_uncached unrolled) ──
fn nm1(a: &str) -> Name {
    fold_step(name_anon(), a)
}
fn nm_i() -> Name {
    nm1("I")
}
fn nm_bool() -> Name {
    nm1("Bool")
}
fn nm_a() -> Name {
    nm1("A")
}
fn nm_list() -> Name {
    nm1("List")
}
fn nm_forest() -> Name {
    nm1("Forest")
}
fn nm_mk() -> Name {
    nm1("mk")
}
fn nm_dd() -> Name {
    nm1("Dd")
}
fn nm_pp() -> Name {
    nm1("Pp")
}
// The Lit-rule type names the infer stack references (B11) — cut with the R8
// scenario section, re-provided here.
fn nat_type_name() -> Name {
    nm1("Nat")
}
fn str_type_name() -> Name {
    nm1("String")
}

fn bd0() -> BinderData {
    BinderData { info: 0, mult: 2 }
}
// The R8 LocalContext probe (push_forced_id_control) references `bdm()` — the
// same default BinderData; re-provided here (cut with the R8 scenario section).
fn bdm() -> BinderData {
    BinderData { info: 0, mult: 2 }
}

// ── Inductive-decl structs (FAITHFUL mirrors of inductive/mod.rs Constructor
// (:33), InductiveType (:42), InductiveDecl (:53); only the read fields kept). ─
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

// ── InductiveError — the reject variants these three gates produce, in the
// real enum's source shape (NonPositive from positivity; the ctor-return trio
// from is_valid_ind_app). ──
#[derive(Clone, Debug)]
pub enum InductiveError {
    NonPositive(Name, Name),
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

// ── Pi-telescope helpers — VERBATIM inductive/mod.rs:752 get_return_type,
// :710 count_pi_args. ──
fn get_return_type(expr: &Expr) -> &Expr {
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = &current.kind {
        current = body;
    }
    current
}

fn count_pi_args(expr: &Expr) -> u32 {
    let mut count = 0u32;
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = &current.kind {
        count = count.saturating_add(1);
        current = body;
    }
    count
}

// ── mentions_name — VERBATIM the ExprVisitor visit_const override
// (inductive/mod.rs:687-699 / mentions_name :698): structural recursion,
// combine = OR, only Const matches; Const equality is the PRODUCTION name_eq.
// Over the 11-variant core [B5] (the exotic arms are structurally absent). ──
fn mentions_name(expr: &Expr, name: &Name) -> bool {
    match &expr.kind {
        ExprKind::Const(n, _) => name_eq(n, name),
        ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => false,
        ExprKind::App(f, a) => mentions_name(f, name) || mentions_name(a, name),
        ExprKind::Lam(_, ty, body) => mentions_name(ty, name) || mentions_name(body, name),
        ExprKind::Pi(_, ty, body) => mentions_name(ty, name) || mentions_name(body, name),
        ExprKind::Let(_, ty, val, body, _) => {
            mentions_name(ty, name) || mentions_name(val, name) || mentions_name(body, name)
        }
        ExprKind::Proj(_, _, e) => mentions_name(e, name),
        ExprKind::MData(_, inner) => mentions_name(inner, name),
    }
}

// ═══════════════════════ CHECK 1 — STRICT POSITIVITY ════════════════════════
// VERBATIM inductive/mod.rs; the `stack_safe(|| ...)` maybe_grow pass-throughs
// (B4) are inlined to direct calls. `blind` = the DROP control: when set, the
// Pi-arm strict-positivity guard (check_no_negative_occurrence on the arrow
// DOMAIN, for the inductive AND every mutual sibling — mod.rs:536-541) is NOT
// run, so a non-strictly-positive constructor argument is ADMITTED.

/// VERBATIM :661 check_no_negative_occurrence.
fn check_no_negative_occurrence(inductive_name: &Name, expr: &Expr) -> Result<(), InductiveError> {
    if mentions_name(expr, inductive_name) {
        Err(InductiveError::NonPositive(
            inductive_name.clone(),
            inductive_name.clone(),
        ))
    } else {
        Ok(())
    }
}

/// VERBATIM :490 check_strictly_positive_impl (11-variant core).
fn check_strictly_positive_impl(
    inductive_name: &Name,
    expr: &Expr,
    _param_count: u32,
    all_ind_names: &[&Name],
    blind: bool,
) -> Result<(), InductiveError> {
    match &expr.kind {
        ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => Ok(()),

        ExprKind::Const(_name, _) => Ok(()),

        ExprKind::App(f, a) => {
            let head = expr.get_app_fn();
            if let ExprKind::Const(name, _) = &head.kind {
                if name_eq(name, inductive_name) {
                    // I applied to args — args must not mention ANY mutual
                    // inductive negatively (#2145, is_valid_ind_app/has_ind_occ).
                    // `for arg { for ind_name { ... } }` transcribed as index
                    // loops (B9 — the slice-iter dual, identical order).
                    let args = expr.get_app_args();
                    let mut ai: usize = 0;
                    while ai < args.len() {
                        let mut ni: usize = 0;
                        while ni < all_ind_names.len() {
                            check_no_negative_occurrence(all_ind_names[ni], &args[ai])?;
                            ni += 1;
                        }
                        ai += 1;
                    }
                    return Ok(());
                }
            }
            check_strictly_positive_impl(inductive_name, f, _param_count, all_ind_names, blind)?;
            check_strictly_positive_impl(inductive_name, a, _param_count, all_ind_names, blind)?;
            Ok(())
        }

        ExprKind::Pi(_, domain, codomain) => {
            // THE CRITICAL CASE: (A -> B) in a constructor argument. The
            // inductive CANNOT appear in A (negative), and neither can any
            // sibling mutual inductive (Wave 107). It CAN appear in B.
            //
            // The soundness-critical guard — DROPPED under `blind`.
            if !blind {
                check_no_negative_occurrence(inductive_name, domain)?;
                let mut si: usize = 0;
                while si < all_ind_names.len() {
                    let sibling = all_ind_names[si];
                    if !name_eq(sibling, inductive_name) {
                        check_no_negative_occurrence(sibling, domain)?;
                    }
                    si += 1;
                }
            }
            check_strictly_positive_impl(
                inductive_name,
                codomain,
                _param_count,
                all_ind_names,
                blind,
            )?;
            Ok(())
        }

        ExprKind::Lam(_, ty, body) => {
            check_strictly_positive_impl(inductive_name, ty, _param_count, all_ind_names, blind)?;
            check_strictly_positive_impl(inductive_name, body, _param_count, all_ind_names, blind)?;
            Ok(())
        }

        ExprKind::Let(_, ty, val, body, _) => {
            check_strictly_positive_impl(inductive_name, ty, _param_count, all_ind_names, blind)?;
            check_strictly_positive_impl(inductive_name, val, _param_count, all_ind_names, blind)?;
            check_strictly_positive_impl(inductive_name, body, _param_count, all_ind_names, blind)?;
            Ok(())
        }

        ExprKind::Proj(_, _, e) => {
            check_strictly_positive_impl(inductive_name, e, _param_count, all_ind_names, blind)?;
            Ok(())
        }

        ExprKind::MData(_, inner) => {
            check_strictly_positive_impl(inductive_name, inner, _param_count, all_ind_names, blind)
        }
    }
}

/// VERBATIM :451 check_positivity_in_ctor_type_impl.
fn check_positivity_in_ctor_type_impl(
    inductive_name: &Name,
    expr: &Expr,
    param_count: u32,
    all_ind_names: &[&Name],
    blind: bool,
) -> Result<(), InductiveError> {
    match &expr.kind {
        ExprKind::Pi(_, domain, codomain) => {
            check_strictly_positive_impl(
                inductive_name,
                domain,
                param_count,
                all_ind_names,
                blind,
            )?;
            check_positivity_in_ctor_type_impl(
                inductive_name,
                codomain,
                param_count,
                all_ind_names,
                blind,
            )?;
            Ok(())
        }
        _ => Ok(()),
    }
}

/// VERBATIM :409 check_positivity (public entry).
fn check_positivity(
    inductive_name: &Name,
    expr: &Expr,
    param_count: u32,
    all_ind_names: &[&Name],
    blind: bool,
) -> Result<(), InductiveError> {
    check_positivity_in_ctor_type_impl(inductive_name, expr, param_count, all_ind_names, blind)
}

// ══════════════════ CHECK 3 — CTOR-RETURN (is_valid_ind_app) ════════════════
// VERBATIM inductive/mod.rs:854 validate_ctor_return_type. The `.get`/
// `.is_some_and`/`skip().enumerate()` iterator forms are transcribed as index
// `while`-loops (B9 — the de-Bruijn dual, identical bound / first-failure
// order), exactly as the landed clean_ctor_return_slice. The CubicalPath HIT
// dispatch is absent (11-variant core, [B5]; ordinary ctor returns are
// Const/App heads). `blind` DROPS each of the three soundness rejects.
fn validate_ctor_return_type(
    ctor: &Constructor,
    ind_type: &InductiveType,
    decl: &InductiveDecl,
    all_names: &[&Name],
    blind: bool,
) -> Result<(), InductiveError> {
    let return_type = get_return_type(&ctor.type_);
    let head = return_type.get_app_fn();

    // Check 1: constructor returns the correct inductive type (head name_eq).
    let head_ok = match &head.kind {
        ExprKind::Const(name, _) => name_eq(name, &ind_type.name),
        _ => false,
    };
    if !head_ok && !blind {
        return Err(InductiveError::ConstructorReturnType(
            ctor.name.clone(),
            ind_type.name.clone(),
        ));
    }

    let args = return_type.get_app_args();
    let args_len = args.len();

    // Check 2: parameter arguments match declared params as BVars.
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
            if !param_ok && !blind {
                return Err(InductiveError::ConstructorParamMismatch {
                    ctor_name: ctor.name.clone(),
                    ind_name: ind_type.name.clone(),
                    param_idx: i,
                });
            }
            i += 1;
        }
    }

    // Check 3: index arguments must not mention any inductive in the mutual
    // block (lean4#2125).
    let num_params = decl.num_params as usize;
    let mut j = num_params;
    while j < args_len {
        let idx_pos = (j - num_params) as u32;
        let idx_arg = &args[j];
        let mut ni: usize = 0;
        while ni < all_names.len() {
            let ind_name = all_names[ni];
            if mentions_name(idx_arg, ind_name) && !blind {
                return Err(InductiveError::IndexArgMentionsInductive {
                    ctor_name: ctor.name.clone(),
                    ind_name: ind_name.clone(),
                    index_pos: idx_pos,
                });
            }
            ni += 1;
        }
        j += 1;
    }

    Ok(())
}

// ═════════════════ CHECK 2 — LARGE-ELIMINATION-FROM-PROP ═══════════════════
// ctor_field_sort_levels — VERBATIM tc/infer.rs:808, threaded on the R8 FVar
// LocalContext (ctx_push a fresh FVar carrying the field domain -> open_bvar
// the body -> infer_sort the domain -> ctx_pop). [C-refcell]: a fresh per-call
// context (production shares self.ctx).
impl<'env> Verifier<'env> {
    fn ctor_field_sort_levels(
        &self,
        ctor_type: &Expr,
        num_params: u32,
    ) -> Result<Vec<Level>, TypeError> {
        let mut current = ctor_type.clone();
        let mut depth = 0u32;
        let mut field_sorts: Vec<Level> = Vec::new();
        let mut ctx = LocalContext::new();

        let result = loop {
            match current.kind() {
                ExprKind::Pi(bd, domain, body) => {
                    if depth >= num_params {
                        match self.infer_sort(domain, &mut ctx) {
                            Ok(sort) => field_sorts.push(sort),
                            Err(e) => break Err(e),
                        }
                    }
                    let fvar_id = ctx.push(name_anon(), domain.as_ref().clone(), *bd);
                    current = self.open_bvar(body, fvar_id);
                    depth += 1;
                }
                _ => break Ok(field_sorts),
            }
        };

        let mut k = 0u32;
        while k < depth {
            ctx.pop();
            k += 1;
        }
        result
    }
}

// elim_only_at_universe_zero — VERBATIM env/elim_analysis.rs:38 (the MODERN
// form: `result_level.is_nonzero()` gate over the full production Level; the
// filter/map/skip iterator forms transcribed as index loops, B9). Returns TRUE
// iff the recursor may eliminate ONLY into Prop (large elim FORBIDDEN). `blind`
// DROPS the field-not-a-direct-index restriction (the Int.NonNeg-parity guard):
// a non-Prop field that is not a return index no longer forces Prop-only, so
// large elimination is GRANTED to a Nonempty-like proposition — UNSOUND.
fn elim_only_at_universe_zero(
    verifier: &Verifier,
    ind_type_expr: &Expr,
    constructors: &[Constructor],
    num_params: u32,
    num_types: usize,
    blind: bool,
) -> bool {
    let result_sort = get_return_type(ind_type_expr);
    let result_level = match &result_sort.kind {
        ExprKind::Sort(l) => l.clone(),
        _ => return false, // not a sort head — malformed; rejected elsewhere
    };
    if result_level.is_nonzero() {
        return false; // provably >= 1 -> large elimination allowed
    }

    if num_types > 1 {
        return true; // Mutual Prop predicates -> Prop-only (#3238)
    }

    if constructors.len() > 1 {
        return true; // Multiple constructors -> Prop-only
    }
    if constructors.is_empty() {
        return false; // Empty type (e.g. False) -> large elimination
    }

    let ctor = &constructors[0];
    let field_sorts = match verifier.ctor_field_sort_levels(&ctor.type_, num_params) {
        Ok(sorts) => sorts,
        Err(_) => {
            // Type checking failed — conservatively restrict to Prop
            // elimination (sound: at worst too-restrictive).
            return true;
        }
    };

    // Non-Prop field positions (0-indexed from first non-param field).
    let mut non_prop_fields: Vec<usize> = Vec::new();
    {
        let mut i: usize = 0;
        let n = field_sorts.len();
        while i < n {
            if !field_sorts[i].is_zero() {
                non_prop_fields.push(i);
            }
            i += 1;
        }
    }

    if non_prop_fields.is_empty() {
        return false; // All non-param fields in Prop -> large elimination allowed
    }

    // Condition 2: non-Prop fields must appear DIRECTLY in return-type indices.
    let mut cur = &ctor.type_;
    while let ExprKind::Pi(_, _, body) = &cur.kind {
        cur = body;
    }
    let mut return_args: Vec<&Expr> = Vec::new();
    {
        let mut ret = cur;
        while let ExprKind::App(func, arg) = &ret.kind {
            return_args.push(arg.as_ref());
            ret = func;
        }
    }
    return_args.reverse();
    let mut index_args: Vec<&Expr> = Vec::new();
    {
        let mut j: usize = 0;
        let m = return_args.len();
        while j < m {
            if j >= num_params as usize {
                index_args.push(return_args[j]);
            }
            j += 1;
        }
    }

    let total_fields = field_sorts.len();
    let mut fp: usize = 0;
    let nf = non_prop_fields.len();
    while fp < nf {
        let field_pos = non_prop_fields[fp];
        let bvar_idx = (total_fields - 1 - field_pos) as u32;
        let mut found = false;
        {
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
        }
        // The soundness-critical restriction — DROPPED under `blind`.
        if !found && !blind {
            return true; // Field not a direct index arg -> Prop-only elimination
        }
        fp += 1;
    }

    false // All non-Prop fields appear directly in indices -> large elimination
}

// ═══════════════════════════ SCENARIO BUILDERS ══════════════════════════════
// Prop tower (the R6 prop_ty): T0 = forall(a:Sort0). a -> a : Sort 0 — a Prop.
fn prop_ty() -> Expr {
    Expr::pi(
        bd0(),
        Expr::sort0(),
        Expr::pi(bd0(), Expr::bvar(0), Expr::bvar(1)),
    )
}

/// The modeled environment for the large-elim scenarios (B1 slice-scan):
///   Pp := prop_ty          => Pp : Sort 0     (a Prop field domain)
///   Dd := Sort 0           => Dd : Sort 1     (a Type-0 field domain)
fn build_env() -> Vec<(Name, Option<Expr>)> {
    let mut env: Vec<(Name, Option<Expr>)> = Vec::new();
    env.push((nm_pp(), Some(prop_ty())));
    env.push((nm_dd(), Some(Expr::sort0())));
    env
}

// ── Const-head Expr helpers (module-level fns; the frontend's emit-closure
// does not lower nested no-capture closures, so scenario builders call these
// directly — the R6/R8 build_decl_case convention). ──
fn ei() -> Expr {
    Expr::cnst(nm_i())
}
fn ea() -> Expr {
    Expr::cnst(nm_a())
}
fn eb() -> Expr {
    Expr::cnst(nm_bool())
}
fn ef() -> Expr {
    Expr::cnst(nm_forest())
}
fn en() -> Expr {
    Expr::cnst(nat_type_name())
}
fn el() -> Expr {
    Expr::cnst(nm_list())
}
fn epp() -> Expr {
    Expr::cnst(nm_pp())
}
fn edd() -> Expr {
    Expr::cnst(nm_dd())
}

// ── Positivity scenarios: build the constructor type for `case`. ──
// The inductive is `I`; the mutual sibling (case 4) is `Forest`.
fn pos_ctor_type(case: u64) -> Expr {
    let bd = bd0();
    match case {
        // 0 ACCEPT (Nat-like): mk : I -> I  (direct recursive arg).
        0 => Expr::pi(bd, ei(), ei()),
        // 1 ACCEPT (W-type-like): mk : (A -> I) -> I  (strictly-positive
        //   higher-order arg — I only to the RIGHT of the inner arrow).
        1 => Expr::pi(bd, Expr::pi(bd, ea(), ei()), ei()),
        // 2 REJECT (Reynolds): mk : (I -> Bool) -> I  (I to the LEFT of the
        //   inner arrow — non-strictly-positive). CENTERPIECE.
        2 => Expr::pi(bd, Expr::pi(bd, ei(), eb()), ei()),
        // 3 ACCEPT: mk : Bool -> I -> I  (a data field + a recursive field).
        3 => Expr::pi(bd, eb(), Expr::pi(bd, ei(), ei())),
        // 4 REJECT (Wave 107 mutual sibling): mk : (Forest -> Bool) -> I —
        //   the SIBLING `Forest` appears non-positively; checked because the
        //   positivity walk runs against ALL mutual names.
        _ => Expr::pi(bd, Expr::pi(bd, ef(), eb()), ei()),
    }
}

// ── Ctor-return scenarios. Inductive `I`; ctor `mk`. ──
fn cr_scenario(case: u64) -> (Expr, u32) {
    let bd = bd0();
    match case {
        // 0 ACCEPT: mk : Nat -> I  (num_params 0, head I).
        0 => (Expr::pi(bd, en(), ei()), 0),
        // 1 ACCEPT param: mk : (A:Sort0) -> I (BVar 0)  (num_params 1).
        1 => (
            Expr::pi(bd, Expr::sort0(), Expr::app(ei(), Expr::bvar(0))),
            1,
        ),
        // 2 REJECT head: mk : Nat -> Nat  (head is not I).
        2 => (Expr::pi(bd, en(), en()), 0),
        // 3 REJECT param: mk : (A:Sort0) -> I Nat  (param arg is Nat, not BVar 0).
        3 => (Expr::pi(bd, Expr::sort0(), Expr::app(ei(), en())), 1),
        // 4 REJECT index (lean4#2125): mk : (A:Sort0) -> I (BVar 0) (List I) —
        //   one param (ok) + one index `List I` that MENTIONS I. CENTERPIECE.
        _ => (
            Expr::pi(
                bd,
                Expr::sort0(),
                Expr::app(Expr::app(ei(), Expr::bvar(0)), Expr::app(el(), ei())),
            ),
            1,
        ),
    }
}

// ── Large-elim scenarios: (ind_type_former, ctor_type, ctor_count, num_params,
//    num_types). Inductive `I`. ──
fn elim_scenario(case: u64) -> (Expr, Expr, u32, u32, usize) {
    let bd = bd0();
    match case {
        // 0 False-like: Prop, 0 ctors -> large elim (10).
        0 => (Expr::sort0(), Expr::sort0(), 0, 0, 1),
        // 1 Or-like: Prop, 2 ctors -> Prop-only (11).
        1 => (Expr::sort0(), Expr::pi(bd, epp(), ei()), 2, 0, 1),
        // 2 Mutual: Prop, 1 ctor, num_types 2 -> Prop-only (11).
        2 => (Expr::sort0(), Expr::pi(bd, epp(), ei()), 1, 0, 2),
        // 3 Type-valued: Sort 1, 1 ctor -> large elim (10) via is_nonzero.
        3 => (
            Expr::sort(Level::succ(Level::Zero)),
            Expr::pi(bd, epp(), ei()),
            1,
            0,
            1,
        ),
        // 4 And-like: Prop, 1 ctor `Pp -> Pp -> I` (both fields Prop) -> large
        //   elim allowed (10) — the recognized subsingleton case.
        4 => (
            Expr::sort0(),
            Expr::pi(bd, epp(), Expr::pi(bd, epp(), ei())),
            1,
            0,
            1,
        ),
        // 5 Nonempty-like: Prop, 1 ctor `Dd -> I` (a non-Prop field, NOT an
        //   index) -> Prop-only (11). CENTERPIECE (blind -> 10, granting large
        //   elim = extracting the Dd datum from a proof = UNSOUND).
        _ => (Expr::sort0(), Expr::pi(bd, edd(), ei()), 1, 0, 1),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// The differential OUTPUT: verdict code + the primary Name identity (real
// cached_hash) + the scenario term's ExprMeta bit-pattern — so a native == JIT
// comparison pins the VERDICT, the ERROR-IDENTITY Name (murmur cached_hash),
// AND compute_meta all at once.
//   code: 0 Accept | 1 NonPositive | 2 CtorReturnHead | 3 ParamMismatch
//         | 4 IndexMentions | 10 ElimLarge | 11 ElimPropOnly
//         (param_idx / index_pos folded into bits 8..16 for the ctor trio)
// ════════════════════════════════════════════════════════════════════════════
#[repr(C)]
pub struct CheckResult {
    pub code: u64,
    pub name_hash: u64,
    pub ctor_meta: u64,
}

// ── ROOT 1: positivity ──
#[unsafe(no_mangle)]
pub extern "C" fn positivity_root(out: *mut CheckResult, case: u64, blind: u64) {
    let blind = blind != 0;
    let ind = nm_i();
    let sib = nm_forest();
    let ctor_type = pos_ctor_type(case);
    let names_one = [&ind];
    let names_two = [&ind, &sib];
    // case 4 is the mutual scenario (two names); all others single.
    let all: &[&Name] = if case == 4 { &names_two } else { &names_one };
    let res = check_positivity(&ind, &ctor_type, 0, all, blind);
    let (code, name_hash) = match res {
        Ok(()) => (0u64, ind.cached_hash),
        Err(InductiveError::NonPositive(n, _)) => (1u64, n.cached_hash),
        Err(InductiveError::ConstructorReturnType(n, _)) => (2u64, n.cached_hash),
        Err(InductiveError::ConstructorParamMismatch {
            ind_name,
            param_idx,
            ..
        }) => (3u64 | ((param_idx as u64) << 8), ind_name.cached_hash),
        Err(InductiveError::IndexArgMentionsInductive {
            ind_name,
            index_pos,
            ..
        }) => (4u64 | ((index_pos as u64) << 8), ind_name.cached_hash),
    };
    let r = CheckResult {
        code,
        name_hash,
        ctor_meta: ctor_type.meta().raw(),
    };
    unsafe {
        std::ptr::write(out, r);
    }
}

// ── ROOT 2: ctor-return ──
#[unsafe(no_mangle)]
pub extern "C" fn ctor_return_root(out: *mut CheckResult, case: u64, blind: u64) {
    let blind = blind != 0;
    let ind = nm_i();
    let ctor_name = nm_mk();
    let (ctor_type, num_params) = cr_scenario(case);
    let ctor = Constructor {
        name: ctor_name,
        type_: ctor_type.clone(),
    };
    let ind_type = InductiveType {
        name: ind.clone(),
        type_: Expr::sort0(),
        constructors: Vec::new(),
    };
    let decl = InductiveDecl {
        num_params,
        types: Vec::new(),
    };
    let names_one = [&ind];
    let all: &[&Name] = &names_one;
    let res = validate_ctor_return_type(&ctor, &ind_type, &decl, all, blind);
    let (code, name_hash) = match res {
        Ok(()) => (0u64, ind.cached_hash),
        Err(InductiveError::NonPositive(n, _)) => (1u64, n.cached_hash),
        Err(InductiveError::ConstructorReturnType(_, ind_name)) => (2u64, ind_name.cached_hash),
        Err(InductiveError::ConstructorParamMismatch {
            ind_name,
            param_idx,
            ..
        }) => (3u64 | ((param_idx as u64) << 8), ind_name.cached_hash),
        Err(InductiveError::IndexArgMentionsInductive {
            ind_name,
            index_pos,
            ..
        }) => (4u64 | ((index_pos as u64) << 8), ind_name.cached_hash),
    };
    let r = CheckResult {
        code,
        name_hash,
        ctor_meta: ctor_type.meta().raw(),
    };
    unsafe {
        std::ptr::write(out, r);
    }
}

// ── ROOT 3: large-elim ──
#[unsafe(no_mangle)]
pub extern "C" fn elim_root(out: *mut CheckResult, case: u64, blind: u64) {
    let blind = blind != 0;
    let env = build_env();
    let ctors_tbl: Vec<(Name, u32)> = Vec::new();
    let verifier = Verifier {
        env: &env,
        ctors: &ctors_tbl,
    };
    let ind = nm_i();
    let (ind_type_expr, ctor_type, ctor_count, num_params, num_types) = elim_scenario(case);
    let mut ctors: Vec<Constructor> = Vec::new();
    if ctor_count >= 1 {
        ctors.push(Constructor {
            name: nm_mk(),
            type_: ctor_type.clone(),
        });
    }
    if ctor_count >= 2 {
        ctors.push(Constructor {
            name: nm_mk(),
            type_: ctor_type.clone(),
        });
    }
    let only_zero = elim_only_at_universe_zero(
        &verifier,
        &ind_type_expr,
        &ctors,
        num_params,
        num_types,
        blind,
    );
    let code = if only_zero { 11u64 } else { 10u64 };
    let r = CheckResult {
        code,
        name_hash: ind.cached_hash,
        ctor_meta: ctor_type.meta().raw(),
    };
    unsafe {
        std::ptr::write(out, r);
    }
}

// ── standalone smoke harness (native only; not part of any emitted root) ──
fn run(out_root: u8, case: u64, blind: u64) -> u64 {
    let mut slot = std::mem::MaybeUninit::<CheckResult>::uninit();
    let r = unsafe {
        match out_root {
            0 => positivity_root(slot.as_mut_ptr(), case, blind),
            1 => ctor_return_root(slot.as_mut_ptr(), case, blind),
            _ => elim_root(slot.as_mut_ptr(), case, blind),
        };
        slot.assume_init()
    };
    r.code
}

fn main() {
    // Positivity: 0,1,3 accept; 2,4 reject; blind admits 2,4.
    let p: Vec<u64> = (0u64..5).map(|c| run(0, c, 0)).collect();
    let pb: Vec<u64> = (0u64..5).map(|c| run(0, c, 1)).collect();
    // Ctor-return: 0,1 accept; 2,3,4 reject; blind admits 2,3,4.
    let c: Vec<u64> = (0u64..5).map(|c| run(1, c, 0)).collect();
    let cb: Vec<u64> = (0u64..5).map(|c| run(1, c, 1)).collect();
    // Elim: verdicts 10/11; blind flips 5.
    let e: Vec<u64> = (0u64..6).map(|c| run(2, c, 0)).collect();
    let eb: Vec<u64> = (0u64..6).map(|c| run(2, c, 1)).collect();
    println!("pos    ={:?}", p);
    println!("pos-bl ={:?}", pb);
    println!("ctor   ={:?}", c);
    println!("ctor-bl={:?}", cb);
    println!("elim   ={:?}", e);
    println!("elim-bl={:?}", eb);
    let ok = p == vec![0, 0, 1, 0, 1]
        && pb == vec![0, 0, 0, 0, 0]
        && c == vec![0, 0, 2, 3, 4]
        && cb == vec![0, 0, 0, 0, 0]
        && e == vec![10, 11, 11, 10, 10, 11]
        && eb == vec![10, 11, 11, 10, 10, 10];
    println!("SMOKE {}", if ok { "OK" } else { "FAIL" });
    std::process::exit((!ok) as i32);
}
