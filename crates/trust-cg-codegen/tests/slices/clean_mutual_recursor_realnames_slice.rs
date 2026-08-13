// R5 — the FULL mutual-recursor module over REAL NAMES: the landed
// clean_mutual_recursor_slice.rs (T3, verified native==JIT) with its Name(u32)
// + pre-interned RecPair-table model REPLACED by the production `Name`
// (NameInner Anon/Str/Num, Arc parent chain, Arc<str> payload, construction-time
// `cached_hash` via the real murmur/mix chain) — the follow-on named by round 4
// ("splice real Names into the full 431KB mutual-recursor module").
//
// WHAT CHANGED vs the landed u32 fixture (each at its definition):
//   * `Name`/`NameInner` — VERBATIM the production declarations (name.rs:150-159,
//     233-239) + the production `Hash for Name` (name.rs:461-465: O(1), writes
//     cached_hash). Construction chain (`name_anon`/`name_str_part`/
//     `name_num_part` = from_inner+compute_hash fused, name.rs:339-364, 483-527),
//     `murmur_hash_64a_idx` [T-murmur-idx], `parse_u64_ascii` [T-parse],
//     `fold_step` (= from_string_uncached's fold body), `str_bytes_eq` +
//     `name_eq` [T-eq-iter] — ALL VERBATIM the round-4 str_stage2_slice.rs
//     transcriptions (harness-proved bit-identical to the real clean-kernel).
//   * EVERY Name equality the construction performs is now the PRODUCTION
//     `Name::eq` (hash fast-path + full structural walk): `field_motive_index`,
//     `ctor_motive_index`, the `this_motive_idx` position scan, `name_in_set`,
//     the find-by-name loop, and the `minor_idx_offset` take_while all compare
//     through `name_eq` (`&a == &b` -> `name_eq(&a, &b)` — the production
//     PartialEq body transcribed as a free fn, same note as round 4).
//   * THE INTERNING IS DE-MODELED IN THE FULL MODULE: `rec_name_of` + the
//     caller-provided `&[RecPair]` table are GONE. `name_append_rec` transcribes
//     the production `Name::from_string(&format!("{name}.rec"))`
//     (inductive_recursor.rs:80 for the own rec name; inductive_recursor_rules.rs:213
//     for the mutual-branch IH) — see [T-append] at its definition.
//   * `fresh_univ_name` (inductive_fixed_indices.rs:276) now RUNS IN-MODULE on
//     its no-collision fast path (candidate "u" built from literal parts,
//     `existing.contains` -> name_eq scan); the u_1/u_2 suffix search needs
//     format! (gap 4) and is provably dead on the harness families. The
//     rec_level_params derivation ([u] ++ level_params, inductive_recursor.rs:96-99
//     non-prop arm) also runs in-module — both were MODELED-OUT INPUTS in the
//     u32 fixture.
//   * The mutual FAMILIES (Even/Odd; Tree/Forest) are now built IN-MODULE with
//     real Names from literal parts (`from_string_uncached` unrolled,
//     [T-unroll]) — no host-marshalled inputs at all: the roots take only
//     (family, which, sel)/(family, idx) scalars.
//   * `Level::Succ` now carries the PRODUCTION pointer type `LevelArc =
//     Arc<Level>` (level/mod.rs:32; the u32 fixture's Box<Level> was itself a
//     model — and Box::new is a known frontend gap while Arc::new lowers).
//     Level stays the 3-variant subset {Zero, Succ, Param} (Max/IMax
//     unconstructible on this path — same note as the landed fixture).
//
// MODELING boundaries that REMAIN (each documented at its definition):
//   * ExprMeta payload hashes (`hash_to_u64` family) still run through the
//     KaniHasher model (production non-kani uses DefaultHasher/SipHash13,
//     meta.rs:367-374) and the Const meta arm still hashes the name only
//     (production also mixes levels_hash — the landed T1 model, recorded
//     skeptic nuance). NOW the Name hash CONTENT is the real production
//     cached_hash (murmur/mix chain) flowing through that modeled hasher.
//     Next step for full de-modeling: transcribe SipHash13 + the levels_hash mix.
//   * `prop_only` (elim_only_at_universe_zero) is a MODELED INPUT = false —
//     separately native==JIT verified, and genuinely false for both harness
//     families (neither is Prop-valued).
//   * `HashSet<&Name>` -> Vec<Name> + name_eq scan (pure membership semantics —
//     exact: production Eq IS name_eq); `SmallVec<[Level;2]>` -> Vec<Level>;
//     `consume_type_annotations` -> no-op (no reserved wrapper Name on any
//     harness domain); `ctor_path_data` -> None (non-HIT families);
//     RecursorVal metadata (is_k etc.) not built. All unchanged from T3.
//   * `Arc<str>` crossings (`Arc::<str>::from`, deref, clone) and `Arc<Name>`/
//     `Arc<Level>` clone lower to extern decls bound to FAITHFUL host shims
//     (the landed convention); `Arc::new` + `Arc` deref are INLINED (RUNG 5/6).
//     wrapping/saturating arithmetic leaf externs as in every landed fixture.
//     Drops are not emitted (leak model — every Name/Expr immortal).
//
// Crate name is load-bearing (appears in the mangled extern symbols the JIT
// binds): it MUST stay `clean_mutual_recursor_realnames_slice`.
//
// Regen (one module per root; trust-ir main >= 375c800 — the landed stage-2
// string frontend; NO frontend changes this round):
//   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//   cd $HOME/trust-ir/frontend
//   env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//     $S/bin/cargo run --bin trust_ir_mir -- \
//     ../../trust-cg/crates/trust-cg-codegen/tests/slices/clean_mutual_recursor_realnames_slice.rs \
//     --crate-type=lib --mir-emit-closure <root> <out.tir>
//   roots: build_mutual_rec_realnames_root | realnames_name_probe_root
#![allow(dead_code)]
#![allow(clippy::all)]
#![allow(unused_variables)]

use std::sync::Arc;
use std::hash::{Hash, Hasher};
#[allow(unused_imports)]
use std::convert::TryFrom; // pre-2021 prelude (the MIR driver's edition) needs the explicit import

// ════════════════════════════════════════════════════════════════════════════
// clean-kernel name.rs — the production Name (VERBATIM declarations; round-4
// str_stage2_slice.rs transcriptions, harness-proved bit-identical).
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
/// construction-time cached_hash. This is the impl `hash_name`/`hash_level`
/// (Level::Param payloads) reach; the HASHER stays the KaniHasher model (see
/// header), but the CONTENT is now the real murmur/mix chain value.
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
// against BOTH the as-chunks oracle and clean-kernel golden constants): the
// production `as_chunks::<8>()` block iteration becomes an index loop
// assembling each 8-byte little-endian word; the tail fold's
// `.iter().enumerate()` becomes an index loop.

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

/// `Name::str(self, s)`: `from_inner(NameInner::Str(name_parent(Arc::new(self)),
/// Arc::from(s.as_ref())))` with `compute_hash(Str(p, s)) =
/// mix_hash(p.cached_hash, murmur_hash_64a(s.as_bytes(), 11))`.
/// [T-hash-src] production hashes the bytes read back out of the STORED
/// `Arc<str>`; this transcription hashes the SAME bytes from the incoming
/// `&str` (`Arc::from` copies them verbatim) — value-identical, and it keeps
/// the hash computation fully in-module (the Arc<str> read-back would cross
/// the deref shim).
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
/// (Note production `Name::from_string` IS `from_string_uncached` —
/// name.rs:578-581 — no interner on this path at all.)
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
// EVERY Name equality the recursor construction performs goes through this fn.

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

// ════════════════════════════════════════════════════════════════════════════
// THE DE-MODELED `.rec` DERIVATION — `Name::from_string(&format!("{name}.rec"))`
// (inductive_recursor.rs:80 — the own rec name; inductive_recursor_rules.rs:213
// — the mutual-branch IH rec name). No table, no pre-interned inputs.
//
// [T-append] The render->reparse is resolved at transcription time: production
// Display renders the chain dotted root-to-leaf and `from_string` re-folds the
// dotted string, so for every head whose parts round-trip (Str parts without
// '.' that do not parse as u64 — ALL heads this harness ever constructs:
// single-Str-part "Even"/"Odd"/"Tree"/"Forest"), the reparse rebuilds exactly
// the head's own chain and then appends the "rec" part. Value-identical
// (name_eq true, cached_hash bit-identical — proved against the real kernel:
// `Name::from_string("Tree").str("rec") == Name::from_string("Tree.rec")`,
// hash 0x293412c406e2a88e both ways) to continuing the fold on a clone of the
// head. Chain SHARING (the Arc parent points into head's chain instead of a
// fresh rebuild) is invisible to every downstream consumer — no pointer
// identity anywhere; same convention as round 4's rec_name_of_constructed.
// ════════════════════════════════════════════════════════════════════════════

pub fn name_append_rec(head: &Name) -> Name {
    fold_step(head.clone(), "rec")
}

// ════════════════════════════════════════════════════════════════════════════
// Modeled leaf payloads (FVarId/Level/Literal/BinderData). Level now carries
// the PRODUCTION `LevelArc = Arc<Level>` (level/mod.rs:32, non-kani) — the u32
// fixture's Box<Level> was a model. Variant subset {Zero, Succ, Param}
// unchanged (Max/IMax unconstructible on the recursor-construction path).
// ════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FVarId(pub u64);

#[derive(Clone, Debug, Hash)]
pub enum Level {
    Zero,
    Succ(Arc<Level>),
    Param(Name),
}

/// VERBATIM `level_arc` (level/mod.rs:36-40, non-kani): wrap a Level in the
/// production pointer type.
pub(crate) fn level_arc(l: Level) -> Arc<Level> {
    Arc::new(l)
}

impl Level {
    fn has_params(&self) -> bool {
        match self {
            Level::Zero => false,
            Level::Succ(l) => l.has_params(),
            Level::Param(_) => true,
        }
    }
}

type LevelVec = Vec<Level>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Literal {
    Nat(u64),
    Str(u32),
}

// BinderInfo::Default / Implicit modeled as the real `bd.info` byte (Default=0,
// Implicit=1). infer_implicit only ever compares against Default and constructs
// Implicit, so the two-variant model is faithful.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BinderData {
    pub info: u8,
    pub mult: u8,
}

impl BinderData {
    // VERBATIM `BinderData::new(info, mult)` (expr/types.rs:131).
    #[inline]
    fn new(info: u8, mult: u8) -> Self {
        BinderData { info, mult }
    }
}

// BinderInfo::Default / Implicit -> the scalar BinderData the real constructor stores.
// Built as RUNTIME locals (NOT `const` items): the real `Expr::pi(BinderInfo::Default,..)`
// passes a freshly-`Into`-converted `BinderData`, and the frontend lowers a struct-adt
// only as a runtime aggregate. These `#[inline]` fns return the same scalar pair as
// `BinderInfo::Default.into()` / `::Implicit.into()`.
#[inline]
fn bi_default() -> BinderData {
    BinderData { info: 0, mult: 0 }
}
#[inline]
fn bi_implicit() -> BinderData {
    BinderData { info: 1, mult: 0 }
}
// `BinderInfo::Default` used as a comparison value in infer_implicit / has_loose_bvars_in_domain.
const INFO_DEFAULT: u8 = 0;

// ════════════════════════════════════════════════════════════════════════════
// meta.rs — KaniHasher / hash_to_u64 / level_has_mvar (the MODELED payload
// hasher — see header; the Name content flowing through it is now the REAL
// cached_hash via the production `Hash for Name` above).
// ════════════════════════════════════════════════════════════════════════════

pub(crate) struct KaniHasher {
    state: u64,
}

impl KaniHasher {
    pub(crate) fn new() -> Self {
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
pub(crate) fn hash_to_u64<T: Hash>(value: &T) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[inline]
pub(crate) fn hash_name(value: &Name) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[inline]
pub(crate) fn hash_level(value: &Level) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[inline]
pub(crate) fn hash_lit(value: &Literal) -> u64 {
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[inline]
pub(crate) fn level_has_mvar(_level: &Level) -> bool {
    false
}

// ════════════════════════════════════════════════════════════════════════════
// meta.rs — VERBATIM ExprMeta (bit-packed u64) + pack + accessors + mk_*_meta.
// ════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Copy, Debug)]
pub(crate) struct ExprMeta(u64);

impl ExprMeta {
    const HASH_MASK: u64 = 0xFFFF_FFFF;
    const DEPTH_SHIFT: u32 = 32;
    const DEPTH_MASK: u64 = 0xFF;
    const HAS_FVAR_BIT: u32 = 40;
    const HAS_EXPR_MVAR_BIT: u32 = 41;
    const HAS_LEVEL_MVAR_BIT: u32 = 42;
    const HAS_LEVEL_PARAM_BIT: u32 = 43;
    const BVAR_RANGE_SHIFT: u32 = 44;
    pub(crate) const MAX_DEPTH: u32 = 255;
    pub(crate) const MAX_BVAR_RANGE: u32 = 1_048_575;

    #[inline]
    pub fn pack(
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

    #[inline]
    pub fn raw(self) -> u64 {
        self.0
    }
    #[inline]
    pub fn hash(self) -> u32 {
        (self.0 & Self::HASH_MASK) as u32
    }
    #[inline]
    pub fn approx_depth(self) -> u8 {
        ((self.0 >> Self::DEPTH_SHIFT) & Self::DEPTH_MASK) as u8
    }
    #[inline]
    pub fn has_fvar(self) -> bool {
        (self.0 >> Self::HAS_FVAR_BIT) & 1 == 1
    }
    #[inline]
    pub fn has_expr_mvar(self) -> bool {
        (self.0 >> Self::HAS_EXPR_MVAR_BIT) & 1 == 1
    }
    #[inline]
    pub fn has_level_mvar(self) -> bool {
        (self.0 >> Self::HAS_LEVEL_MVAR_BIT) & 1 == 1
    }
    #[inline]
    pub fn has_level_param(self) -> bool {
        (self.0 >> Self::HAS_LEVEL_PARAM_BIT) & 1 == 1
    }
    #[inline]
    pub fn loose_bvar_range(self) -> u32 {
        (self.0 >> Self::BVAR_RANGE_SHIFT) as u32
    }

    #[inline]
    pub fn mk_app_meta(f: ExprMeta, a: ExprMeta) -> ExprMeta {
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

    #[inline]
    pub fn mk_binder_meta(ty: ExprMeta, body: ExprMeta, extra_hash: u64) -> ExprMeta {
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

    #[inline]
    pub fn mk_let_meta(ty: ExprMeta, val: ExprMeta, body: ExprMeta) -> ExprMeta {
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

    #[inline]
    pub fn mk_wrapper_meta(inner: ExprMeta, extra_hash: u64) -> ExprMeta {
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

// ════════════════════════════════════════════════════════════════════════════
// kind.rs — ExprKind + compute_meta (construction arms VERBATIM; the Const arm
// keeps the landed T1 payload-hash model — see header — with the REAL Name
// hash content now flowing through hash_name).
// ════════════════════════════════════════════════════════════════════════════

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
}

impl ExprKind {
    pub(crate) fn compute_meta(&self) -> ExprMeta {
        match self {
            // ── CONSTRUCTION ARMS (reached by build_recursor_type) — VERBATIM ──
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
                // VERBATIM the real `levels.iter().any(|l| l.has_params())` — lowered to
                // the equivalent explicit loop. True iff any level is a Param; keeps the
                // has_level_param meta bit faithful for the Const(I/ctor, [Param(u)..]) nodes.
                let mut has_param = false;
                {
                    let mut _li = 0usize;
                    while _li < _levels.len() {
                        if _levels[_li].has_params() {
                            has_param = true;
                        }
                        _li += 1;
                    }
                }
                ExprMeta::pack(
                    mix_hash(5, name_hash) as u32,
                    0,
                    0,
                    false,
                    false,
                    false,
                    has_param,
                )
            }
            // ── LEAF ARMS (off this fn's construction path) — payload hash MODELED ──
            ExprKind::FVar(id) => {
                ExprMeta::pack(mix_hash(13, id.0) as u32, 0, 0, true, false, false, false)
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
                    mix_hash(
                        hash_name(name),
                        mix_hash(*idx as u64, inner.hash() as u64),
                    ),
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
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// mod.rs — VERBATIM Expr{kind,meta} + from_kind + accessors + constructors.
// ════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Debug)]
pub struct Expr {
    pub(crate) kind: ExprKind,
    pub(crate) meta: ExprMeta,
}

impl Expr {
    #[inline]
    pub fn from_kind(kind: ExprKind) -> Self {
        let meta = kind.compute_meta();
        Expr { kind, meta }
    }
    #[inline]
    pub(crate) fn meta(&self) -> ExprMeta {
        self.meta
    }
    #[inline]
    pub fn kind(&self) -> &ExprKind {
        &self.kind
    }
    #[inline]
    pub fn loose_bvar_range(&self) -> u32 {
        self.meta.loose_bvar_range()
    }

    // ── VERBATIM constructors (each builds via from_kind, Arc::new children). ──
    pub fn bvar(idx: u32) -> Self {
        Expr::from_kind(ExprKind::BVar(idx))
    }
    pub fn const_(name: Name, levels: LevelVec) -> Self {
        Expr::from_kind(ExprKind::Const(name, levels))
    }
    pub fn sort(level: Level) -> Self {
        Expr::from_kind(ExprKind::Sort(level))
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
}

// ════════════════════════════════════════════════════════════════════════════
// subst.rs / expr::mod.rs — VERBATIM de-Bruijn READS: lift_at (WRITE lift) +
// has_loose_bvar_in_range (the meta-guarded loose-bvar READ driving infer_implicit).
// ════════════════════════════════════════════════════════════════════════════

#[inline]
pub(crate) fn checked_add_u32(a: u32, b: u32) -> u32 {
    a.saturating_add(b)
}

// VERBATIM `bvar_in_range` (expr/mod.rs:94).
pub(crate) fn bvar_in_range(idx: u32, start: u32, end: u32) -> bool {
    if end == u32::MAX {
        idx >= start
    } else {
        idx >= start && idx < end
    }
}

// VERBATIM `shift_bvar_range` (expr/mod.rs:114). `checked_add_u32` -> saturating_add.
pub(crate) fn shift_bvar_range(start: u32, end: u32) -> Option<(u32, u32)> {
    if end != u32::MAX && start >= end {
        return None;
    }
    if start == u32::MAX {
        return None;
    }
    let next_start = checked_add_u32(start, 1);
    let next_end = if end == u32::MAX {
        u32::MAX
    } else {
        checked_add_u32(end, 1)
    };
    Some((next_start, next_end))
}

impl Expr {
    pub fn lift_at(&self, start: u32, amount: u32) -> Expr {
        if amount == 0 {
            return self.clone();
        }
        if start >= self.loose_bvar_range() {
            return self.clone();
        }
        match &self.kind {
            ExprKind::BVar(idx) => {
                if *idx >= start {
                    Expr::bvar(checked_add_u32(*idx, amount))
                } else {
                    self.clone()
                }
            }
            ExprKind::App(f, a) => Expr::app(f.lift_at(start, amount), a.lift_at(start, amount)),
            ExprKind::Lam(bd, ty, body) => Expr::lam(
                *bd,
                ty.lift_at(start, amount),
                body.lift_at(checked_add_u32(start, 1), amount),
            ),
            ExprKind::Pi(bd, ty, body) => Expr::pi(
                *bd,
                ty.lift_at(start, amount),
                body.lift_at(checked_add_u32(start, 1), amount),
            ),
            _ => self.clone(),
        }
    }

    // VERBATIM `Expr::lift` (subst.rs:495).
    pub fn lift(&self, amount: u32) -> Expr {
        self.lift_at(0, amount)
    }
    // VERBATIM `Expr::lift_from` (subst.rs:511).
    pub fn lift_from(&self, start: u32, amount: u32) -> Expr {
        self.lift_at(start, amount)
    }

    // VERBATIM `Expr::get_app_fn` (expr/constructors.rs:256) — the VERIFIED App-spine
    // head walk (reused by field_motive_index).
    pub fn get_app_fn(&self) -> &Expr {
        let mut current = self;
        while let ExprKind::App(f, _) = &current.kind {
            current = f;
        }
        current
    }

    // VERBATIM `Expr::has_loose_bvar` (subst.rs:547).
    pub fn has_loose_bvar(&self, idx: u32) -> bool {
        self.has_loose_bvar_in_range(idx, idx + 1)
    }

    // VERBATIM `Expr::has_loose_bvar_in_range` (subst.rs:595) — the real wraps
    // `has_loose_bvar_in_range_impl` in `stack_safe(||..)` (a maybe_grow that is a
    // no-op on these small trees); dropped, calling the impl directly.
    pub fn has_loose_bvar_in_range(&self, start: u32, end: u32) -> bool {
        self.has_loose_bvar_in_range_impl(start, end)
    }

    // VERBATIM `has_loose_bvar_in_range_impl` (subst.rs:601). Only the modeled ExprKind
    // arms are present (the CubicalPath/MData/SProp/Squash/... arms are unconstructible
    // in this slice; the `_ => false` on leaves matches the real FVar/Sort/Const/Lit).
    fn has_loose_bvar_in_range_impl(&self, start: u32, end: u32) -> bool {
        if end != u32::MAX && start >= end {
            return false;
        }
        // O(1) metadata guard: all loose BVar indices are < loose_bvar_range(),
        // so if loose_bvar_range() <= start, no BVars exist in [start, end).
        if self.loose_bvar_range() <= start {
            return false;
        }
        match &self.kind {
            ExprKind::BVar(idx) => bvar_in_range(*idx, start, end),
            ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Const(_, _) | ExprKind::Lit(_) => {
                false
            }
            ExprKind::App(f, a) => {
                f.has_loose_bvar_in_range(start, end) || a.has_loose_bvar_in_range(start, end)
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                let body_has_loose = match shift_bvar_range(start, end) {
                    Some((next_start, next_end)) => {
                        body.has_loose_bvar_in_range(next_start, next_end)
                    }
                    None => false,
                };
                ty.has_loose_bvar_in_range(start, end) || body_has_loose
            }
            ExprKind::Let(_, ty, val, body, _) => {
                let body_has_loose = match shift_bvar_range(start, end) {
                    Some((next_start, next_end)) => {
                        body.has_loose_bvar_in_range(next_start, next_end)
                    }
                    None => false,
                };
                ty.has_loose_bvar_in_range(start, end)
                    || val.has_loose_bvar_in_range(start, end)
                    || body_has_loose
            }
            ExprKind::Proj(_, _, e) => e.has_loose_bvar_in_range(start, end),
        }
    }

    // VERBATIM `infer_implicit` (subst.rs:560) — strict-mode wrapper over infer_implicit_n.
    pub fn infer_implicit(&self, strict: bool) -> Expr {
        self.infer_implicit_n(u32::MAX, strict)
    }

    // VERBATIM `infer_implicit_n` (subst.rs:567). `bd.info != BinderInfo::Default`
    // -> `bd.info != INFO_DEFAULT`; `BinderData::new(BinderInfo::Implicit, bd.mult)`
    // -> `BinderData::new(1, bd.mult)`.
    pub fn infer_implicit_n(&self, num_params: u32, strict: bool) -> Expr {
        if num_params == 0 {
            return self.clone();
        }
        match &self.kind {
            ExprKind::Pi(bd, domain, body) => {
                let new_body = body.infer_implicit_n(num_params - 1, strict);
                if bd.info != INFO_DEFAULT {
                    // Already non-explicit — keep as-is, just update body
                    Expr::pi(*bd, (**domain).clone(), new_body)
                } else if has_loose_bvars_in_domain(&new_body, 0, strict) {
                    // BVar 0 appears in a subsequent domain — mark implicit
                    Expr::pi(
                        BinderData::new(1, bd.mult),
                        (**domain).clone(),
                        new_body,
                    )
                } else {
                    Expr::pi(*bd, (**domain).clone(), new_body)
                }
            }
            _ => self.clone(),
        }
    }
}

// VERBATIM `has_loose_bvars_in_domain` (expr/mod.rs:140). `bd.info == BinderInfo::Default`
// -> `bd.info == INFO_DEFAULT`.
pub(crate) fn has_loose_bvars_in_domain(b: &Expr, vidx: u32, strict: bool) -> bool {
    match &b.kind {
        ExprKind::Pi(bd, domain, body) => {
            if domain.has_loose_bvar(vidx) {
                if bd.info == INFO_DEFAULT {
                    // vidx appears in an explicit argument's domain
                    return true;
                } else if has_loose_bvars_in_domain(body, 0, strict) {
                    // Transitivity
                    return true;
                }
            }
            has_loose_bvars_in_domain(body, vidx + 1, strict)
        }
        _ => {
            if !strict {
                b.has_loose_bvar(vidx)
            } else {
                false
            }
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// MODELED InductiveType — the struct build_recursor_type reads via `all_types`:
//   .name (ctor_motive_index / this_motive_idx / field_motive_index),
//   .type_ (count_pi_args / collect_pi_binders_after_skip for the motive-type builder),
//   .constructors (ctor_path_data — HIT check, modeled to return None).
// Names inside are now REAL production Names.
// ════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Debug)]
pub struct Ctor {
    pub name: Name,
    pub type_: Expr,
}

#[derive(Clone, Debug)]
pub struct InductiveType {
    pub name: Name,
    pub type_: Expr,
    pub constructors: Vec<Ctor>,
}

// VERBATIM `ind_const_with_levels` (inductive_fixed_indices.rs:266):
//   `levels = level_params.iter().map(|p| Level::param(p.clone())).collect();
//    Expr::const_(name.clone(), levels)`
// — map lowered to the equivalent push loop; the clones are now REAL Name
// clones (Arc refcount bumps), exactly the production text.
pub(crate) fn ind_const_with_levels(name: &Name, level_params: &[Name]) -> Expr {
    let mut levels: Vec<Level> = Vec::new();
    {
        let mut _i = 0usize;
        while _i < level_params.len() {
            levels.push(Level::Param(level_params[_i].clone()));
            _i += 1;
        }
    }
    Expr::const_(name.clone(), levels)
}

// VERBATIM `get_return_type` (inductive/mod.rs:650) — walk past the Pi telescope.
pub(crate) fn get_return_type(expr: &Expr) -> &Expr {
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = &current.kind {
        current = body;
    }
    current
}

// ════════════════════════════════════════════════════════════════════════════
// The Environment-method PILLARS transcribed as free fns over the modeled types.
// ════════════════════════════════════════════════════════════════════════════

#[inline]
fn usize_to_u32(value: usize) -> u32 {
    u32::try_from(value).unwrap_or(u32::MAX)
}

// VERBATIM `count_pi_args` (inductive/mod.rs:608).
pub(crate) fn count_pi_args(expr: &Expr) -> u32 {
    let mut count = 0u32;
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = &current.kind {
        count = count.saturating_add(1);
        current = body;
    }
    count
}

// MODELED `consume_type_annotations` (inductive/mod.rs:676). The real fn peels
// optParam/autoParam (arity-2) and outParam/semiOutParam (arity-1) wrapper Consts by
// comparing `name.to_string()` to those literals. No synthetic domain in this slice uses
// a reserved wrapper Name, so the scan is a faithful no-op returning its input unchanged.
// (The `to_string` render is format machinery — gap 4; still modeled out.)
pub(crate) fn consume_type_annotations(expr: &Expr) -> &Expr {
    expr
}

// VERBATIM `field_motive_index` (inductive_recursor_types.rs:45). The Name
// equality `&ind_type.name == name` is the production PartialEq — `name_eq`.
pub(crate) fn field_motive_index(field_ty: &Expr, all_types: &[InductiveType]) -> usize {
    let ret_ty = get_return_type(field_ty);
    let head = ret_ty.get_app_fn();
    if let ExprKind::Const(name, _) = &head.kind {
        // VERBATIM `for (idx, ind_type) in all_types.iter().enumerate()` — index loop.
        let mut idx = 0usize;
        while idx < all_types.len() {
            if name_eq(&all_types[idx].name, name) {
                return idx;
            }
            idx += 1;
        }
    }
    0
}

// VERBATIM `ctor_motive_index` (inductive_recursor_types.rs:28). `&ctor.name ==
// ctor_name` -> production PartialEq -> `name_eq`.
pub(crate) fn ctor_motive_index(ctor_name: &Name, all_types: &[InductiveType]) -> usize {
    // VERBATIM `for (idx, ind_type) in all_types.iter().enumerate()` — index loops.
    let mut idx = 0usize;
    while idx < all_types.len() {
        let mut ci = 0usize;
        while ci < all_types[idx].constructors.len() {
            if name_eq(&all_types[idx].constructors[ci].name, ctor_name) {
                return idx;
            }
            ci += 1;
        }
        idx += 1;
    }
    0
}

// MODELED `ctor_path_data` (inductive_recursor_minor.rs:175). The real fn returns
// `Some((left,right))` ONLY when a ctor's return type is `ExprKind::CubicalPath{..}`
// (a HIT path ctor). The modeled ExprKind has NO CubicalPath variant and every test
// inductive is non-HIT, so this ALWAYS returns None — the is_path / path-minor branch
// is provably dead on every verified case.
pub(crate) fn ctor_path_data(
    _ctor_name: &Name,
    _all_types: &[InductiveType],
) -> Option<(Expr, Expr)> {
    None
}

// VERBATIM `count_pi_binders` (inductive_recursor_rules.rs:24).
pub(crate) fn count_pi_binders(expr: &Expr) -> usize {
    let mut count = 0;
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = &current.kind {
        count += 1;
        current = body;
    }
    count
}

// VERBATIM `collect_pi_domains` (inductive_recursor_rules.rs:39).
pub(crate) fn collect_pi_domains(expr: &Expr) -> Vec<(BinderData, Expr)> {
    let mut domains = Vec::new();
    let mut current = expr;
    while let ExprKind::Pi(bi, domain, body) = &current.kind {
        domains.push((*bi, (**domain).clone()));
        current = body;
    }
    domains
}

// VERBATIM `collect_pi_binders` (inductive_recursor.rs:988). The real collects through
// `consume_type_annotations(domain)` (modeled no-op).
pub(crate) fn collect_pi_binders(ty: &Expr, count: u32) -> Vec<(BinderData, Expr)> {
    let mut result = Vec::new();
    let mut current = ty.clone();
    let mut collected = 0u32;
    while collected < count {
        if let ExprKind::Pi(bi, domain, codomain) = &current.kind {
            result.push((*bi, consume_type_annotations(domain).clone()));
            current = (**codomain).clone();
            collected += 1;
        } else {
            break;
        }
    }
    result
}

// VERBATIM `collect_pi_binders_after_skip` (inductive_recursor_types.rs:510).
pub(crate) fn collect_pi_binders_after_skip(
    ty: &Expr,
    skip: u32,
    count: u32,
) -> Vec<(BinderData, Expr)> {
    let mut current = ty.clone();
    {
        let mut _s = 0u32;
        while _s < skip {
            if let ExprKind::Pi(_, _, body) = &current.kind {
                current = (**body).clone();
            }
            _s += 1;
        }
    }
    collect_pi_binders(&current, count)
}

// VERBATIM `get_constructor_return_indices` (inductive_recursor.rs:951).
pub(crate) fn get_constructor_return_indices(ctor_ty: &Expr, num_params: u32) -> Vec<Expr> {
    let mut current = ctor_ty.clone();
    while let ExprKind::Pi(_, _, codomain) = &current.kind {
        current = (**codomain).clone();
    }
    let mut args: Vec<Expr> = Vec::new();
    while let ExprKind::App(f, a) = &current.kind {
        args.push((**a).clone());
        current = (**f).clone();
    }
    // args collected rightmost-first; VERBATIM `args.reverse()` then
    // `.into_iter().skip(num_params).collect()` — single forward emit over the reversed
    // (source-order) indices, skipping the first num_params.
    let np = num_params as usize;
    let n = args.len();
    let mut out: Vec<Expr> = Vec::new();
    {
        let mut s = 0usize;
        while s < n {
            if s >= np {
                out.push(args[n - 1 - s].clone());
            }
            s += 1;
        }
    }
    out
}

// VERBATIM `remap_residual_index_bvars_for_minor` (inductive_recursor_rules.rs:94).
pub(crate) fn remap_residual_index_bvars_for_minor(
    expr: &Expr,
    field_idx: usize,
    nf: usize,
    ih_offset: usize,
    n_pis: usize,
) -> Expr {
    match &expr.kind {
        ExprKind::BVar(k) => {
            let k = *k as usize;
            let new_k = if k < n_pis {
                k
            } else {
                let ctor_k = k - n_pis;
                if ctor_k < field_idx {
                    let field_j = field_idx - 1 - ctor_k;
                    ih_offset + nf - 1 - field_j + n_pis
                } else {
                    let param_j = ctor_k - field_idx;
                    ih_offset + nf + 1 + param_j + n_pis
                }
            };
            Expr::bvar(usize_to_u32(new_k))
        }
        ExprKind::App(f, a) => {
            let f2 = remap_residual_index_bvars_for_minor(f, field_idx, nf, ih_offset, n_pis);
            let a2 = remap_residual_index_bvars_for_minor(a, field_idx, nf, ih_offset, n_pis);
            Expr::app(f2, a2)
        }
        _ => expr.clone(),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// VERIFIED PILLAR — `build_minor_premise_type`, VERBATIM from
// inductive_recursor_minor.rs:33 (native==JIT verified in T3; unchanged except
// the Name clones are now real). `BinderInfo::Default` -> `bi_default()`.
// ════════════════════════════════════════════════════════════════════════════

#[allow(clippy::too_many_arguments)]
pub fn build_minor_premise_type(
    ind_name: &Name,
    ctor_name: &Name,
    num_fields: u32,
    recursive_flags: &[bool],
    field_types: &[Expr],
    num_params: u32,
    ind_level_params: &[Name],
    ctor_indices: &[Expr],
    num_motives: usize,
    conclusion_motive_idx: usize,
    all_types: &[InductiveType],
) -> Expr {
    // VERBATIM `recursive_flags.iter().filter(|&&b| b).count()` — explicit count loop.
    let mut num_ihs: usize = 0;
    {
        let mut _ci = 0usize;
        while _ci < recursive_flags.len() {
            if recursive_flags[_ci] {
                num_ihs += 1;
            }
            _ci += 1;
        }
    }
    let num_fields = num_fields as usize;

    let conclusion_motive_bvar =
        num_fields + num_ihs + (num_motives - 1 - conclusion_motive_idx);

    let adjust_index_expr = |expr: Expr, ih_offset: usize| -> Expr {
        let mut adjusted = expr.lift(usize_to_u32(ih_offset));
        adjusted = adjusted.lift_from(
            usize_to_u32(ih_offset + num_fields),
            num_motives as u32,
        );
        adjusted
    };

    // VERBATIM `ind_level_params.iter().map(|p| Level::param(p.clone())).collect()`.
    let mut ctor_levels: Vec<Level> = Vec::new();
    {
        let mut _pi = 0usize;
        while _pi < ind_level_params.len() {
            ctor_levels.push(Level::Param(ind_level_params[_pi].clone()));
            _pi += 1;
        }
    }
    let mut ctor_app = Expr::const_(ctor_name.clone(), ctor_levels);
    {
        let mut i: u32 = 0;
        while i < num_params {
            let param_depth =
                num_fields + num_ihs + num_motives + (num_params as usize - 1 - i as usize);
            ctor_app = Expr::app(ctor_app, Expr::bvar(usize_to_u32(param_depth)));
            i += 1;
        }
    }
    {
        let mut i: usize = 0;
        while i < num_fields {
            let field_depth = (num_fields - 1 - i) + num_ihs;
            ctor_app = Expr::app(ctor_app, Expr::bvar(usize_to_u32(field_depth)));
            i += 1;
        }
    }

    let mut result = Expr::bvar(usize_to_u32(conclusion_motive_bvar));
    {
        let mut _ii = 0usize;
        while _ii < ctor_indices.len() {
            let adjusted = adjust_index_expr(ctor_indices[_ii].clone(), num_ihs);
            result = Expr::app(result, adjusted);
            _ii += 1;
        }
    }
    result = Expr::app(result, ctor_app);

    let mut ih_offset = 0usize;
    let mut _ri = recursive_flags.len();
    while _ri > 0 {
        _ri -= 1;
        let i = _ri;
        let is_recursive = recursive_flags[i];
        if is_recursive {
            let ihs_above = num_ihs - 1 - ih_offset;
            let field_depth = (num_fields - 1 - i) + ihs_above;

            let ih_motive_idx = match field_types.get(i) {
                Some(ft) => field_motive_index(ft, all_types),
                None => conclusion_motive_idx,
            };
            let motive_at_ih = num_fields + ihs_above + (num_motives - 1 - ih_motive_idx);

            let n_pis = match field_types.get(i) {
                Some(ft) => count_pi_binders(ft),
                None => 0,
            };

            let ih_motive = motive_at_ih + n_pis;
            let ih_field_depth = field_depth + n_pis;

            let mut ih_type = Expr::bvar(usize_to_u32(ih_motive));

            let field_ty = match field_types.get(i) {
                Some(ft) => ft.clone(),
                None => ind_const_with_levels(ind_name, ind_level_params),
            };
            let field_indices = get_constructor_return_indices(&field_ty, num_params);
            {
                let mut _fi = 0usize;
                while _fi < field_indices.len() {
                    let remapped = remap_residual_index_bvars_for_minor(
                        &field_indices[_fi], i, num_fields, ihs_above, n_pis,
                    );
                    ih_type = Expr::app(ih_type, remapped);
                    _fi += 1;
                }
            }

            let mut major = Expr::bvar(usize_to_u32(ih_field_depth));
            {
                let mut _k = n_pis;
                while _k > 0 {
                    _k -= 1;
                    major = Expr::app(major, Expr::bvar(usize_to_u32(_k)));
                }
            }
            ih_type = Expr::app(ih_type, major);

            let pi_domains = match field_types.get(i) {
                Some(ft) => collect_pi_domains(ft),
                None => Vec::new(),
            };
            {
                let mut _pd = pi_domains.len();
                while _pd > 0 {
                    _pd -= 1;
                    let k = _pd;
                    let (bi, domain) = &pi_domains[k];
                    let remapped = remap_residual_index_bvars_for_minor(
                        domain, i, num_fields, ihs_above, k,
                    );
                    ih_type = Expr::pi(*bi, remapped, ih_type);
                }
            }

            result = Expr::pi(bi_default(), ih_type, result);
            ih_offset += 1;
        }
    }

    {
        let mut _fb = num_fields;
        while _fb > 0 {
            _fb -= 1;
            let i = _fb;
            let field_ty = match field_types.get(i) {
                Some(ft) => ft.clone(),
                None => ind_const_with_levels(ind_name, ind_level_params),
            };
            let lifted_field_ty = field_ty.lift_from(usize_to_u32(i), num_motives as u32);
            result = Expr::pi(bi_default(), lifted_field_ty, result);
        }
    }

    result
}

// ════════════════════════════════════════════════════════════════════════════
// THE SOUNDNESS-CRITICAL FN — `build_recursor_type`, VERBATIM from
// inductive_recursor_types.rs:89 (native==JIT verified in T3). `&self` dropped
// (used only to reach helpers transcribed above). The `build_ind_app` closure
// is preserved verbatim. `motive_univ = Level::param(name.clone())` and the
// `this_motive_idx` position scan now run over REAL Names (`name_eq`).
//
// A CtorInfo is `(ctor_name, num_fields, recursive_flags, field_types, return_indices)`.
// ════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Debug)]
pub struct CtorInfo {
    pub name: Name,
    pub num_fields: u32,
    pub recursive_flags: Vec<bool>,
    pub field_types: Vec<Expr>,
    pub return_indices: Vec<Expr>,
}

#[allow(clippy::too_many_arguments)]
pub fn build_recursor_type(
    ind_name: &Name,
    ind_type: &Expr,
    num_params: u32,
    num_indices: u32,
    motive_univ_name: Option<&Name>,
    ind_level_params: &[Name],
    ctor_infos: &[CtorInfo],
    all_types: &[InductiveType],
) -> Expr {
    // Prop-only elimination: motive targets Sort 0 (Prop). Large elimination: Sort u.
    // VERBATIM `match motive_univ_name { Some(name) => Level::param(name.clone()),
    //   None => Level::zero() }`.
    let motive_univ = match motive_univ_name {
        Some(name) => Level::Param(name.clone()),
        None => Level::Zero,
    };
    let ind_const = ind_const_with_levels(ind_name, ind_level_params);

    let num_motives = all_types.len();

    // Collect parameter and index binders from the inductive type.
    let param_binders = collect_pi_binders(ind_type, num_params);
    let mut current = ind_type.clone();
    {
        let mut _p = 0u32;
        while _p < num_params {
            if let ExprKind::Pi(_, _, body) = &current.kind {
                current = (**body).clone();
            }
            _p += 1;
        }
    }
    let index_binders = collect_pi_binders(&current, num_indices);
    let num_minors = ctor_infos.len();

    // Helper to build Ind applied to params and indices at given depths (VERBATIM closure).
    let build_ind_app = |param_offset: u32, index_offset: u32| -> Expr {
        let mut ind_app = ind_const.clone();
        {
            let mut i: u32 = 0;
            while i < num_params {
                let idx = param_offset + (num_params - 1 - i);
                ind_app = Expr::app(ind_app, Expr::bvar(idx));
                i += 1;
            }
        }
        {
            let mut i: u32 = 0;
            while i < num_indices {
                let idx = index_offset + (num_indices - 1 - i);
                ind_app = Expr::app(ind_app, Expr::bvar(idx));
                i += 1;
            }
        }
        ind_app
    };

    // Build motive types for ALL types in the mutual block.
    // Each motive: Π indices_i, Π (major : Type_i indices_i), Sort u.
    let mut motive_types: Vec<Expr> = Vec::with_capacity(num_motives);
    {
        let mut _t = 0usize;
        while _t < all_types.len() {
            let t = &all_types[_t];
            let t_const = ind_const_with_levels(&t.name, ind_level_params);
            let t_type_arity = count_pi_args(&t.type_);
            let t_num_indices = t_type_arity.saturating_sub(num_params);
            let t_index_binders =
                collect_pi_binders_after_skip(&t.type_, num_params, t_num_indices);

            let mut mtype = Expr::from_kind(ExprKind::Sort(motive_univ.clone()));
            // major type: Type_i params indices
            let mut major_ty_for_motive = t_const.clone();
            {
                let mut i: u32 = 0;
                while i < num_params {
                    let idx = t_num_indices + (num_params - 1 - i);
                    major_ty_for_motive = Expr::app(major_ty_for_motive, Expr::bvar(idx));
                    i += 1;
                }
            }
            {
                let mut i: u32 = 0;
                while i < t_num_indices {
                    let idx = t_num_indices - 1 - i;
                    major_ty_for_motive = Expr::app(major_ty_for_motive, Expr::bvar(idx));
                    i += 1;
                }
            }
            mtype = Expr::pi(bi_default(), major_ty_for_motive, mtype);
            // Add the index binders, outermost (idx_0) last. Each I_i placed UNCHANGED
            // (see the real comment: the standalone-motive and inductive-telescope
            // contexts are identical; a previous over-shift was the multi-index bug).
            // VERBATIM `for (binder_info, index_ty) in t_index_binders.iter().rev()`.
            {
                let mut _ib = t_index_binders.len();
                while _ib > 0 {
                    _ib -= 1;
                    let (binder_info, index_ty) = &t_index_binders[_ib];
                    mtype = Expr::pi(*binder_info, index_ty.clone(), mtype);
                }
            }
            motive_types.push(mtype);
            _t += 1;
        }
    }

    // Determine which motive index corresponds to ind_name.
    // VERBATIM `all_types.iter().position(|t| &t.name == ind_name).unwrap_or(0)` —
    // the Name equality is the production PartialEq (`name_eq`).
    let this_motive_idx = {
        let mut found: Option<usize> = None;
        let mut _i = 0usize;
        while _i < all_types.len() {
            if name_eq(&all_types[_i].name, ind_name) {
                found = Some(_i);
                break;
            }
            _i += 1;
        }
        match found {
            Some(v) => v,
            None => 0,
        }
    };

    // Build minor premise types. Each entry is (type, is_path).
    let mut minor_types: Vec<(Expr, bool)> = Vec::new();
    {
        let mut minor_self_idx = 0usize;
        while minor_self_idx < ctor_infos.len() {
            let ci = &ctor_infos[minor_self_idx];
            let ctor_name = &ci.name;
            let num_fields = ci.num_fields;
            let recursive_flags = &ci.recursive_flags;
            let field_types = &ci.field_types;
            let return_indices = &ci.return_indices;

            let ctor_motive_idx = ctor_motive_index(ctor_name, all_types);
            match ctor_path_data(ctor_name, all_types) {
                Some(_lr) => {
                    // Provably dead on every non-HIT test case (ctor_path_data == None).
                    // Path-minor construction is NOT modeled; unreachable here.
                    minor_types.push((Expr::bvar(0), true));
                }
                None => {
                    let minor_ty = build_minor_premise_type(
                        ind_name,
                        ctor_name,
                        num_fields,
                        recursive_flags,
                        field_types,
                        num_params,
                        ind_level_params,
                        return_indices,
                        num_motives,
                        ctor_motive_idx,
                        all_types,
                    );
                    minor_types.push((minor_ty, false));
                }
            }
            minor_self_idx += 1;
        }
    }

    // Build the full rec type from inside out:
    // params → motives → minors → indices → major → motive_i indices major
    let this_motive_bvar = usize_to_u32(
        num_minors + num_indices as usize + 1 + (num_motives - 1 - this_motive_idx),
    );
    let mut result_ty = Expr::bvar(this_motive_bvar);
    {
        let mut i: u32 = 0;
        while i < num_indices {
            let idx = usize_to_u32(num_indices as usize - i as usize);
            result_ty = Expr::app(result_ty, Expr::bvar(idx));
            i += 1;
        }
    }
    result_ty = Expr::app(result_ty, Expr::bvar(0)); // major

    // Add major premise: (t : Ind params indices) → result.
    let major_ty = build_ind_app(num_indices + num_minors as u32 + num_motives as u32, 0);
    result_ty = Expr::pi(bi_default(), major_ty, result_ty);

    // Add index binders. Param-referencing BVars shifted by (num_minors + num_motives).
    // VERBATIM `for (i, (binder_info, index_ty)) in index_binders.iter().enumerate().rev()`.
    let extra = usize_to_u32(num_minors + num_motives);
    {
        let mut _ix = index_binders.len();
        while _ix > 0 {
            _ix -= 1;
            let i = _ix;
            let (binder_info, index_ty) = &index_binders[i];
            let lifted_index_ty = if extra > 0 {
                index_ty.lift_from(i as u32, extra)
            } else {
                index_ty.clone()
            };
            result_ty = Expr::pi(*binder_info, lifted_index_ty, result_ty);
        }
    }

    // Add minor premises (reverse order). Each minor's BVars reference the motives; a
    // non-path minor at index i is lifted by i. Path minors (dead here) skip the lift.
    // VERBATIM `for (i, (minor_ty, is_path)) in minor_types.iter().enumerate().rev()`.
    {
        let mut _m = minor_types.len();
        while _m > 0 {
            _m -= 1;
            let i = _m;
            let (minor_ty, is_path) = &minor_types[i];
            let lifted_minor_ty = if *is_path || i == 0 {
                minor_ty.clone()
            } else {
                minor_ty.lift(usize_to_u32(i))
            };
            result_ty = Expr::pi(bi_default(), lifted_minor_ty, result_ty);
        }
    }

    // Add motives (innermost motive last). Motive_i lifted by i.
    // VERBATIM `for (i, mtype) in motive_types.iter().enumerate().rev()`.
    {
        let mut _mo = motive_types.len();
        while _mo > 0 {
            _mo -= 1;
            let i = _mo;
            let mtype = &motive_types[i];
            let lifted_mtype = if i > 0 {
                mtype.lift(usize_to_u32(i))
            } else {
                mtype.clone()
            };
            result_ty = Expr::pi(bi_implicit(), lifted_mtype, result_ty);
        }
    }

    // Add parameters (outermost).
    // VERBATIM `for (_i, (binder_info, param_ty)) in param_binders.iter().enumerate().rev()`.
    {
        let mut _pb = param_binders.len();
        while _pb > 0 {
            _pb -= 1;
            let (binder_info, param_ty) = &param_binders[_pb];
            result_ty = Expr::pi(*binder_info, param_ty.clone(), result_ty);
        }
    }

    // infer_implicit: mark explicit binders Implicit when their bvar appears in a
    // subsequent Pi domain (strict). Ref: lean4-ref/src/kernel/inductive.cpp:767.
    result_ty = result_ty.infer_implicit(true);

    result_ty
}

// ════════════════════════════════════════════════════════════════════════════
// VERBATIM `remap_residual_index_bvars` (inductive_recursor_rules.rs:51) — the
// NON-minor variant (distinct arithmetic from _for_minor), used by the rule RHS.
// ════════════════════════════════════════════════════════════════════════════

pub(crate) fn remap_residual_index_bvars(
    expr: &Expr,
    field_idx: usize,
    np: usize,
    nf: usize,
    n_minors: usize,
    nm: usize,
    n_pis: usize,
) -> Expr {
    match &expr.kind {
        ExprKind::BVar(k) => {
            let k = *k as usize;
            let new_k = if k < n_pis {
                k
            } else {
                let ctor_k = k - n_pis;
                if ctor_k < field_idx {
                    let field_j = field_idx - 1 - ctor_k;
                    nf - 1 - field_j + n_pis
                } else {
                    let param_j = np - 1 - (ctor_k - field_idx);
                    nf + n_minors + nm + np - 1 - param_j + n_pis
                }
            };
            Expr::bvar(usize_to_u32(new_k))
        }
        ExprKind::App(f, a) => {
            let f2 = remap_residual_index_bvars(f, field_idx, np, nf, n_minors, nm, n_pis);
            let a2 = remap_residual_index_bvars(a, field_idx, np, nf, n_minors, nm, n_pis);
            Expr::app(f2, a2)
        }
        _ => expr.clone(),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// THE SOUNDNESS-CRITICAL FN — `build_recursor_rule_rhs`, VERBATIM from
// inductive_recursor_rules.rs:148, INCLUDING the `all_types.len() > 1` MUTUAL
// branch — NOW WITH THE REAL DERIVATION: `Name::from_string(&format!("{name}.rec"))`
// runs as `name_append_rec` ([T-append]) over the REAL head Name pulled out of
// the field's return type — no table, no pre-interned inputs. `&self` dropped;
// `BinderInfo::Default` -> bi_default(); SmallVec -> Vec (modeled, see header).
// ════════════════════════════════════════════════════════════════════════════

#[allow(clippy::too_many_arguments)]
pub fn build_recursor_rule_rhs(
    rec_name: &Name,
    rec_level_params: &[Name],
    num_params: u32,
    num_motives: u32,
    num_indices: u32,
    num_fields: u32,
    recursive_flags: &[bool],
    field_types: &[Expr],
    num_ctors: usize,
    ctor_idx: usize,
    eliminator_type: &Expr,
    all_types: &[InductiveType],
) -> Expr {
    let nf = num_fields as usize;
    let np = num_params as usize;
    let nm = num_motives as usize;
    let n_minors = num_ctors; // num_minors == num_ctors for standard rec
    let total_binders = np + nm + n_minors + nf;

    // minor for ctor_idx (minors go minor_0 outermost .. minor_{n-1} innermost).
    let minor_bvar = usize_to_u32(nf + n_minors - 1 - ctor_idx);
    let mut body = Expr::bvar(minor_bvar);

    // Apply all fields to minor: minor field_0 .. field_{nf-1}.
    // VERBATIM `for i in 0..nf` — ascending while loop.
    {
        let mut i: usize = 0;
        while i < nf {
            let field_bvar = usize_to_u32(nf - 1 - i);
            body = Expr::app(body, Expr::bvar(field_bvar));
            i += 1;
        }
    }

    // rec_levels = rec_level_params.iter().map(|n| Level::param(n.clone())).collect()
    // VERBATIM — explicit push loop (SmallVec -> Vec, modeled).
    let mut rec_levels: Vec<Level> = Vec::new();
    {
        let mut _li = 0usize;
        while _li < rec_level_params.len() {
            rec_levels.push(Level::Param(rec_level_params[_li].clone()));
            _li += 1;
        }
    }

    // Apply IH for each recursive field.
    // VERBATIM `for (i, &is_recursive) in recursive_flags.iter().enumerate()`.
    {
        let mut i: usize = 0;
        while i < recursive_flags.len() {
            let is_recursive = recursive_flags[i];
            if is_recursive {
                let n_pis = match field_types.get(i) {
                    Some(ft) => count_pi_binders(ft),
                    None => 0,
                };
                let shift = n_pis;

                // THE MUTUAL BRANCH — VERBATIM control flow (rules.rs:208-222):
                // for a mutual block the IH names the recursor of the type the
                // field RETURNS TO (Lean 4 inductive.cpp:738). The
                // `Name::from_string(&format!("{name}.rec"))` step is now the
                // REAL in-module derivation ([T-append]); the else arms are the
                // production `rec_name.clone()`.
                let ih_rec_name = if all_types.len() > 1 {
                    match field_types.get(i) {
                        Some(field_ty) => {
                            let ret_ty = get_return_type(field_ty);
                            let head = ret_ty.get_app_fn();
                            match &head.kind {
                                ExprKind::Const(name, _) => name_append_rec(name),
                                _ => rec_name.clone(),
                            }
                        }
                        None => rec_name.clone(),
                    }
                } else {
                    rec_name.clone()
                };

                // ih = ih_rec@{levels} params motives minors [indices] (field xs)
                let mut ih = Expr::const_(ih_rec_name, rec_levels.clone());

                // Apply params (outermost group). VERBATIM `for j in 0..np`.
                {
                    let mut j: usize = 0;
                    while j < np {
                        let param_bvar = usize_to_u32(total_binders - 1 - j + shift);
                        ih = Expr::app(ih, Expr::bvar(param_bvar));
                        j += 1;
                    }
                }
                // Apply motives.
                {
                    let mut j: usize = 0;
                    while j < nm {
                        let motive_bvar = usize_to_u32(nf + n_minors + nm - 1 - j + shift);
                        ih = Expr::app(ih, Expr::bvar(motive_bvar));
                        j += 1;
                    }
                }
                // Apply minors.
                {
                    let mut j: usize = 0;
                    while j < n_minors {
                        let minor_bvar_idx = usize_to_u32(nf + n_minors - 1 - j + shift);
                        ih = Expr::app(ih, Expr::bvar(minor_bvar_idx));
                        j += 1;
                    }
                }

                // Apply index arguments for indexed inductives.
                if num_indices > 0 {
                    if let Some(field_ty) = field_types.get(i) {
                        let indices = get_constructor_return_indices(field_ty, num_params);
                        {
                            let mut _ix = 0usize;
                            while _ix < indices.len() {
                                let remapped = remap_residual_index_bvars(
                                    &indices[_ix], i, np, nf, n_minors, nm, n_pis,
                                );
                                ih = Expr::app(ih, remapped);
                                _ix += 1;
                            }
                        }
                    }
                }

                // Apply the recursive field as major premise.
                let mut major = Expr::bvar(usize_to_u32(nf - 1 - i + shift));
                // VERBATIM `for k in (0..n_pis).rev()` — descending while loop.
                {
                    let mut _k = n_pis;
                    while _k > 0 {
                        _k -= 1;
                        major = Expr::app(major, Expr::bvar(usize_to_u32(_k)));
                    }
                }
                ih = Expr::app(ih, major);

                // Wrap IH in lambda binders for Pi-bound variables (reflexive fields).
                let pi_domains = match field_types.get(i) {
                    Some(ft) => collect_pi_domains(ft),
                    None => Vec::new(),
                };
                // VERBATIM `for (k, (bi, domain)) in pi_domains.iter().enumerate().rev()`.
                {
                    let mut _pd = pi_domains.len();
                    while _pd > 0 {
                        _pd -= 1;
                        let k = _pd;
                        let (bi, domain) = &pi_domains[k];
                        let remapped =
                            remap_residual_index_bvars(domain, i, np, nf, n_minors, nm, k);
                        ih = Expr::lam(*bi, remapped, ih);
                    }
                }

                body = Expr::app(body, ih);
            }
            i += 1;
        }
    }

    // Extract actual domain types from the eliminator type's Pi binders:
    // Π params. Π motives. Π minors. Π rest...
    let dummy_ty = Expr::sort(Level::Zero);
    let mut elim_cursor = eliminator_type.clone();
    let mut param_domain_types: Vec<Expr> = Vec::new();
    {
        let mut _p = 0usize;
        while _p < np {
            match &elim_cursor.kind {
                ExprKind::Pi(_, domain, body) => {
                    param_domain_types.push((**domain).clone());
                    elim_cursor = (**body).clone();
                }
                _ => {
                    param_domain_types.push(dummy_ty.clone());
                }
            }
            _p += 1;
        }
    }
    let mut motive_domain_types: Vec<Expr> = Vec::new();
    {
        let mut _m = 0usize;
        while _m < nm {
            match &elim_cursor.kind {
                ExprKind::Pi(_, domain, body) => {
                    motive_domain_types.push((**domain).clone());
                    elim_cursor = (**body).clone();
                }
                _ => {
                    motive_domain_types.push(dummy_ty.clone());
                }
            }
            _m += 1;
        }
    }
    let mut minor_domain_types: Vec<Expr> = Vec::new();
    {
        let mut _mn = 0usize;
        while _mn < n_minors {
            match &elim_cursor.kind {
                ExprKind::Pi(_, domain, body) => {
                    minor_domain_types.push((**domain).clone());
                    elim_cursor = (**body).clone();
                }
                _ => {
                    minor_domain_types.push(dummy_ty.clone());
                }
            }
            _mn += 1;
        }
    }

    // Wrap body in λ params. λ motives. λ minors. λ fields. body
    let mut result = body;

    // Fields (innermost) — lift field types by (nm + n_minors) at depth i.
    let lift_amount = usize_to_u32(nm + n_minors);
    // VERBATIM `for i in (0..nf).rev()` — descending while loop.
    {
        let mut _fi = nf;
        while _fi > 0 {
            _fi -= 1;
            let i = _fi;
            let field_ty = match field_types.get(i) {
                Some(ft) => {
                    if lift_amount > 0 {
                        ft.lift_from(i as u32, lift_amount)
                    } else {
                        ft.clone()
                    }
                }
                None => dummy_ty.clone(),
            };
            result = Expr::lam(bi_default(), field_ty, result);
        }
    }
    // Minors (innermost minor first wrapping outward).
    {
        let mut _mi = minor_domain_types.len();
        while _mi > 0 {
            _mi -= 1;
            result = Expr::lam(bi_default(), minor_domain_types[_mi].clone(), result);
        }
    }
    // Motives.
    {
        let mut _mo = motive_domain_types.len();
        while _mo > 0 {
            _mo -= 1;
            result = Expr::lam(bi_default(), motive_domain_types[_mo].clone(), result);
        }
    }
    // Params (innermost param first wrapping outward).
    {
        let mut _pa = param_domain_types.len();
        while _pa > 0 {
            _pa -= 1;
            result = Expr::lam(bi_default(), param_domain_types[_pa].clone(), result);
        }
    }

    result
}

// ════════════════════════════════════════════════════════════════════════════
// The CtorInfo derivation from REAL ctor Pi-telescopes (VERBATIM, T3-verified).
// `HashSet<&Name>` -> Vec<Name> + name_eq scan (exact membership semantics:
// production Eq IS name_eq); `self` dropped.
// ════════════════════════════════════════════════════════════════════════════

// Modeled `ind_name_set.contains(name)` — linear scan over the block's names,
// each compare the production `Name::eq`.
pub(crate) fn name_in_set(name: &Name, ind_name_set: &[Name]) -> bool {
    let mut i = 0usize;
    while i < ind_name_set.len() {
        if name_eq(&ind_name_set[i], name) {
            return true;
        }
        i += 1;
    }
    false
}

// VERBATIM `field_is_eliminably_recursive` (inductive_recursor.rs:902): a field is
// *eliminably* recursive iff, after stripping leading Pi binders, the HEAD of its
// return type is one of the block inductives.
pub(crate) fn field_is_eliminably_recursive(field_ty: &Expr, ind_name_set: &[Name]) -> bool {
    let ret_ty = get_return_type(field_ty);
    let head = ret_ty.get_app_fn();
    // VERBATIM `matches!(&head.kind, ExprKind::Const(name, _) if ind_name_set.contains(name))`.
    match &head.kind {
        ExprKind::Const(name, _) => name_in_set(name, ind_name_set),
        _ => false,
    }
}

// VERBATIM `get_recursive_field_flags` (inductive_recursor.rs:877). For mutual
// inductives, a field is recursive if it (eliminably) mentions ANY type in the block.
pub(crate) fn get_recursive_field_flags(
    ctor_ty: &Expr,
    ind_name_set: &[Name],
    num_params: u32,
) -> Vec<bool> {
    let mut flags = Vec::new();
    let mut current = ctor_ty.clone();
    let mut arg_count = 0u32;

    while let ExprKind::Pi(_, domain, codomain) = &current.kind {
        if arg_count >= num_params {
            flags.push(field_is_eliminably_recursive(domain, ind_name_set));
        }
        current = (**codomain).clone();
        arg_count += 1;
    }
    flags
}

// VERBATIM `get_constructor_field_types` (inductive_recursor.rs:915) — field types
// after skipping parameters, through consume_type_annotations (modeled no-op).
pub(crate) fn get_constructor_field_types(ctor_ty: &Expr, num_params: u32) -> Vec<Expr> {
    let mut types = Vec::new();
    let mut current = ctor_ty.clone();
    let mut arg_count = 0u32;

    while let ExprKind::Pi(_, domain, codomain) = &current.kind {
        if arg_count >= num_params {
            types.push(consume_type_annotations(domain).clone());
        }
        current = (**codomain).clone();
        arg_count += 1;
    }
    types
}

// VERBATIM `compute_ctor_infos` (inductive_recursor.rs:34). The `decl` is passed as
// its two read fields (types via `all_types`, num_params); ind_name_set is built by
// the caller ONCE per block (`decl.types.iter().map(|t| &t.name).collect()` — push
// loop) and threaded through, preserving the once-per-block construction.
// `ctor.name.clone()` is now a REAL Name clone (production text).
pub(crate) fn compute_ctor_infos(
    ind_type: &InductiveType,
    ind_name_set: &[Name],
    num_params: u32,
) -> Vec<CtorInfo> {
    let mut ctor_infos: Vec<CtorInfo> = Vec::with_capacity(ind_type.constructors.len());
    // VERBATIM `for ctor in &ind_type.constructors` — index loop.
    {
        let mut _c = 0usize;
        while _c < ind_type.constructors.len() {
            let ctor = &ind_type.constructors[_c];
            let ctor_arity = count_pi_args(&ctor.type_);
            let num_fields = ctor_arity.saturating_sub(num_params);
            let recursive_flags = get_recursive_field_flags(&ctor.type_, ind_name_set, num_params);
            let field_types = get_constructor_field_types(&ctor.type_, num_params);
            let return_indices = get_constructor_return_indices(&ctor.type_, num_params);
            ctor_infos.push(CtorInfo {
                name: ctor.name.clone(),
                num_fields,
                recursive_flags,
                field_types,
                return_indices,
            });
            _c += 1;
        }
    }
    ctor_infos
}

// ════════════════════════════════════════════════════════════════════════════
// `fresh_univ_name` (inductive_fixed_indices.rs:276) — NOW IN-MODULE on its
// no-collision fast path: `candidate = Name::from_string("u")` ([T-unroll],
// single literal part), `existing.contains(&candidate)` -> name_eq scan.
// The `format!("u_{i}")` suffix search (gap 4) is PROVABLY DEAD on the harness
// families (existing = [] or ["v"] — "u" never collides); transcribed as a
// fallback returning the candidate so the fn stays total.
// ════════════════════════════════════════════════════════════════════════════

pub(crate) fn fresh_univ_name(existing: &[Name]) -> Name {
    let candidate = fold_step(name_anon(), "u");
    // VERBATIM `existing.contains(&candidate)` — scan, production Name::eq.
    let mut contains = false;
    {
        let mut _i = 0usize;
        while _i < existing.len() {
            if name_eq(&existing[_i], &candidate) {
                contains = true;
            }
            _i += 1;
        }
    }
    if !contains {
        return candidate;
    }
    // MODELED OUT (format! gap 4): the u_1/u_2/... suffix loop — dead on every
    // harness input (see header).
    candidate
}

// ════════════════════════════════════════════════════════════════════════════
// THE MUTUAL RECURSOR ASSEMBLY — VERBATIM the non-HIT path of `build_recursor`
// (inductive_recursor.rs:66) + the `minor_idx_offset` computation from its
// caller (inductive_builder.rs:322). Produces, for the block's type `which`:
// the full recursor TYPE (sel == 0) or the iota-rule RHS of that type's ctor j
// (sel == 1 + j).
//
// Now REAL end-to-end where Names flow:
//   * `rec_name = Name::from_string(&format!("{ind_name}.rec"))` (recursor.rs:80)
//     -> `name_append_rec(&ind_name)` [T-append] — in-module, no table;
//   * the non-prop arm of the (motive_univ_name, rec_level_params) derivation
//     (recursor.rs:89-99) runs IN-MODULE: fresh_univ_name + [u] ++ level_params
//     (prop_only is a MODELED input = false — separately verified, and
//     genuinely false for both harness families);
//   * the find-by-name loop and the take_while both compare via name_eq.
// RecursorVal metadata (names, arg_order, is_k) still not built (is_k is
// constantly false for mutual blocks — num_types != 1 short-circuit).
// ════════════════════════════════════════════════════════════════════════════

pub fn build_mutual_recursor_part(
    all_types: &[InductiveType],
    num_params: u32,
    level_params: &[Name],
    which: usize,
    sel: usize,
) -> Expr {
    // ind_name_set: `decl.types.iter().map(|t| &t.name).collect()` — push loop
    // (clones — the modeled HashSet<&Name> held refs; value semantics identical).
    let mut ind_name_set: Vec<Name> = Vec::new();
    {
        let mut _i = 0usize;
        while _i < all_types.len() {
            ind_name_set.push(all_types[_i].name.clone());
            _i += 1;
        }
    }

    // VERBATIM `decl.types.iter().find(|t| &t.name == ind_name)` — the root passes
    // `which` as an index, so ind_name = all_types[which].name and the find loop
    // resolves it back (preserving the real find-by-name control flow, now over
    // REAL Name equality).
    let ind_name = all_types[which].name.clone();
    let mut ind_type_idx = 0usize;
    {
        let mut _i = 0usize;
        while _i < all_types.len() {
            if name_eq(&all_types[_i].name, &ind_name) {
                ind_type_idx = _i;
                break;
            }
            _i += 1;
        }
    }
    let ind_type = &all_types[ind_type_idx];

    // THE DE-MODELED STEP (recursor.rs:80):
    // `let rec_name = Name::from_string(&format!("{ind_name}.rec"));`
    let rec_name = name_append_rec(&ind_name);

    // recursor.rs:83-99 — prop_only is MODELED = false (see header); the
    // non-prop arm runs VERBATIM: fresh motive universe + [u] ++ level_params.
    let motive_univ_name_owned = fresh_univ_name(level_params);
    let mut rec_level_params: Vec<Name> = Vec::new();
    rec_level_params.push(motive_univ_name_owned.clone());
    {
        let mut _lp = 0usize;
        while _lp < level_params.len() {
            rec_level_params.push(level_params[_lp].clone());
            _lp += 1;
        }
    }
    let motive_univ_name: Option<&Name> = Some(&motive_univ_name_owned);

    // `ctor_infos` for THIS type; `all_ctor_infos` via flat_map over ALL types
    // (VERBATIM inductive_builder.rs:314 — nested push loops).
    let ctor_infos = compute_ctor_infos(ind_type, &ind_name_set, num_params);
    let mut all_ctor_infos: Vec<CtorInfo> = Vec::new();
    {
        let mut _t = 0usize;
        while _t < all_types.len() {
            let infos_t = compute_ctor_infos(&all_types[_t], &ind_name_set, num_params);
            let mut _j = 0usize;
            while _j < infos_t.len() {
                all_ctor_infos.push(infos_t[_j].clone());
                _j += 1;
            }
            _t += 1;
        }
    }

    // VERBATIM minor_idx_offset (inductive_builder.rs:322):
    // `decl.types.iter().take_while(|t| t.name != ind_type.name).map(|t| t.constructors.len()).sum()`
    // — the `!=` is the production PartialEq negated (`!name_eq`).
    let mut minor_idx_offset: usize = 0;
    {
        let mut _t = 0usize;
        while _t < all_types.len() {
            if !name_eq(&all_types[_t].name, &ind_type.name) {
                minor_idx_offset += all_types[_t].constructors.len();
            } else {
                break;
            }
            _t += 1;
        }
    }

    // VERBATIM build_recursor's core (inductive_recursor.rs:101-120).
    let type_arity = count_pi_args(&ind_type.type_);
    let num_indices = type_arity.saturating_sub(num_params);
    let num_motives = all_types.len() as u32;
    let total_minors = all_ctor_infos.len();

    let rec_ty = build_recursor_type(
        &ind_name,
        &ind_type.type_,
        num_params,
        num_indices,
        motive_univ_name,
        level_params,
        &all_ctor_infos,
        all_types,
    );

    if sel == 0 {
        return rec_ty;
    }

    // VERBATIM the rules construction (inductive_recursor.rs:126-153): rules for
    // THIS type's constructors only, minor index globally offset. `sel - 1`
    // selects the local ctor idx (harness contract: 1 <= sel <= ctor_infos.len()).
    let mut idx = sel - 1;
    if idx >= ctor_infos.len() {
        idx = 0; // harness contract violation guard — never taken by the tests
    }
    let ci = &ctor_infos[idx];
    build_recursor_rule_rhs(
        &rec_name,
        &rec_level_params,
        num_params,
        num_motives,
        num_indices,
        ci.num_fields,
        &ci.recursive_flags,
        &ci.field_types,
        total_minors,
        minor_idx_offset + idx,
        &rec_ty,
        all_types,
    )
}

// ════════════════════════════════════════════════════════════════════════════
// IN-MODULE FAMILIES — the same Even/Odd and Tree/Forest blocks the landed T3
// test verified, now with REAL Names built from literal parts IN-MODULE
// (`from_string_uncached` unrolled — [T-unroll]; every dotted ctor name is the
// fold over its parts, continuing the ind-name chain exactly as production
// `from_string` would rebuild it). `vec![..]` -> Vec::new()+push (the
// established explicit-loop convention).
// ════════════════════════════════════════════════════════════════════════════

// Even/Odd: 0 params, 0 indices, monomorphic (Type 1 formers; level_params = []).
//   Even.zero : Even ; Even.succ_odd : Π(_:Odd). Even ; Odd.succ_even : Π(_:Even). Odd
pub fn family_even_odd() -> Vec<InductiveType> {
    // Type 1 former: Sort(Succ(Zero)) — Succ carries the production Arc.
    let type1 = Expr::sort(Level::Succ(level_arc(Level::Zero)));
    let e = Expr::const_(fold_step(name_anon(), "Even"), Vec::new());
    let o = Expr::const_(fold_step(name_anon(), "Odd"), Vec::new());

    let mut even_ctors: Vec<Ctor> = Vec::new();
    even_ctors.push(Ctor {
        name: fold_step(fold_step(name_anon(), "Even"), "zero"),
        type_: e.clone(),
    });
    even_ctors.push(Ctor {
        name: fold_step(fold_step(name_anon(), "Even"), "succ_odd"),
        type_: Expr::pi(bi_default(), o.clone(), e.clone()),
    });
    let mut odd_ctors: Vec<Ctor> = Vec::new();
    odd_ctors.push(Ctor {
        name: fold_step(fold_step(name_anon(), "Odd"), "succ_even"),
        type_: Expr::pi(bi_default(), e, o),
    });

    let mut out: Vec<InductiveType> = Vec::new();
    out.push(InductiveType {
        name: fold_step(name_anon(), "Even"),
        type_: type1.clone(),
        constructors: even_ctors,
    });
    out.push(InductiveType {
        name: fold_step(name_anon(), "Odd"),
        type_: type1,
        constructors: odd_ctors,
    });
    out
}

pub fn family_even_odd_level_params() -> Vec<Name> {
    Vec::new()
}

// Tree/Forest helpers: the level param `v` and the `I A` head applications.
fn lv_v() -> Level {
    Level::Param(fold_step(name_anon(), "v"))
}

fn tf_head_app(head: &str, a: Expr) -> Expr {
    let mut levels: Vec<Level> = Vec::new();
    levels.push(lv_v());
    Expr::app(Expr::const_(fold_step(name_anon(), head), levels), a)
}

// Tree/Forest: 1 param (A : Sort v), 0 indices; level_params = [v].
//   Tree.node    : Π(A:Sort v)(a:A)(f:Forest A). Tree A
//   Forest.nil   : Π(A:Sort v). Forest A
//   Forest.cons  : Π(A:Sort v)(t:Tree A)(f:Forest A). Forest A
pub fn family_tree_forest() -> Vec<InductiveType> {
    let sort_v = Expr::sort(lv_v());
    // former: Π(A:Sort v). Sort v
    let former = Expr::pi(bi_default(), sort_v.clone(), Expr::sort(lv_v()));
    // Tree.node : Π(A:Sort v). Π(a:#0). Π(f:Forest #1). Tree #2
    let node_ty = Expr::pi(
        bi_default(),
        sort_v.clone(),
        Expr::pi(
            bi_default(),
            Expr::bvar(0),
            Expr::pi(
                bi_default(),
                tf_head_app("Forest", Expr::bvar(1)),
                tf_head_app("Tree", Expr::bvar(2)),
            ),
        ),
    );
    // Forest.nil : Π(A:Sort v). Forest #0
    let nil_ty = Expr::pi(bi_default(), sort_v.clone(), tf_head_app("Forest", Expr::bvar(0)));
    // Forest.cons : Π(A:Sort v). Π(t:Tree #0). Π(f:Forest #1). Forest #2
    let cons_ty = Expr::pi(
        bi_default(),
        sort_v,
        Expr::pi(
            bi_default(),
            tf_head_app("Tree", Expr::bvar(0)),
            Expr::pi(
                bi_default(),
                tf_head_app("Forest", Expr::bvar(1)),
                tf_head_app("Forest", Expr::bvar(2)),
            ),
        ),
    );

    let mut tree_ctors: Vec<Ctor> = Vec::new();
    tree_ctors.push(Ctor {
        name: fold_step(fold_step(name_anon(), "Tree"), "node"),
        type_: node_ty,
    });
    let mut forest_ctors: Vec<Ctor> = Vec::new();
    forest_ctors.push(Ctor {
        name: fold_step(fold_step(name_anon(), "Forest"), "nil"),
        type_: nil_ty,
    });
    forest_ctors.push(Ctor {
        name: fold_step(fold_step(name_anon(), "Forest"), "cons"),
        type_: cons_ty,
    });

    let mut out: Vec<InductiveType> = Vec::new();
    out.push(InductiveType {
        name: fold_step(name_anon(), "Tree"),
        type_: former.clone(),
        constructors: tree_ctors,
    });
    out.push(InductiveType {
        name: fold_step(name_anon(), "Forest"),
        type_: former,
        constructors: forest_ctors,
    });
    out
}

pub fn family_tree_forest_level_params() -> Vec<Name> {
    let mut lp: Vec<Name> = Vec::new();
    lp.push(fold_step(name_anon(), "v"));
    lp
}

// ════════════════════════════════════════════════════════════════════════════
// MONO ROOT A (#[no_mangle]) — the full mutual-recursor construction over REAL
// in-module Names: (family, which, sel) scalars in, the resulting Expr out
// through the sret pointer. family 0 = Even/Odd (0 params), family 1 =
// Tree/Forest (1 param). sel 0 => rec TYPE; 1 + j => rule RHS of local ctor j.
// ════════════════════════════════════════════════════════════════════════════

#[no_mangle]
pub extern "C" fn build_mutual_rec_realnames_root(
    out: *mut Expr,
    family: u64,
    which: u64,
    sel: u64,
) {
    let result = if family == 0 {
        let all_types = family_even_odd();
        let level_params = family_even_odd_level_params();
        build_mutual_recursor_part(&all_types, 0, &level_params, which as usize, sel as usize)
    } else {
        let all_types = family_tree_forest();
        let level_params = family_tree_forest_level_params();
        build_mutual_recursor_part(&all_types, 1, &level_params, which as usize, sel as usize)
    };
    unsafe {
        std::ptr::write(out, result);
    }
}

// ════════════════════════════════════════════════════════════════════════════
// MONO ROOT B (#[no_mangle]) — the NAME PROBE: returns (sret) one of the REAL
// Names the family construction produces, straight off the built block, so the
// harness can decode it raw and pin cached_hash BIT-IDENTICAL to the real
// clean-kernel goldens:
//   idx 0 / 1     : all_types[idx].name (the ind names)
//   idx 2 ..= 4   : the block's constructors in GLOBAL MINOR ORDER (flat index
//                   idx-2 across types — the same order the minors take)
//   idx 5 / 6     : name_append_rec(&all_types[idx-5].name) — the production
//                   `.rec` derivation over the STORED head names
//   idx 7         : fresh_univ_name(level_params) — the motive universe `u`
//   idx 8+        : level_params[0] (family 1's `v`; anon for family 0 — the
//                   harness never asks)
// ════════════════════════════════════════════════════════════════════════════

fn probe_pick(all_types: &[InductiveType], level_params: &[Name], idx: u64) -> Name {
    if idx == 0 || idx == 1 {
        return all_types[idx as usize].name.clone();
    }
    if idx >= 2 && idx <= 4 {
        let mut want = (idx - 2) as usize;
        let mut t = 0usize;
        while t < all_types.len() {
            if want < all_types[t].constructors.len() {
                return all_types[t].constructors[want].name.clone();
            }
            want -= all_types[t].constructors.len();
            t += 1;
        }
        return name_anon(); // out of range — never taken by the harness
    }
    if idx == 5 || idx == 6 {
        return name_append_rec(&all_types[(idx - 5) as usize].name);
    }
    if idx == 7 {
        return fresh_univ_name(level_params);
    }
    if level_params.len() > 0 {
        return level_params[0].clone();
    }
    name_anon()
}

#[no_mangle]
pub extern "C" fn realnames_name_probe_root(out: *mut Name, family: u64, idx: u64) {
    let name = if family == 0 {
        let all_types = family_even_odd();
        let level_params = family_even_odd_level_params();
        probe_pick(&all_types, &level_params, idx)
    } else {
        let all_types = family_tree_forest();
        let level_params = family_tree_forest_level_params();
        probe_pick(&all_types, &level_params, idx)
    };
    unsafe {
        std::ptr::write(out, name);
    }
}

// ── standalone smoke harness (native only; NOT part of either emitted root) ──

fn main() {
    // Both families, every (which, sel) the e2e drives: print the meta words.
    let mut all_ok = true;
    let fam_sels: [(u64, u64, u64); 10] = [
        (0, 0, 0),
        (0, 0, 1),
        (0, 0, 2),
        (0, 1, 0),
        (0, 1, 1),
        (1, 0, 0),
        (1, 0, 1),
        (1, 1, 0),
        (1, 1, 1),
        (1, 1, 2),
    ];
    for (family, which, sel) in fam_sels {
        let mut slot = std::mem::MaybeUninit::<Expr>::uninit();
        let via_root = unsafe {
            build_mutual_rec_realnames_root(slot.as_mut_ptr(), family, which, sel);
            slot.assume_init()
        };
        let direct = if family == 0 {
            let at = family_even_odd();
            let lp = family_even_odd_level_params();
            build_mutual_recursor_part(&at, 0, &lp, which as usize, sel as usize)
        } else {
            let at = family_tree_forest();
            let lp = family_tree_forest_level_params();
            build_mutual_recursor_part(&at, 1, &lp, which as usize, sel as usize)
        };
        let eq = via_root.meta.raw() == direct.meta.raw();
        println!(
            "f{family} w{which} s{sel}: meta={:#018x} eq={eq}",
            direct.meta.raw()
        );
        if !eq {
            all_ok = false;
        }
    }
    // Name probes: print the cached_hash of every probed name.
    for family in 0u64..2 {
        let top = if family == 0 { 8 } else { 9 };
        for idx in 0..top {
            let mut slot = std::mem::MaybeUninit::<Name>::uninit();
            let n = unsafe {
                realnames_name_probe_root(slot.as_mut_ptr(), family, idx);
                slot.assume_init()
            };
            println!("probe f{family} i{idx}: {:#018x}", n.cached_hash);
        }
    }
    std::process::exit((!all_ok) as i32);
}
