// R18 — THE QUOTIENT MACHINERY, re-composed on the full modern stack: the
// companion to R17's inductive-soundness gate. Clean's kernel ASSERTS the five
// quotient axiom TYPES as true without proof (a wrong axiom type installs a
// LIE — a route to False), and REDUCES `Quot.lift f h (Quot.mk r a)` to `f a`
// (the iota computation rule, soundness-critical). This slice re-composes BOTH
// surfaces on the COMPLETE modern stack — real production Names (NameInner
// Anon/Str/Num Arc chains, murmur/mix cached_hash, name_eq at every comparison),
// the full production Level {Zero,Succ,Max,IMax,Param}, and the production
// compute_meta (Const arm mixes levels_hash + derives has_level_param) — rather
// than R1's Name(u32) + Zero/Succ/Param-only model
// (clean_expr_quot_slice.rs / clean_quot_type_slice.rs).
//
// THE TWO SURFACES:
//   1. THE 5 AXIOM TYPES (the trusted types the kernel asserts as axioms):
//      quot_type / quot_mk_type / quot_lift_type / quot_ind_type /
//      quot_sound_type — VERBATIM $HOME/clean/crates/clean-kernel/src/quot.rs
//      (:97 / :126 / :174 (+build_lift_proof_type :247 + make_eq_type :298) /
//      :321 (+build_ind_hyp_type :394) / :420), upgraded to real Names + full
//      Level. Each built type is compared BIT-IDENTICAL (ExprMeta + structure)
//      native == JIT.
//   2. THE IOTA REDUCTION: `try_quot_lift_reduction` (quot.rs:598) and
//      `try_quot_ind_reduction` (:679) VERBATIM, wired at the whnf App-arm
//      quot-leaf (cert/reduction.rs:296 / tc/reduction/mod.rs:695) — a real
//      Quot.lift-of-Quot.mk reduces to `f a` (payload-deep), and a NON-redex
//      (Quot.lift on a non-Quot.mk major) is left stuck — native == JIT.
//
// THE LOAD-BEARING / SOUNDNESS PROOF (the R17/R15 pattern): a WRONG axiom type
// is a LIE. Two axiom builders carry an armed `blind` flag reproducing the EXACT
// latent off-by-one the source comments warn about:
//   * quot_lift_type: the result-type BVar. Production is `Expr::bvar(3)` (the
//     codomain β); the SOUNDNESS comment (quot.rs:205-214) records a latent bug
//     that used `Expr::bvar(2)` (the lifting function `f`) instead — installing
//     an ill-typed eliminator. `blind` reproduces `Expr::bvar(2)`. This is the
//     ORIGINAL R1 negative control, now on the modern stack.
//   * quot_sound_type: the hypothesis `h : r a b`. Production is
//     `app(app(r, a), b)`; `blind` swaps the arguments to `app(app(r, b), a)`
//     (`r b a`) — a swapped-relation-argument corruption of the SOUNDNESS
//     axiom, installing a different (wrong-direction) quotient-identification
//     axiom.
// Plus a POISONED IOTA ORACLE: `try_quot_lift_reduction` carries an armed
// `poison` flag that, when set, extracts the WRONG quoted value
// (`major_args[1]` = r, not `major_args[2]` = a) — a reduce that returns the
// wrong term. Each corruption DIVERGES from the correct construction native ==
// JIT, demonstrating the machine code genuinely runs the soundness-critical
// logic.
//
// MODELED BOUNDARIES (which of the 5 / which quot paths are modeled vs
// transcribed; whether the modern stack genuinely flows through):
//   * Names: FULLY MODERN. Every Name is the production `Name` built in-module
//     from literal parts (`from_string_uncached` unrolled — name.rs:557-565);
//     the interned `names::QUOT` / `QUOT_MK` / `QUOT_LIFT` / `QUOT_IND` /
//     `QUOT_SOUND` / `"Eq"` / `"u"` / `"v"` are `fold_step`-folded exactly as
//     `Name::from_string` folds them (splitting on '.'), value-identical (no
//     interner on this path — name.rs:578, the round-5 finding). Every name
//     comparison the iota reduction performs (is Quot.lift? is Quot.mk? is
//     Quot.ind?) is the PRODUCTION `name_eq` (hash fast-path + structural walk).
//   * Level: the FULL production 5-variant enum {Zero,Succ,Max,IMax,Param} with
//     Param carrying real Names, VERBATIM smart constructors (zero/succ/max/imax/
//     param) / has_params / is_zero / is_nonzero / PartialEq (Param arm = the
//     production name_eq) / Hash. The quotient axioms build ONLY `Sort(Param u)`,
//     `Sort(Param v)`, `prop()`=`Sort(Zero)`, and `Const(_, [Param u | Param v])`
//     — EXACTLY as production quot.rs does (the quotient primitives are universe-
//     parametric, never Max/IMax). [BOUNDARY: the normalize / is_geq / is_norm_lt
//     universe-UNIFICATION machinery is OMITTED here — it is not reached by the
//     quotient machinery (the builders construct raw Param/Zero and the iota path
//     does no universe compare; whnf never normalizes), exactly as production
//     quot.rs never touches normalize; that machinery is transcribed+verified in
//     the R6 realnames rung. The Max/IMax variants EXIST in the enum and are
//     handled by has_params/Hash/PartialEq, but the axioms never INSTANTIATE
//     them — so full-Level flow here is the real Names threading through
//     Param + the production compute_meta, not Max/IMax normalization.]
//   * compute_meta: PRODUCTION (Const arm expr/kind.rs:567-581 — levels_hash
//     mixed, has_level_param derived). Payload hashes flow through the KaniHasher
//     (B7 — clean's own cfg(kani) hasher; the real-Name cached_hash CONTENT is
//     production). The five axiom-type meta words are therefore internally
//     consistent + native==JIT bit-identical, but NOT equal to a production
//     non-kani SipHash13 clean-kernel binary golden (B7). The REAL-NAME
//     cached_hashes ARE pinned to the murmur-chain golden (R4-R7 verified
//     bit-identical to the real clean-kernel binary).
//   * env / ctor-info: slice-scan (B1), empty on the iota scenarios (the quot
//     heads never delta-unfold; the major whnf's to Quot.mk directly).
//   * Arc<Expr>/Arc<Level>/Arc<Name>/Arc<str> children are real; Arc::new + Arc
//     deref INLINED; clones/from bound to faithful host shims (landed
//     convention). Drops not emitted (leak model — every Name/Expr immortal).
//   * BinderInfo::Default/Implicit -> the production `BinderData` scalar the real
//     `Expr::pi` stores after `Into` (Default=>{info:0,mult:2(Many)},
//     Implicit=>{info:1,mult:2}); compute_meta ignores BinderData, so the exact
//     mult byte is verification-inert (native==JIT), and is the production value
//     (more faithful than R1's mult:0 model).
//   * try_quot_ind_reduction is transcribed and exercised (case 3); the K-axiom
//     / native / nat reducers are out of scope (verified elsewhere / registry-
//     empty here).
//
// SOURCES (verbatim transcription targets in $HOME/clean/crates/clean-kernel/src):
//   quot.rs           — quot_type(:97), quot_mk_type(:126), quot_lift_type(:174),
//                       build_lift_proof_type(:247), make_eq_type(:298),
//                       quot_ind_type(:321), build_ind_hyp_type(:394),
//                       quot_sound_type(:420), try_quot_lift_reduction(:598),
//                       try_quot_ind_reduction(:679).
//   cert/reduction.rs — whnf_impl (BETA/DELTA/ZETA/proj-iota) + try_quot_reduction
//                       (:296) dispatch.
//   tc/reduction/mod.rs — the lift|ind quot-reduction dispatch (:695).
//   name.rs / level/mod.rs / expr/meta.rs / expr/kind.rs — the modern-stack
//                       Name / Level / ExprMeta / compute_meta (VERBATIM the
//                       R4-R7 transcriptions; see clean_decl_universe_realnames_slice.rs).
//
// Crate name is load-bearing (appears in mangled extern-leaf symbols): it MUST
// stay `clean_quotient_slice`.
//
// REGEN (one module per root; trust-ir main >= 375c800 — NO frontend changes):
//   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//   cd $HOME/trust-ir/frontend
//   env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//     $S/bin/cargo run --bin trust_ir_mir -- \
//     ../../trust-cg/crates/trust-cg-codegen/tests/slices/clean_quotient_slice.rs \
//     --crate-type=lib --mir-emit-closure <root> <out.tir>
//   roots: quot_axiom_root | quot_iota_root | quot_names_probe_root

#![allow(dead_code)]
#![allow(clippy::all)]
#![allow(unused_variables)]

#[allow(unused_imports)]
use std::convert::TryFrom;
use std::hash::{Hash, Hasher};
use std::sync::Arc; // pre-2021 prelude (the MIR driver's edition)

// ════════════════════════════════════════════════════════════════════════════
// clean-kernel name.rs — the production Name (VERBATIM; R4-R7 transcriptions,
// harness-proved bit-identical to the real clean-kernel).
// ════════════════════════════════════════════════════════════════════════════

/// name.rs:150-159 (production, non-kani): the recursive inner representation.
#[derive(Clone, Debug)]
pub enum NameInner {
    Anon,
    Str(Arc<Name>, Arc<str>),
    Num(Arc<Name>, u64),
}

/// name.rs:233-239: hierarchical name with construction-time cached hash.
#[derive(Clone, Debug)]
pub struct Name {
    pub inner: NameInner,
    pub cached_hash: u64,
}

/// VERBATIM production `Hash for Name` (name.rs:461-465): O(1) cached_hash.
impl Hash for Name {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.cached_hash.hash(state);
    }
}

/// MurmurHash2-64A mixing step (expr/meta.rs:264-273). VERBATIM.
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

/// env/native_reducers_string.rs:357-393 murmur_hash_64a [T-murmur-idx].
pub fn murmur_hash_64a_idx(data: &[u8], seed: u64) -> u64 {
    const M: u64 = 0xc6a4_a793_5bd1_e995;
    const R: u32 = 47;
    let len = data.len();
    let mut h: u64 = seed ^ (len as u64).wrapping_mul(M);

    let nblocks = len / 8;
    let mut b = 0usize;
    while b < nblocks {
        let base = b * 8;
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

/// `Name::anon()`; `compute_hash(Anon) = 1723`.
pub fn name_anon() -> Name {
    Name {
        inner: NameInner::Anon,
        cached_hash: 1723,
    }
}

/// `Name::str(self, s)`: cached_hash = mix_hash(p.cached_hash, murmur(s, 11)).
pub fn name_str_part(parent: Name, part: &str) -> Name {
    let string_hash = murmur_hash_64a_idx(part.as_bytes(), 11);
    let cached_hash = mix_hash(parent.cached_hash, string_hash);
    let inner = NameInner::Str(Arc::new(parent), Arc::from(part));
    Name { inner, cached_hash }
}

/// `Name::num(self, n)`: cached_hash = mix_hash(p.cached_hash, n).
pub fn name_num_part(parent: Name, n: u64) -> Name {
    let cached_hash = mix_hash(parent.cached_hash, n);
    Name {
        inner: NameInner::Num(Arc::new(parent), n),
        cached_hash,
    }
}

/// `part.parse::<u64>()` decimal path [T-parse].
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
        if acc > (u64::MAX - d) / 10 {
            return (false, 0);
        }
        acc = acc * 10 + d;
        i += 1;
    }
    (true, acc)
}

/// `from_string_uncached`'s fold body, one part (name.rs:558-564).
pub fn fold_step(acc: Name, part: &str) -> Name {
    let (is_num, n) = parse_u64_ascii(part);
    if is_num {
        name_num_part(acc, n)
    } else {
        name_str_part(acc, part)
    }
}

/// `str::eq` value semantics.
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

/// name.rs:367-377 production PartialEq [T-eq-iter]: hash fast-path + walk.
pub fn name_eq(a: &Name, b: &Name) -> bool {
    if a.cached_hash != b.cached_hash {
        return false;
    }
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

/// `str::cmp` == `as_bytes().cmp()`.
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

/// name.rs:393-458 production Ord (Lean cmp_core) [T-ord]. Present for source
/// fidelity; NOT reached by the quotient machinery (no level normalize).
pub fn name_cmp_is_lt(a: &Name, b: &Name) -> bool {
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
                (NameInner::Num(_, _), NameInner::Str(_, _)) => return true,
                (NameInner::Str(_, _), NameInner::Num(_, _)) => return false,
                _ => {}
            },
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Leaf payloads + the full production Level (level/mod.rs). VERBATIM.
// ════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FVarId(pub u64);

pub type LevelArc = Arc<Level>;

#[inline(always)]
fn level_arc(l: Level) -> LevelArc {
    Arc::new(l)
}

/// level/mod.rs:81 — variant ORDER VERBATIM (Zero=0,Succ=1,Max=2,IMax=3,Param=4).
#[derive(Clone, Debug)]
pub enum Level {
    Zero,
    Succ(LevelArc),
    Max(LevelArc, LevelArc),
    IMax(LevelArc, LevelArc),
    Param(Name),
}

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
    pub fn zero() -> Self {
        Level::Zero
    }
    pub fn succ(l: Level) -> Self {
        Level::Succ(level_arc(l))
    }
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
    pub fn is_zero(&self) -> bool {
        match self {
            Level::Zero => true,
            Level::Succ(_) | Level::Param(_) => false,
            Level::Max(l1, l2) => l1.is_zero() && l2.is_zero(),
            Level::IMax(_, l2) => l2.is_zero(),
        }
    }
    fn is_nonzero(&self) -> bool {
        match self {
            Level::Zero | Level::Param(_) => false,
            Level::Succ(_) => true,
            Level::Max(l1, l2) => l1.is_nonzero() || l2.is_nonzero(),
            Level::IMax(_, l2) => l2.is_nonzero(),
        }
    }
    pub fn has_params(&self) -> bool {
        match self {
            Level::Zero => false,
            Level::Succ(l) => l.has_params(),
            Level::Max(l1, l2) | Level::IMax(l1, l2) => l1.has_params() || l2.has_params(),
            Level::Param(_) => true,
        }
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

// BinderInfo::Default/Implicit -> the production BinderData the real Expr::pi
// stores after `Into` (Default=>{0,Many}, Implicit=>{1,Many}; Many=2).
#[inline]
fn bi_default() -> BinderData {
    BinderData { info: 0, mult: 2 }
}
#[inline]
fn bi_implicit() -> BinderData {
    BinderData { info: 1, mult: 2 }
}

// ════════════════════════════════════════════════════════════════════════════
// expr/meta.rs — KaniHasher (B7) + per-type hashers + ExprMeta (VERBATIM).
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
/// `hash_to_u64(levels)` for `levels: &LevelVec` — length-prefix + per-element
/// (the production Const-arm levels_hash, expr/kind.rs:569) [B9].
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
#[inline]
fn level_has_mvar(_l: &Level) -> bool {
    false
}

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
    pub fn raw(self) -> u64 {
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

// ════════════════════════════════════════════════════════════════════════════
// expr/kind.rs — ExprKind + production compute_meta (Const arm :567-581 VERBATIM).
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
            // PRODUCTION Const arm (expr/kind.rs:567-581).
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
    pub kind: ExprKind,
    pub meta: ExprMeta,
}

impl Expr {
    pub fn from_kind(kind: ExprKind) -> Self {
        let meta = kind.compute_meta();
        Expr { kind, meta }
    }
    pub fn meta(&self) -> ExprMeta {
        self.meta
    }
    pub fn kind(&self) -> &ExprKind {
        &self.kind
    }
    fn loose_bvar_range(&self) -> u32 {
        self.meta.loose_bvar_range()
    }
    pub fn bvar(idx: u32) -> Self {
        Expr::from_kind(ExprKind::BVar(idx))
    }
    pub fn cnst(name: Name) -> Self {
        Expr::from_kind(ExprKind::Const(name, Vec::new()))
    }
    pub fn const_(name: Name, levels: LevelVec) -> Self {
        Expr::from_kind(ExprKind::Const(name, levels))
    }
    pub fn sort0() -> Self {
        Expr::from_kind(ExprKind::Sort(Level::Zero))
    }
    pub fn sort(l: Level) -> Self {
        Expr::from_kind(ExprKind::Sort(l))
    }
    /// `Expr::prop` (constructors.rs:42): Prop = Sort 0.
    pub fn prop() -> Self {
        Expr::from_kind(ExprKind::Sort(Level::zero()))
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
            ExprKind::Let(name, ty, val_e, body, nondep) => Expr::from_kind(ExprKind::Let(
                name.clone(),
                Arc::new(ty.instantiate_at(val, depth)),
                Arc::new(val_e.instantiate_at(val, depth)),
                Arc::new(body.instantiate_at(val, depth.saturating_add(1))),
                *nondep,
            )),
            ExprKind::Proj(name, idx, e) => Expr::from_kind(ExprKind::Proj(
                name.clone(),
                *idx,
                Arc::new(e.instantiate_at(val, depth)),
            )),
            _ => self.clone(),
        }
    }
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
// The interned quotient / Eq Names, built in-module (fold_step splits on '.').
// ════════════════════════════════════════════════════════════════════════════

#[derive(Clone)]
pub struct QuotNames {
    pub quot: Name,       // names::QUOT       = "Quot"
    pub quot_mk: Name,    // names::QUOT_MK    = "Quot.mk"
    pub quot_lift: Name,  // names::QUOT_LIFT  = "Quot.lift"
    pub quot_ind: Name,   // names::QUOT_IND   = "Quot.ind"
    pub quot_sound: Name, // names::QUOT_SOUND = "Quot.sound"
    pub eq: Name,         // Name::from_string("Eq")
}

pub fn nm_quot() -> Name {
    fold_step(name_anon(), "Quot")
}
pub fn nm_quot_mk() -> Name {
    fold_step(fold_step(name_anon(), "Quot"), "mk")
}
pub fn nm_quot_lift() -> Name {
    fold_step(fold_step(name_anon(), "Quot"), "lift")
}
pub fn nm_quot_ind() -> Name {
    fold_step(fold_step(name_anon(), "Quot"), "ind")
}
pub fn nm_quot_sound() -> Name {
    fold_step(fold_step(name_anon(), "Quot"), "sound")
}
pub fn nm_eq() -> Name {
    fold_step(name_anon(), "Eq")
}
pub fn nm_u() -> Name {
    fold_step(name_anon(), "u")
}
pub fn nm_v() -> Name {
    fold_step(name_anon(), "v")
}

fn quot_names() -> QuotNames {
    QuotNames {
        quot: nm_quot(),
        quot_mk: nm_quot_mk(),
        quot_lift: nm_quot_lift(),
        quot_ind: nm_quot_ind(),
        quot_sound: nm_quot_sound(),
        eq: nm_eq(),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// quot.rs — VERBATIM axiom-type builders (real Names + full Level). The `blind`
// flag on quot_lift_type / quot_sound_type reproduces the EXACT latent
// off-by-one the SOUNDNESS comments warn about.
// ════════════════════════════════════════════════════════════════════════════

/// VERBATIM `quot_type` (quot.rs:97).
fn quot_type(u: &Name) -> Expr {
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
    let alpha = Expr::bvar(0);
    let r_type = Expr::pi(
        bi_default(),
        alpha.clone(),
        Expr::pi(bi_default(), Expr::bvar(1), Expr::prop()),
    );
    let result = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
    Expr::pi(
        bi_implicit(),
        sort_u,
        Expr::pi(bi_default(), r_type, result),
    )
}

/// VERBATIM `quot_mk_type` (quot.rs:126).
fn quot_mk_type(u: &Name, qn: &QuotNames) -> Expr {
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
    let r_type = Expr::pi(
        bi_default(),
        Expr::bvar(0),
        Expr::pi(bi_default(), Expr::bvar(1), Expr::prop()),
    );
    let quot_app = Expr::app(
        Expr::app(
            Expr::const_(qn.quot.clone(), vec![Level::param(u.clone())]),
            Expr::bvar(2),
        ),
        Expr::bvar(1),
    );
    Expr::pi(
        bi_implicit(),
        sort_u,
        Expr::pi(
            bi_default(),
            r_type,
            Expr::pi(bi_default(), Expr::bvar(1), quot_app),
        ),
    )
}

/// VERBATIM `quot_lift_type` (quot.rs:174). `blind` reproduces the latent
/// result-type off-by-one (BVar(2)=f instead of BVar(3)=β; quot.rs:205-214).
fn quot_lift_type(u: &Name, v: &Name, qn: &QuotNames, blind: bool) -> Expr {
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
    let sort_v = Expr::from_kind(ExprKind::Sort(Level::param(v.clone())));
    let r_type = Expr::pi(
        bi_default(),
        Expr::bvar(0),
        Expr::pi(bi_default(), Expr::bvar(1), Expr::prop()),
    );
    let f_type = Expr::pi(bi_default(), Expr::bvar(2), Expr::bvar(1));
    let proof_type = build_lift_proof_type(Level::param(v.clone()), qn);
    let quot_type_app = Expr::app(
        Expr::app(
            Expr::const_(qn.quot.clone(), vec![Level::param(u.clone())]),
            Expr::bvar(4),
        ),
        Expr::bvar(3),
    );
    // SOUNDNESS: production is BVar(3) (the codomain β). The latent bug used
    // BVar(2) (the lifting function f) — an ill-typed eliminator, a LIE.
    let result = if blind { Expr::bvar(2) } else { Expr::bvar(3) };
    Expr::pi(
        bi_implicit(),
        sort_u,
        Expr::pi(
            bi_implicit(),
            r_type,
            Expr::pi(
                bi_implicit(),
                sort_v,
                Expr::pi(
                    bi_default(),
                    f_type,
                    Expr::pi(
                        bi_default(),
                        proof_type,
                        Expr::pi(bi_default(), quot_type_app, result),
                    ),
                ),
            ),
        ),
    )
}

/// VERBATIM `build_lift_proof_type` (quot.rs:247).
fn build_lift_proof_type(level_v: Level, qn: &QuotNames) -> Expr {
    let alpha = Expr::bvar(3);
    let _r = Expr::bvar(2);
    let _f = Expr::bvar(0);
    let r_a_b = Expr::app(Expr::app(Expr::bvar(4), Expr::bvar(1)), Expr::bvar(0));
    let f_a = Expr::app(Expr::bvar(3), Expr::bvar(2));
    let f_b = Expr::app(Expr::bvar(3), Expr::bvar(1));
    let eq_type = make_eq_type(level_v, Expr::bvar(4), f_a, f_b, qn);
    Expr::pi(
        bi_default(),
        alpha.clone(),
        Expr::pi(
            bi_default(),
            Expr::bvar(4),
            Expr::pi(bi_default(), r_a_b, eq_type),
        ),
    )
}

/// VERBATIM `make_eq_type` (quot.rs:298).
fn make_eq_type(level_v: Level, beta: Expr, a: Expr, b: Expr, qn: &QuotNames) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(qn.eq.clone(), vec![level_v]), beta),
            a,
        ),
        b,
    )
}

/// VERBATIM `quot_ind_type` (quot.rs:321).
fn quot_ind_type(u: &Name, qn: &QuotNames) -> Expr {
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
    let r_type = Expr::pi(
        bi_default(),
        Expr::bvar(0),
        Expr::pi(bi_default(), Expr::bvar(1), Expr::prop()),
    );
    let quot_alpha_r = Expr::app(
        Expr::app(
            Expr::const_(qn.quot.clone(), vec![Level::param(u.clone())]),
            Expr::bvar(1),
        ),
        Expr::bvar(0),
    );
    let beta_type = Expr::pi(bi_default(), quot_alpha_r.clone(), Expr::prop());
    let ih_type = build_ind_hyp_type(u, qn);
    let quot_final = Expr::app(
        Expr::app(
            Expr::const_(qn.quot.clone(), vec![Level::param(u.clone())]),
            Expr::bvar(3),
        ),
        Expr::bvar(2),
    );
    let beta_q = Expr::app(Expr::bvar(2), Expr::bvar(0));
    Expr::pi(
        bi_implicit(),
        sort_u,
        Expr::pi(
            bi_implicit(),
            r_type,
            Expr::pi(
                bi_implicit(),
                beta_type,
                Expr::pi(
                    bi_default(),
                    ih_type,
                    Expr::pi(bi_default(), quot_final, beta_q),
                ),
            ),
        ),
    )
}

/// VERBATIM `build_ind_hyp_type` (quot.rs:394).
fn build_ind_hyp_type(u: &Name, qn: &QuotNames) -> Expr {
    let alpha = Expr::bvar(2);
    let mk_a = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(qn.quot_mk.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(3),
            ),
            Expr::bvar(2),
        ),
        Expr::bvar(0),
    );
    let beta_mk_a = Expr::app(Expr::bvar(1), mk_a);
    Expr::pi(bi_default(), alpha, beta_mk_a)
}

/// VERBATIM `quot_sound_type` (quot.rs:420). `blind` swaps the hypothesis
/// arguments (`r a b` -> `r b a`) — a swapped-relation-argument corruption of
/// the soundness axiom.
fn quot_sound_type(u: &Name, qn: &QuotNames, blind: bool) -> Expr {
    let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
    let r_type = Expr::pi(
        bi_default(),
        Expr::bvar(0),
        Expr::pi(bi_default(), Expr::bvar(1), Expr::prop()),
    );
    let a_type = Expr::bvar(1);
    let b_type = Expr::bvar(2);
    // production `h : r a b` = app(app(r, a), b) = app(app(#2,#1),#0). The blind
    // variant swaps a and b -> `r b a` = app(app(#2,#0),#1).
    let h_type = if blind {
        Expr::app(Expr::app(Expr::bvar(2), Expr::bvar(0)), Expr::bvar(1))
    } else {
        Expr::app(Expr::app(Expr::bvar(2), Expr::bvar(1)), Expr::bvar(0))
    };
    let quot_alpha_r = Expr::app(
        Expr::app(
            Expr::const_(qn.quot.clone(), vec![Level::param(u.clone())]),
            Expr::bvar(4),
        ),
        Expr::bvar(3),
    );
    let mk_a = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(qn.quot_mk.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(4),
            ),
            Expr::bvar(3),
        ),
        Expr::bvar(2),
    );
    let mk_b = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(qn.quot_mk.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(4),
            ),
            Expr::bvar(3),
        ),
        Expr::bvar(1),
    );
    let eq_app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(qn.eq.clone(), vec![Level::param(u.clone())]),
                quot_alpha_r,
            ),
            mk_a,
        ),
        mk_b,
    );
    Expr::pi(
        bi_implicit(),
        sort_u,
        Expr::pi(
            bi_implicit(),
            r_type,
            Expr::pi(
                bi_implicit(),
                a_type,
                Expr::pi(
                    bi_implicit(),
                    b_type,
                    Expr::pi(bi_default(), h_type, eq_app),
                ),
            ),
        ),
    )
}

fn build_axiom(kind: u64, blind: bool) -> Expr {
    let u = nm_u();
    let v = nm_v();
    let qn = quot_names();
    if kind == 0 {
        quot_type(&u)
    } else if kind == 1 {
        quot_mk_type(&u, &qn)
    } else if kind == 2 {
        quot_lift_type(&u, &v, &qn, blind)
    } else if kind == 3 {
        quot_ind_type(&u, &qn)
    } else {
        quot_sound_type(&u, &qn, blind)
    }
}

// ════════════════════════════════════════════════════════════════════════════
// The whnf + iota-reduction Verifier (cert/reduction.rs). env/ctors empty on
// the quot scenarios; `quots` carries the real interned Names for the name_eq
// checks; `poison` is the armed iota-oracle flag.
// ════════════════════════════════════════════════════════════════════════════

pub struct Verifier<'env> {
    pub env: &'env [(Name, Option<Expr>)],
    pub ctors: &'env [(Name, u32)],
    pub quots: &'env QuotNames,
    pub poison: bool,
}

impl<'env> Verifier<'env> {
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
    fn try_iota_reduction(&self, _e: &Expr) -> Option<Expr> {
        None
    }

    // ── try_quot_reduction: the whnf App-arm quot-leaf (cert/reduction.rs:296
    //    + tc/reduction/mod.rs:695 lift|ind dispatch). ──
    fn try_quot_reduction(&self, e: &Expr) -> Option<Expr> {
        let head = e.get_app_fn();
        let name = match &head.kind {
            ExprKind::Const(name, _levels) => name.clone(),
            _ => return None,
        };
        let is_lift = name_eq(&name, &self.quots.quot_lift);
        let is_ind = name_eq(&name, &self.quots.quot_ind);
        if !is_lift && !is_ind {
            return None;
        }
        let args = e.get_app_args();
        if is_lift {
            self.try_quot_lift_reduction(&args)
        } else {
            self.try_quot_ind_reduction(&args)
        }
    }

    // ── VERBATIM `try_quot_lift_reduction` (quot.rs:598), method form with the
    //    verifier's whnf. `poison` (armed) extracts major_args[1] instead of
    //    major_args[2] — a reduce that returns the WRONG term. ──
    fn try_quot_lift_reduction(&self, args: &[Expr]) -> Option<Expr> {
        // Quot.lift has 6 arguments: α, r, β, f, h, q.
        if args.len() < 6 {
            return None;
        }
        let major = &args[5];
        let major_whnf = self.whnf_impl(major);
        let major_head = major_whnf.get_app_fn();
        let mk_name = match &major_head.kind {
            ExprKind::Const(mk_name, _) => mk_name.clone(),
            _ => return None,
        };
        if !name_eq(&mk_name, &self.quots.quot_mk) {
            return None;
        }
        // Quot.mk has 3 arguments: α, r, a.
        let major_args = major_whnf.get_app_args();
        if major_args.len() < 3 {
            return None;
        }
        // The value being quoted (major_args[2]); poison picks [1] (=r) instead.
        let a = if self.poison {
            &major_args[1]
        } else {
            &major_args[2]
        };
        let f = &args[3];
        // Result: f a (extra..); elim_arity = 6.
        let mut result = Expr::app(f.clone(), a.clone());
        let elim_arity: usize = 6;
        let mut i = elim_arity;
        while i < args.len() {
            result = Expr::app(result, args[i].clone());
            i += 1;
        }
        Some(result)
    }

    // ── VERBATIM `try_quot_ind_reduction` (quot.rs:679). elim_arity = 5. ──
    fn try_quot_ind_reduction(&self, args: &[Expr]) -> Option<Expr> {
        // Quot.ind has 5 arguments: α, r, β, f, q.
        if args.len() < 5 {
            return None;
        }
        let major = &args[4];
        let major_whnf = self.whnf_impl(major);
        let major_head = major_whnf.get_app_fn();
        let mk_name = match &major_head.kind {
            ExprKind::Const(mk_name, _) => mk_name.clone(),
            _ => return None,
        };
        if !name_eq(&mk_name, &self.quots.quot_mk) {
            return None;
        }
        let major_args = major_whnf.get_app_args();
        if major_args.len() < 3 {
            return None;
        }
        let a = if self.poison {
            &major_args[1]
        } else {
            &major_args[2]
        };
        let f = &args[3];
        let mut result = Expr::app(f.clone(), a.clone());
        let elim_arity: usize = 5;
        let mut i = elim_arity;
        while i < args.len() {
            result = Expr::app(result, args[i].clone());
            i += 1;
        }
        Some(result)
    }

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
}

// ════════════════════════════════════════════════════════════════════════════
// Iota scenario terms.
//   α = Sort(Param u), r = Const("r"), β = Sort(Param v), f = Const("f"),
//   h = Const("h"), a = App(Const("g"), Const("a")) (a non-trivial quoted value
//   so `f a` is payload-deep).
//   case 0: redex (6 args)         -> f a
//   case 1: non-redex (major=Const)-> stuck (Quot.lift head)
//   case 2: redex + 1 extra arg    -> (f a) extra
//   case 3: Quot.ind redex (5 args)-> f a
// ════════════════════════════════════════════════════════════════════════════

fn nm1(s: &str) -> Name {
    fold_step(name_anon(), s)
}

fn iota_alpha() -> Expr {
    Expr::sort(Level::param(nm_u()))
}
fn iota_beta() -> Expr {
    Expr::sort(Level::param(nm_v()))
}
fn iota_r() -> Expr {
    Expr::cnst(nm1("r"))
}
fn iota_f() -> Expr {
    Expr::cnst(nm1("f"))
}
fn iota_h() -> Expr {
    Expr::cnst(nm1("h"))
}
fn iota_a() -> Expr {
    Expr::app(Expr::cnst(nm1("g")), Expr::cnst(nm1("a")))
}
fn iota_extra() -> Expr {
    Expr::cnst(nm1("extra"))
}

fn quot_mk_app(qn: &QuotNames) -> Expr {
    // Quot.mk α r a
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(qn.quot_mk.clone(), vec![Level::param(nm_u())]),
                iota_alpha(),
            ),
            iota_r(),
        ),
        iota_a(),
    )
}

fn build_iota_term(case: u64, qn: &QuotNames) -> Expr {
    if case == 3 {
        // Quot.ind α r β f (Quot.mk α r a)  -> f a
        let mut ind = Expr::const_(qn.quot_ind.clone(), vec![Level::param(nm_u())]);
        let args = [
            iota_alpha(),
            iota_r(),
            iota_beta(),
            iota_f(),
            quot_mk_app(qn),
        ];
        let mut i = 0usize;
        while i < args.len() {
            ind = Expr::app(ind, args[i].clone());
            i += 1;
        }
        return ind;
    }
    // Quot.lift-headed.
    let mut lift = Expr::const_(
        qn.quot_lift.clone(),
        vec![Level::param(nm_u()), Level::param(nm_v())],
    );
    let major: Expr = if case == 1 {
        // NON-redex: major head is a plain Const (not Quot.mk).
        Expr::app(
            Expr::app(Expr::app(Expr::cnst(nm1("NotMk")), iota_alpha()), iota_r()),
            iota_a(),
        )
    } else {
        quot_mk_app(qn)
    };
    let base = [
        iota_alpha(),
        iota_r(),
        iota_beta(),
        iota_f(),
        iota_h(),
        major,
    ];
    let mut i = 0usize;
    while i < base.len() {
        lift = Expr::app(lift, base[i].clone());
        i += 1;
    }
    if case == 2 {
        lift = Expr::app(lift, iota_extra());
    }
    lift
}

// ════════════════════════════════════════════════════════════════════════════
// MONO ROOTS (#[no_mangle]).
// ════════════════════════════════════════════════════════════════════════════

/// ROOT 1 — build an axiom TYPE and write it out (deep-compared native == JIT +
/// meta word). `blind` selects the corrupted variant for kind 2 (lift) / 4
/// (sound).
#[unsafe(no_mangle)]
pub extern "C" fn quot_axiom_root(out: *mut Expr, kind: u64, blind: u64) {
    let e = build_axiom(kind, blind != 0);
    unsafe {
        std::ptr::write(out, e);
    }
}

/// ROOT 2 — run the iota reduction (whnf) on a scenario term and write the
/// result (deep-compared native == JIT + meta word). `poison` arms the wrong-arg
/// iota oracle.
#[unsafe(no_mangle)]
pub extern "C" fn quot_iota_root(out: *mut Expr, case: u64, poison: u64) {
    let env: Vec<(Name, Option<Expr>)> = Vec::new();
    let ctors: Vec<(Name, u32)> = Vec::new();
    let qn = quot_names();
    let v = Verifier {
        env: &env,
        ctors: &ctors,
        quots: &qn,
        poison: poison != 0,
    };
    let term = build_iota_term(case, &qn);
    let result = v.whnf_impl(&term);
    unsafe {
        std::ptr::write(out, result);
    }
}

/// ROOT 3 — the interned quot Names (for cached_hash golden pins):
///   0 Quot | 1 Quot.mk | 2 Quot.lift | 3 Quot.ind | 4 Quot.sound | 5 Eq
///   6 u | 7 v
#[unsafe(no_mangle)]
pub extern "C" fn quot_names_probe_root(out: *mut Name, idx: u64) {
    let n = if idx == 0 {
        nm_quot()
    } else if idx == 1 {
        nm_quot_mk()
    } else if idx == 2 {
        nm_quot_lift()
    } else if idx == 3 {
        nm_quot_ind()
    } else if idx == 4 {
        nm_quot_sound()
    } else if idx == 5 {
        nm_eq()
    } else if idx == 6 {
        nm_u()
    } else if idx == 7 {
        nm_v()
    } else {
        name_anon()
    };
    unsafe {
        std::ptr::write(out, n);
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Standalone native smoke harness (NOT part of any emitted root).
// ════════════════════════════════════════════════════════════════════════════

fn deep_eq(a: &Expr, b: &Expr) -> bool {
    if a.meta.raw() != b.meta.raw() {
        return false;
    }
    match (&a.kind, &b.kind) {
        (ExprKind::BVar(x), ExprKind::BVar(y)) => x == y,
        (ExprKind::FVar(x), ExprKind::FVar(y)) => x == y,
        (ExprKind::Sort(x), ExprKind::Sort(y)) => x == y,
        (ExprKind::Const(n1, l1), ExprKind::Const(n2, l2)) => name_eq(n1, n2) && l1 == l2,
        (ExprKind::Lit(x), ExprKind::Lit(y)) => x == y,
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => deep_eq(f1, f2) && deep_eq(a1, a2),
        (ExprKind::Lam(b1, t1, y1), ExprKind::Lam(b2, t2, y2)) => {
            b1 == b2 && deep_eq(t1, t2) && deep_eq(y1, y2)
        }
        (ExprKind::Pi(b1, t1, y1), ExprKind::Pi(b2, t2, y2)) => {
            b1 == b2 && deep_eq(t1, t2) && deep_eq(y1, y2)
        }
        (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
            name_eq(n1, n2) && i1 == i2 && deep_eq(e1, e2)
        }
        (ExprKind::MData(t1, e1), ExprKind::MData(t2, e2)) => t1 == t2 && deep_eq(e1, e2),
        _ => false,
    }
}

fn via_axiom(kind: u64, blind: u64) -> Expr {
    let mut slot = std::mem::MaybeUninit::<Expr>::uninit();
    unsafe {
        quot_axiom_root(slot.as_mut_ptr(), kind, blind);
        slot.assume_init()
    }
}
fn via_iota(case: u64, poison: u64) -> Expr {
    let mut slot = std::mem::MaybeUninit::<Expr>::uninit();
    unsafe {
        quot_iota_root(slot.as_mut_ptr(), case, poison);
        slot.assume_init()
    }
}

fn main() {
    let labels = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind", "Quot.sound"];
    for kind in 0u64..5 {
        let e = via_axiom(kind, 0);
        println!("{}: meta={:#018x}", labels[kind as usize], e.meta.raw());
    }
    // corruptions diverge.
    let lift = via_axiom(2, 0);
    let lift_blind = via_axiom(2, 1);
    assert!(!deep_eq(&lift, &lift_blind), "lift blind must diverge");
    let sound = via_axiom(4, 0);
    let sound_blind = via_axiom(4, 1);
    assert!(!deep_eq(&sound, &sound_blind), "sound blind must diverge");

    // iota
    for case in 0u64..4 {
        let r = via_iota(case, 0);
        println!("iota case {case}: meta={:#018x}", r.meta.raw());
    }
    let r0 = via_iota(0, 0);
    let r0p = via_iota(0, 1);
    assert!(!deep_eq(&r0, &r0p), "poison iota must diverge");

    for idx in 0u64..8 {
        let mut slot = std::mem::MaybeUninit::<Name>::uninit();
        let n = unsafe {
            quot_names_probe_root(slot.as_mut_ptr(), idx);
            slot.assume_init()
        };
        println!("name {idx}: {:#018x}", n.cached_hash);
    }
    println!("quotient slice smoke OK");
}
