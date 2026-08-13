// R19 — THE RECURSOR IOTA REDUCTION on a real inductive family: the computation
// rule that makes inductives ACTUALLY COMPUTE. This is soundness-relevant — a
// wrong iota reduction means the kernel accepts a wrong computation (Nat.rec
// computing the wrong successor case would let you prove wrong equalities). This
// completes the inductive-computation picture on the modern stack: R17 (the
// inductive well-formedness CHECKS) + R5 (the recursor TYPE) + R19 (the recursor
// IOTA REDUCTION), all on production-exact Names + full Level + compute_meta.
//
// THE IOTA RULE, as the modern kernel factors it, is TWO cooperating pieces:
//   (1) build_recursor_rule_rhs (inductive_recursor_rules.rs:175) precompiles,
//       per constructor, the RHS lambda
//         λ params. λ motives. λ minors. λ fields.
//           minor_k field0 .. fieldn IH0 .. IHm
//       — this is where MINOR SELECTION (the `minor_k` BVar picks the RIGHT minor
//       premise for ctor_idx) and the RECURSIVE IH (for each recursive field,
//       `rec params motives minors field` — the induction hypothesis, in the
//       right position/order) genuinely LIVE. VERBATIM from R5.
//   (2) try_iota_reduction (cert/reduction.rs:128) APPLIES that RHS: it whnf's
//       the major premise to a constructor head, selects the rule by ctor index
//       (name-verified) / by-name fallback, extracts the constructor fields,
//       instantiates level params, applies params+motives+minors+fields, and
//       lets whnf beta-reduce. VERBATIM from cert/reduction.rs, wired at the whnf
//       App-arm (whnf_inner:61-66).
// Together (1)+(2) ARE the recursor iota rule. A multi-step full normalize (nf)
// drives whnf repeatedly so each IH re-fires the recursor — exercising the IH
// construction RECURSIVELY (Nat.rec over succ(succ zero)) reduces all the way to
// `s (succ zero) (s zero z)`).
//
// REAL INDUCTIVE FAMILIES (production-exact Names, non-mutual, 0 params/indices):
//   * Nat  { Nat.zero : Nat ; Nat.succ : Nat -> Nat }  with Nat.rec  — the
//     canonical recursive inductive (base-case iota + successor iota with the
//     recursive IH; ONE recursive field).
//   * Tree { Tree.leaf : Nat -> Tree ; Tree.node : Tree -> Tree -> Tree } with
//     Tree.rec — a TWO-constructor family exercising (i) MINOR SELECTION
//     (leaf vs node pick different minors), (ii) a ctor with a NON-recursive
//     field (leaf's Nat), and (iii) TWO recursive IHs in the right ORDER
//     (node's left before right).
//
// SCENARIOS (each native == JIT, payload-deep + ExprMeta bit-identical):
//   0  Nat.rec C z s Nat.zero                      -whnf-> z                (base iota)
//   1  Nat.rec C z s (succ zero)                   -whnf-> s zero (Nat.rec C z s zero)
//                                                          (one-step: IH CONSTRUCTED, not yet reduced)
//   2  Nat.rec C z s (succ (succ zero))            -nf->   s (succ zero) (s zero z)   (multi-step)
//   3  Nat.rec C z s (succ^3 zero)                 -nf->   s (succ^2 zero) (s (succ zero) (s zero z))
//   4  Tree.rec C ml mn (node (leaf a) (leaf b))   -nf->   mn (leaf a) (leaf b) (ml a) (ml b)
//                                                          (minor selection + non-rec field + 2 IHs in order)
//   5  Nat.rec C z s (FVar x)                      -whnf-> STUCK (non-redex left unchanged)
//   6  Nat.rec C z s (Lit 2)                       -nf->   s (Lit 1) (s (Lit 0) z)
//                                                          (nat_lit_to_constructor feeds iota)
//   7  Nat.rec C z s (succ zero) extra             -whnf-> s zero (Nat.rec C z s zero) extra  (extras loop)
//
// THE LOAD-BEARING / SOUNDNESS PROOF (the R17/R18 pattern) — a POISONED iota
// reduces to a DIFFERENT term, native == JIT (structural + meta). build_rec_env
// bakes an armed `poison` into the precompiled rules:
//   * poison == 1  MINOR SELECTION corrupted: minor_bvar reversed within the
//     block (ctor_idx -> n_minors-1-ctor_idx). For Nat this makes `succ` select
//     the ZERO minor and `zero` select the SUCC minor — `Nat.rec C z s (succ k)`
//     reduces to `z k (..)` instead of `s k (..)`; for Tree, `node` selects `ml`
//     (the leaf minor) instead of `mn`. A wrong minor = a wrong computation.
//   * poison == 2  the RECURSIVE IH DROPPED: the `body = App(body, ih)` step is
//     gated off, so `Nat.rec C z s (succ k)` reduces to `s k` (missing the
//     recursive result) and Tree.node to `mn (leaf a) (leaf b)` (arity 4 -> 2).
//     A dropped IH = a non-computing recursor.
// Each poisoned reduction DIVERGES from the correct one (asserted !deep_eq,
// structural tree-shape independent of the meta primitive) native == JIT — the
// iota rule is proven soundness-critical in compiled machine code. And the STUCK
// non-redex (scenario 5) is left correctly unchanged (a recursor applied to a
// variable does NOT reduce).
//
// MODELED BOUNDARIES (which iota sub-paths are transcribed vs modeled; whether
// the modern stack genuinely flows through):
//   * Names: FULLY MODERN. Every family/ctor/recursor Name is the production
//     `Name` built in-module from literal parts (`from_string_uncached` unrolled,
//     name.rs:557-565; no interner on this path, name.rs:578 — the R5 finding),
//     the `.rec` names DERIVED in-module (`name_append_rec`, no table). Every
//     name comparison the reduction performs (is-recursor? which ctor? rule
//     match?) is the PRODUCTION `name_eq` (hash fast-path + structural walk).
//     The 8 family cached_hashes are pinned to the R4-R7 murmur-chain goldens
//     (Tree.rec == 0x293412c406e2a88e, the round-4 pin, as an anchor).
//   * Level: the FULL production 5-variant {Zero,Succ,Max,IMax,Param} (R18
//     verbatim). The recursor carries ONE motive-universe param `u`; the
//     inductives are monomorphic (Sort(Succ Zero) = Type). instantiate_level_
//     params_direct runs at the iota RHS-instantiation site over params=[u],
//     levels=[Param u] — a genuine structural level-substitution WALK that is
//     identity on these matching inputs (documented inert-on-input; the level-
//     UNIFICATION / normalize machinery is not reached by iota, exactly as
//     production, and is verified R6).
//   * try_iota_reduction: transcribed VERBATIM from cert/reduction.rs:128 (the
//     Classical certificate-verifier reduction), owned-args form (the established
//     get_app_args -> Vec<Expr> convention). The Cubical/HIT sub-paths
//     (CubicalPathApp / CubicalHComp / recursor-over-hcomp), the K-reduction
//     (`is_k` / to_cnstr_when_k), and struct-eta of the major (try_eta_struct)
//     that the tc/reduction/mod.rs variant carries are STRUCTURALLY ABSENT here
//     (Classical mode, is_k=false, no structures) — the cert reduction omits them
//     by construction; declared. The nat-LITERAL major arm (nat_lit_to_constructor)
//     IS transcribed and LIVE (scenario 6); the >u64 BigNat path is out of scope
//     (R13 verified the Nat reducer).
//   * whnf: the cert whnf_inner (App beta / iota / Let zeta / Const-no-delta /
//     Proj-iota / MData), VERBATIM MINUS the reduce_nat literal fast-path (which
//     would fold `Nat.succ Nat.zero` to a Lit BEFORE the recursor sees it — R13
//     verified reduce_nat separately; omitting it keeps the majors in ctor form
//     so they drive the recursor iota, which is exactly R19's surface) and MINUS
//     the try_quot_reduction leg (R18). No delta definitions in the iota
//     registry, so the Const arm is a no-op (get_recursor/get_constructor are the
//     only env lookups). reduce_proj is present (faithful) but unreached (no Proj
//     terms).
//   * nf (full normalize) is a TEST DRIVER, not a kernel function — the kernel
//     exposes only whnf; nf(e) = whnf then structurally normalize children,
//     driving the multi-step reduction so the IH is exercised recursively.
//     Labeled as such.
//   * The eliminator_type passed to build_recursor_rule_rhs is a hand-built
//     recursor-type telescope (correct leading-binder count: motive + minors;
//     faithful domain shapes). It is REDUCTION-INERT and RESULT-META-INERT: iota
//     fully saturates the RHS lambda, so beta consumes every wrapper binder and
//     the reduced term (and its meta) depend only on the RHS BODY (minor
//     selection + fields + IH) — never on the wrapper types. The full production
//     build_recursor_type was verified in R5.
//   * compute_meta: PRODUCTION (Const arm expr/kind.rs:567-581 — levels_hash
//     mixed, has_level_param derived); payload hashes flow through the KaniHasher
//     (B7 — clean's own cfg(kani) hasher). Reduced-term meta words are internally
//     consistent + native == JIT bit-identical; the real-Name cached_hashes ARE
//     pinned to the murmur golden. The soundness proof rests on STRUCTURAL
//     divergence (deep_eq), independent of the meta primitive.
//   * env / delta: the registry is the RecEnv (Vec<RecursorVal>+Vec<ConstructorVal>,
//     linear-scan get_recursor/get_constructor via name_eq); no delta defs.
//   * Arc<Expr>/Arc<Level>/Arc<Name>/Arc<str> children are real; Arc::new + Arc
//     deref INLINED; clones/from bound to faithful host shims (landed
//     convention). Drops not emitted (leak model — every Name/Expr immortal).
//   * BinderInfo::Default/Implicit -> the production `BinderData` scalar
//     (Default => {info:0,mult:2(Many)}, Implicit => {info:1,mult:2});
//     compute_meta ignores BinderData, so verification-inert (native == JIT).
//
// SOURCES (verbatim transcription targets in $HOME/clean/crates/clean-kernel/src):
//   cert/reduction.rs        — whnf_impl/whnf_inner (:34/:39), reduce_proj (:99),
//                              try_iota_reduction (:128).
//   env/inductive_recursor_rules.rs — build_recursor_rule_rhs (:175),
//                              remap_residual_index_bvars (:51), count_pi_binders
//                              (:24), collect_pi_domains (:39).
//   env/inductive_recursor.rs — get_constructor_field_types (:915),
//                              get_recursive_field_flags (:877),
//                              field_is_eliminably_recursive (:902).
//   inductive/mod.rs         — RecursorVal/RecursorRule/ConstructorVal (:64-148),
//                              RecursorArgOrder (:244), count_pi_args (:608),
//                              get_return_type (:650).
//   expr/subst.rs            — instantiate_level_params_direct (:954).
//   expr/constructors.rs     — is_lam (:230).
//   name.rs / level/mod.rs / expr/meta.rs / expr/kind.rs — the modern-stack
//                              Name / Level / ExprMeta / compute_meta (VERBATIM
//                              the R4-R7 / R18 transcriptions).
//
// Crate name is load-bearing (appears in mangled extern-leaf symbols): it MUST
// stay `clean_recursor_iota_slice`.
//
// REGEN (one module per root; trust-ir main >= 375c800 — NO frontend changes):
//   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//   cd $HOME/trust-ir/frontend
//   env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//     $S/bin/cargo run --bin trust_ir_mir -- \
//     ../../trust-cg/crates/trust-cg-codegen/tests/slices/clean_recursor_iota_slice.rs \
//     --crate-type=lib --mir-emit-closure <root> <out.tir>
//   roots: iota_reduce_root | iota_names_probe_root

#![allow(dead_code)]
#![allow(clippy::all)]
#![allow(unused_variables)]
#![allow(unused_parens)]

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
// Expr helpers added for R19 (lift/lift_from wrappers over lift_at; is_lam).
// VERBATIM Expr::lift (subst.rs:495) / Expr::lift_from (subst.rs:511) /
// Expr::is_lam (constructors.rs:230).
// ════════════════════════════════════════════════════════════════════════════

impl Expr {
    pub fn lift(&self, amount: u32) -> Expr {
        self.lift_at(0, amount)
    }
    pub fn lift_from(&self, start: u32, amount: u32) -> Expr {
        self.lift_at(start, amount)
    }
    pub fn is_lam(&self) -> bool {
        matches!(self.kind, ExprKind::Lam(_, _, _))
    }
}

#[inline]
fn usize_to_u32(value: usize) -> u32 {
    u32::try_from(value).unwrap_or(u32::MAX)
}

// ════════════════════════════════════════════════════════════════════════════
// Real production Names for the two families (from_string_uncached unrolled;
// no split('.') in the slice — dotted names are nested fold_step, exactly as
// production from_string folds them). `.rec` derived in-module (name_append_rec).
// ════════════════════════════════════════════════════════════════════════════

pub fn name_append_rec(head: &Name) -> Name {
    fold_step(head.clone(), "rec")
}

fn nm1(s: &str) -> Name {
    fold_step(name_anon(), s)
}
fn nm_nat() -> Name {
    fold_step(name_anon(), "Nat")
}
fn nm_nat_zero() -> Name {
    fold_step(fold_step(name_anon(), "Nat"), "zero")
}
fn nm_nat_succ() -> Name {
    fold_step(fold_step(name_anon(), "Nat"), "succ")
}
fn nm_nat_rec() -> Name {
    name_append_rec(&nm_nat())
}
fn nm_tree() -> Name {
    fold_step(name_anon(), "Tree")
}
fn nm_tree_leaf() -> Name {
    fold_step(fold_step(name_anon(), "Tree"), "leaf")
}
fn nm_tree_node() -> Name {
    fold_step(fold_step(name_anon(), "Tree"), "node")
}
fn nm_tree_rec() -> Name {
    name_append_rec(&nm_tree())
}
fn nm_u() -> Name {
    fold_step(name_anon(), "u")
}

// ════════════════════════════════════════════════════════════════════════════
// The InductiveType/Ctor the family builders + build_recursor_rule_rhs read.
// (VERBATIM shape from clean_mutual_recursor_realnames_slice.rs.)
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

// ════════════════════════════════════════════════════════════════════════════
// The recursor-build / ctor-info helpers (VERBATIM from
// inductive/mod.rs + env/inductive_recursor*.rs; R5-verified).
// ════════════════════════════════════════════════════════════════════════════

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

// VERBATIM `get_return_type` (inductive/mod.rs:650) — walk past the Pi telescope.
pub(crate) fn get_return_type(expr: &Expr) -> &Expr {
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = &current.kind {
        current = body;
    }
    current
}

// MODELED `consume_type_annotations` (inductive/mod.rs:676) — no synthetic domain
// uses a reserved wrapper Name, so a faithful no-op (the format!-render peel is
// gap-4 modeled out; R5 convention).
pub(crate) fn consume_type_annotations(expr: &Expr) -> &Expr {
    expr
}

// VERBATIM `get_constructor_field_types` (inductive_recursor.rs:915).
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

// Modeled `ind_name_set.contains(name)` — scan, each compare the production
// `Name::eq` (= name_eq).
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

// VERBATIM `field_is_eliminably_recursive` (inductive_recursor.rs:902).
pub(crate) fn field_is_eliminably_recursive(field_ty: &Expr, ind_name_set: &[Name]) -> bool {
    let ret_ty = get_return_type(field_ty);
    let head = ret_ty.get_app_fn();
    match &head.kind {
        ExprKind::Const(name, _) => name_in_set(name, ind_name_set),
        _ => false,
    }
}

// VERBATIM `get_recursive_field_flags` (inductive_recursor.rs:877).
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

// VERBATIM `get_constructor_return_indices` (inductive_recursor.rs:951).
// (Dead on the 0-index families; present for the verbatim RHS builder.)
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

// VERBATIM `remap_residual_index_bvars` (inductive_recursor_rules.rs:51) — the
// NON-minor variant used by the rule RHS. Dead on the 0-index families; present
// for the verbatim RHS builder.
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
// THE SOUNDNESS-CRITICAL FN #1 — `build_recursor_rule_rhs`, VERBATIM from
// inductive_recursor_rules.rs:175 (the `all_types.len() > 1` mutual branch is
// present but dead on the single-inductive families here). This is where MINOR
// SELECTION (`minor_bvar`) and the RECURSIVE IH construction genuinely live.
//
// TWO ARMED POISONS (R17/R18 pattern; the load-bearing soundness proof):
//   poison_minor  reverses the minor selection within the block
//                 (ctor_idx -> n_minors-1-ctor_idx) — a WRONG minor premise.
//   poison_ih     gates OFF the whole recursive-field IH loop — a DROPPED IH.
// Everything else is byte-for-byte the production text.
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
    poison_minor: bool,
    poison_ih: bool,
) -> Expr {
    let nf = num_fields as usize;
    let np = num_params as usize;
    let nm = num_motives as usize;
    let n_minors = num_ctors;
    let total_binders = np + nm + n_minors + nf;

    // MINOR SELECTION (production: `nf + n_minors - 1 - ctor_idx`). poison_minor
    // reverses the ctor index within the block — the wrong minor premise.
    let minor_bvar = if poison_minor {
        usize_to_u32(nf + n_minors - 1 - (n_minors - 1 - ctor_idx))
    } else {
        usize_to_u32(nf + n_minors - 1 - ctor_idx)
    };
    let mut body = Expr::bvar(minor_bvar);

    // Apply all fields to minor: minor field_0 .. field_{nf-1}.
    {
        let mut i: usize = 0;
        while i < nf {
            let field_bvar = usize_to_u32(nf - 1 - i);
            body = Expr::app(body, Expr::bvar(field_bvar));
            i += 1;
        }
    }

    // rec_levels = rec_level_params.iter().map(|n| Level::param(n.clone())).collect()
    let mut rec_levels: Vec<Level> = Vec::new();
    {
        let mut _li = 0usize;
        while _li < rec_level_params.len() {
            rec_levels.push(Level::Param(rec_level_params[_li].clone()));
            _li += 1;
        }
    }

    // THE RECURSIVE IH — for each recursive field, apply the induction hypothesis
    // `rec params motives minors [indices] (field xs)`. poison_ih drops this loop.
    if !poison_ih {
        let mut i: usize = 0;
        while i < recursive_flags.len() {
            let is_recursive = recursive_flags[i];
            if is_recursive {
                let n_pis = match field_types.get(i) {
                    Some(ft) => count_pi_binders(ft),
                    None => 0,
                };
                let shift = n_pis;

                // MUTUAL branch (dead here): IH names the recursor of the type the
                // field returns to; else arms are `rec_name.clone()`.
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

                let mut ih = Expr::const_(ih_rec_name, rec_levels.clone());

                // Apply params (outermost group).
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

                // Apply index arguments (dead on the 0-index families).
                if num_indices > 0 {
                    if let Some(field_ty) = field_types.get(i) {
                        let indices = get_constructor_return_indices(field_ty, num_params);
                        {
                            let mut _ix = 0usize;
                            while _ix < indices.len() {
                                let remapped = remap_residual_index_bvars(
                                    &indices[_ix],
                                    i,
                                    np,
                                    nf,
                                    n_minors,
                                    nm,
                                    n_pis,
                                );
                                ih = Expr::app(ih, remapped);
                                _ix += 1;
                            }
                        }
                    }
                }

                // Apply the recursive field as major premise.
                let mut major = Expr::bvar(usize_to_u32(nf - 1 - i + shift));
                {
                    let mut _k = n_pis;
                    while _k > 0 {
                        _k -= 1;
                        major = Expr::app(major, Expr::bvar(usize_to_u32(_k)));
                    }
                }
                ih = Expr::app(ih, major);

                // Wrap IH in lambda binders for Pi-bound variables (reflexive
                // fields; dead on the direct-recursive families here).
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

    let lift_amount = usize_to_u32(nm + n_minors);
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
    {
        let mut _mi = minor_domain_types.len();
        while _mi > 0 {
            _mi -= 1;
            result = Expr::lam(bi_default(), minor_domain_types[_mi].clone(), result);
        }
    }
    {
        let mut _mo = motive_domain_types.len();
        while _mo > 0 {
            _mo -= 1;
            result = Expr::lam(bi_default(), motive_domain_types[_mo].clone(), result);
        }
    }
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
// Level-param substitution + is_lam (used by try_iota_reduction's RHS
// instantiation). instantiate_level_params_direct is transcribed as a direct
// structural walk equivalent to the production `fold_opt_or_clone(
// LevelParamSubstSlice)` (subst.rs:954) — substitute Param names in Sort/Const
// levels, recurse structurally. On params=[u], levels=[Param u] it is identity
// (the recursor's own level param), which is the correct behavior.
// ════════════════════════════════════════════════════════════════════════════

fn subst_level(l: &Level, params: &[Name], levels: &[Level]) -> Level {
    match l {
        Level::Zero => Level::Zero,
        Level::Succ(x) => Level::Succ(Arc::new(subst_level(x, params, levels))),
        Level::Max(a, b) => Level::Max(
            Arc::new(subst_level(a, params, levels)),
            Arc::new(subst_level(b, params, levels)),
        ),
        Level::IMax(a, b) => Level::IMax(
            Arc::new(subst_level(a, params, levels)),
            Arc::new(subst_level(b, params, levels)),
        ),
        Level::Param(n) => {
            let mut i = 0usize;
            while i < params.len() {
                if name_eq(&params[i], n) {
                    return levels[i].clone();
                }
                i += 1;
            }
            Level::Param(n.clone())
        }
    }
}

fn instantiate_level_params_direct(e: &Expr, params: &[Name], levels: &[Level]) -> Expr {
    if params.is_empty() {
        return e.clone();
    }
    match &e.kind {
        ExprKind::Sort(l) => Expr::sort(subst_level(l, params, levels)),
        ExprKind::Const(n, ls) => {
            let mut out: Vec<Level> = Vec::new();
            let mut i = 0usize;
            while i < ls.len() {
                out.push(subst_level(&ls[i], params, levels));
                i += 1;
            }
            Expr::const_(n.clone(), out)
        }
        ExprKind::App(f, a) => Expr::app(
            instantiate_level_params_direct(f, params, levels),
            instantiate_level_params_direct(a, params, levels),
        ),
        ExprKind::Lam(bd, ty, body) => Expr::lam(
            *bd,
            instantiate_level_params_direct(ty, params, levels),
            instantiate_level_params_direct(body, params, levels),
        ),
        ExprKind::Pi(bd, ty, body) => Expr::pi(
            *bd,
            instantiate_level_params_direct(ty, params, levels),
            instantiate_level_params_direct(body, params, levels),
        ),
        ExprKind::Let(nm, ty, val, body, nd) => Expr::from_kind(ExprKind::Let(
            nm.clone(),
            Arc::new(instantiate_level_params_direct(ty, params, levels)),
            Arc::new(instantiate_level_params_direct(val, params, levels)),
            Arc::new(instantiate_level_params_direct(body, params, levels)),
            *nd,
        )),
        ExprKind::Proj(nm, idx, ex) => Expr::from_kind(ExprKind::Proj(
            nm.clone(),
            *idx,
            Arc::new(instantiate_level_params_direct(ex, params, levels)),
        )),
        _ => e.clone(),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// The RecursorVal / RecursorRule / ConstructorVal registry (VERBATIM shape from
// inductive/mod.rs:64-148 + RecursorArgOrder :244; env getters are the linear-
// scan get_recursor/get_constructor over name_eq — the SwissTable is a pure-
// performance model, B1).
// ════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RecursorArgOrder {
    MajorAfterMinors,
    MajorAfterMotive,
}

#[derive(Clone, Debug)]
pub struct RecursorRule {
    pub constructor_name: Name,
    pub num_fields: u32,
    pub recursive_fields: Vec<bool>,
    pub rhs: Expr,
}

#[derive(Clone, Debug)]
pub struct RecursorVal {
    pub name: Name,
    pub arg_order: RecursorArgOrder,
    pub level_params: Vec<Name>,
    pub inductive_name: Name,
    pub num_params: u32,
    pub num_indices: u32,
    pub num_motives: u32,
    pub num_minors: u32,
    pub rules: Vec<RecursorRule>,
    pub is_k: bool,
}

#[derive(Clone, Debug)]
pub struct ConstructorVal {
    pub name: Name,
    pub inductive_name: Name,
    pub num_params: u32,
    pub num_fields: u32,
    pub constructor_idx: u32,
}

pub struct RecEnv {
    pub recs: Vec<RecursorVal>,
    pub ctors: Vec<ConstructorVal>,
}

impl RecEnv {
    pub fn get_recursor(&self, name: &Name) -> Option<&RecursorVal> {
        let mut i = 0usize;
        while i < self.recs.len() {
            if name_eq(&self.recs[i].name, name) {
                return Some(&self.recs[i]);
            }
            i += 1;
        }
        None
    }
    pub fn get_constructor(&self, name: &Name) -> Option<&ConstructorVal> {
        let mut i = 0usize;
        while i < self.ctors.len() {
            if name_eq(&self.ctors[i].name, name) {
                return Some(&self.ctors[i]);
            }
            i += 1;
        }
        None
    }
}

// VERBATIM `nat_lit_to_constructor` (tc/reduction/nat.rs:340), u64 form: the lazy
// `Nat.succ (lit (n-1))` / `Nat.zero` expansion (the >u64 BigNat path is R13's).
fn nat_lit_to_constructor(n: u64) -> Expr {
    if n == 0 {
        Expr::const_(nm_nat_zero(), Vec::new())
    } else {
        Expr::app(
            Expr::const_(nm_nat_succ(), Vec::new()),
            Expr::from_kind(ExprKind::Lit(Literal::Nat(n - 1))),
        )
    }
}

// ════════════════════════════════════════════════════════════════════════════
// THE SOUNDNESS-CRITICAL FN #2 — the whnf + `try_iota_reduction` verifier
// (VERBATIM from cert/reduction.rs; owned-args form). See the header for the
// omitted reduce_nat fast-path (R13) / try_quot leg (R18) / Cubical+K+eta paths.
// ════════════════════════════════════════════════════════════════════════════

pub struct Verifier<'e> {
    pub env: &'e RecEnv,
}

impl<'e> Verifier<'e> {
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
                        app
                    }
                }
            }
            ExprKind::Let(_, _, val, body, _) => {
                let reduced = body.instantiate(val);
                self.whnf_impl(&reduced)
            }
            // No delta definitions in the iota registry.
            ExprKind::Const(_, _) => e.clone(),
            ExprKind::Proj(struct_name, idx, expr) => self.reduce_proj(struct_name, *idx, expr),
            ExprKind::MData(_, inner) => self.whnf_impl(inner),
            _ => e.clone(),
        }
    }

    // VERBATIM `reduce_proj` (cert/reduction.rs:99). Unreached (no Proj terms).
    fn reduce_proj(&self, struct_name: &Name, idx: u32, expr: &Expr) -> Expr {
        let expr_whnf = self.whnf_impl(expr);
        let head = expr_whnf.get_app_fn();
        if let ExprKind::Const(ctor_name, _) = &head.kind {
            if let Some(ctor_val) = self.env.get_constructor(ctor_name) {
                let args = expr_whnf.get_app_args();
                let field_idx = ctor_val.num_params as usize + idx as usize;
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

    // VERBATIM `try_iota_reduction` (cert/reduction.rs:128), owned-args.
    fn try_iota_reduction(&self, e: &Expr) -> Option<Expr> {
        let head = e.get_app_fn();
        let (rec_name, rec_levels) = match &head.kind {
            ExprKind::Const(rec_name, rec_levels) => (rec_name.clone(), rec_levels.clone()),
            _ => return None,
        };
        let rec_val = match self.env.get_recursor(&rec_name) {
            Some(r) => r,
            None => return None,
        };
        let args = e.get_app_args();

        let args_before_major = match rec_val.arg_order {
            RecursorArgOrder::MajorAfterMinors => {
                rec_val.num_params as usize
                    + rec_val.num_motives as usize
                    + rec_val.num_minors as usize
                    + rec_val.num_indices as usize
            }
            RecursorArgOrder::MajorAfterMotive => {
                rec_val.num_params as usize
                    + rec_val.num_motives as usize
                    + rec_val.num_indices as usize
            }
        };
        let required_args = match rec_val.arg_order {
            RecursorArgOrder::MajorAfterMinors => args_before_major + 1,
            RecursorArgOrder::MajorAfterMotive => {
                args_before_major + 1 + rec_val.num_minors as usize
            }
        };
        if args.len() < required_args {
            return None;
        }

        let major_whnf = self.whnf_impl(&args[args_before_major]);
        // nat-literal major -> constructor form (cert/reduction.rs:172).
        let major_whnf: Expr = match &major_whnf.kind {
            ExprKind::Lit(Literal::Nat(n)) => nat_lit_to_constructor(*n),
            _ => major_whnf,
        };

        let major_head = major_whnf.get_app_fn();
        let ctor_name = match &major_head.kind {
            ExprKind::Const(ctor_name, _) => ctor_name.clone(),
            _ => return None,
        };
        let ctor_val = match self.env.get_constructor(&ctor_name) {
            Some(c) => c,
            None => return None,
        };

        // Rule selection: fast index path (name-verified) / by-name fallback.
        let rule: &RecursorRule = if name_eq(&ctor_val.inductive_name, &rec_val.inductive_name) {
            match rec_val.rules.get(ctor_val.constructor_idx as usize) {
                Some(r) => r,
                None => return None,
            }
        } else {
            let mut found: Option<&RecursorRule> = None;
            let mut ri = 0usize;
            while ri < rec_val.rules.len() {
                if name_eq(&rec_val.rules[ri].constructor_name, &ctor_name) {
                    found = Some(&rec_val.rules[ri]);
                    break;
                }
                ri += 1;
            }
            match found {
                Some(r) => r,
                None => return None,
            }
        };

        let major_args = major_whnf.get_app_args();
        if (rule.num_fields as usize) > major_args.len() {
            return None;
        }
        let nparams = major_args.len() - rule.num_fields as usize;
        let mut fields: Vec<Expr> = Vec::new();
        {
            let mut fi = nparams;
            let end = nparams + rule.num_fields as usize;
            while fi < end {
                fields.push(major_args[fi].clone());
                fi += 1;
            }
        }

        if rec_levels.len() != rec_val.level_params.len() {
            return None;
        }

        let minors_start = match rec_val.arg_order {
            RecursorArgOrder::MajorAfterMinors => {
                rec_val.num_params as usize + rec_val.num_motives as usize
            }
            RecursorArgOrder::MajorAfterMotive => args_before_major + 1,
        };

        let mut result = if rule.rhs.is_lam() {
            let mut result =
                instantiate_level_params_direct(&rule.rhs, &rec_val.level_params, &rec_levels);
            let n_pm = rec_val.num_params as usize + rec_val.num_motives as usize;
            let n_pmm = n_pm + rec_val.num_minors as usize;
            match rec_val.arg_order {
                RecursorArgOrder::MajorAfterMinors => {
                    let mut i = 0usize;
                    while i < n_pmm {
                        let a = match args.get(i) {
                            Some(a) => a.clone(),
                            None => return None,
                        };
                        result = Expr::app(result, a);
                        i += 1;
                    }
                }
                RecursorArgOrder::MajorAfterMotive => {
                    let mut i = 0usize;
                    while i < n_pm {
                        let a = match args.get(i) {
                            Some(a) => a.clone(),
                            None => return None,
                        };
                        result = Expr::app(result, a);
                        i += 1;
                    }
                    let mut j = 0usize;
                    while j < rec_val.num_minors as usize {
                        let idx = minors_start + j;
                        let a = match args.get(idx) {
                            Some(a) => a.clone(),
                            None => return None,
                        };
                        result = Expr::app(result, a);
                        j += 1;
                    }
                }
            }
            let mut k = 0usize;
            while k < fields.len() {
                result = Expr::app(result, fields[k].clone());
                k += 1;
            }
            result
        } else {
            let minor_idx = minors_start + ctor_val.constructor_idx as usize;
            if minor_idx >= args.len() {
                return None;
            }
            let mut result = args[minor_idx].clone();
            let mut k = 0usize;
            while k < fields.len() {
                result = Expr::app(result, fields[k].clone());
                k += 1;
            }
            result
        };

        let extras_start = match rec_val.arg_order {
            RecursorArgOrder::MajorAfterMinors => args_before_major + 1,
            RecursorArgOrder::MajorAfterMotive => {
                args_before_major + 1 + rec_val.num_minors as usize
            }
        };
        {
            let mut i = extras_start;
            while i < args.len() {
                result = Expr::app(result, args[i].clone());
                i += 1;
            }
        }
        Some(result)
    }

    // Full normalize (nf) — a TEST DRIVER (the kernel exposes only whnf): whnf
    // then structurally normalize children, driving the multi-step reduction so
    // each IH re-fires the recursor (the IH exercised RECURSIVELY).
    fn nf(&self, e: &Expr) -> Expr {
        let h = self.whnf_impl(e);
        match &h.kind {
            ExprKind::App(_, _) => {
                let head = h.get_app_fn();
                let args = h.get_app_args();
                let mut result = self.nf(&head);
                let mut i = 0usize;
                while i < args.len() {
                    result = Expr::app(result, self.nf(&args[i]));
                    i += 1;
                }
                result
            }
            ExprKind::Lam(bd, ty, body) => Expr::lam(*bd, self.nf(ty), self.nf(body)),
            ExprKind::Pi(bd, ty, body) => Expr::pi(*bd, self.nf(ty), self.nf(body)),
            _ => h,
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// The two REAL inductive families + their (hand-built, reduction-inert)
// recursor-type telescopes.
// ════════════════════════════════════════════════════════════════════════════

fn nat_ty_e() -> Expr {
    Expr::const_(nm_nat(), Vec::new())
}
fn tree_ty_e() -> Expr {
    Expr::const_(nm_tree(), Vec::new())
}
// Type = Sort 1 = Sort(Succ Zero).
fn type1_e() -> Expr {
    Expr::sort(Level::Succ(Arc::new(Level::Zero)))
}

fn family_nat() -> Vec<InductiveType> {
    let mut ctors: Vec<Ctor> = Vec::new();
    ctors.push(Ctor {
        name: nm_nat_zero(),
        type_: nat_ty_e(), // Nat.zero : Nat
    });
    ctors.push(Ctor {
        name: nm_nat_succ(),
        type_: Expr::pi(bi_default(), nat_ty_e(), nat_ty_e()), // Nat.succ : Nat -> Nat
    });
    let mut out: Vec<InductiveType> = Vec::new();
    out.push(InductiveType {
        name: nm_nat(),
        type_: type1_e(),
        constructors: ctors,
    });
    out
}

fn family_tree() -> Vec<InductiveType> {
    let mut ctors: Vec<Ctor> = Vec::new();
    // Tree.leaf : Nat -> Tree   (a NON-recursive field)
    ctors.push(Ctor {
        name: nm_tree_leaf(),
        type_: Expr::pi(bi_default(), nat_ty_e(), tree_ty_e()),
    });
    // Tree.node : Tree -> Tree -> Tree   (two recursive fields)
    ctors.push(Ctor {
        name: nm_tree_node(),
        type_: Expr::pi(
            bi_default(),
            tree_ty_e(),
            Expr::pi(bi_default(), tree_ty_e(), tree_ty_e()),
        ),
    });
    let mut out: Vec<InductiveType> = Vec::new();
    out.push(InductiveType {
        name: nm_tree(),
        type_: type1_e(),
        constructors: ctors,
    });
    out
}

// Hand-built recursor-type telescopes: the correct leading-binder count
// (motive + minors) with faithful domain shapes. REDUCTION-INERT (beta consumes
// the RHS lambda wrappers; the full build_recursor_type is R5-verified).
fn build_elim_type_nat(u: &Name) -> Expr {
    let sort_u = Expr::sort(Level::param(u.clone()));
    let motive_dom = Expr::pi(bi_default(), nat_ty_e(), sort_u); // Nat -> Sort u
    let mz_dom = Expr::app(Expr::bvar(0), Expr::const_(nm_nat_zero(), Vec::new())); // motive Nat.zero
    let ms_dom = Expr::pi(
        bi_default(),
        nat_ty_e(), // (n:Nat) ->
        Expr::pi(
            bi_default(),
            Expr::app(Expr::bvar(1), Expr::bvar(0)), // motive n ->
            Expr::app(
                Expr::bvar(2),
                Expr::app(Expr::const_(nm_nat_succ(), Vec::new()), Expr::bvar(1)),
            ), // motive (succ n)
        ),
    );
    Expr::pi(
        bi_implicit(),
        motive_dom,
        Expr::pi(
            bi_default(),
            mz_dom,
            Expr::pi(
                bi_default(),
                ms_dom,
                Expr::pi(
                    bi_default(),
                    nat_ty_e(),
                    Expr::app(Expr::bvar(3), Expr::bvar(0)),
                ),
            ),
        ),
    )
}

fn build_elim_type_tree(u: &Name) -> Expr {
    let sort_u = Expr::sort(Level::param(u.clone()));
    let motive_dom = Expr::pi(bi_default(), tree_ty_e(), sort_u); // Tree -> Sort u
    // minor_leaf : (n:Nat) -> motive (Tree.leaf n)
    let ml_dom = Expr::pi(
        bi_default(),
        nat_ty_e(),
        Expr::app(
            Expr::bvar(1),
            Expr::app(Expr::const_(nm_tree_leaf(), Vec::new()), Expr::bvar(0)),
        ),
    );
    // minor_node : (l:Tree)->(r:Tree)->motive l->motive r->motive (Tree.node l r)
    let mn_dom = Expr::pi(
        bi_default(),
        tree_ty_e(),
        Expr::pi(
            bi_default(),
            tree_ty_e(),
            Expr::pi(
                bi_default(),
                Expr::app(Expr::bvar(2), Expr::bvar(1)),
                Expr::pi(
                    bi_default(),
                    Expr::app(Expr::bvar(3), Expr::bvar(1)),
                    Expr::app(
                        Expr::bvar(4),
                        Expr::app(
                            Expr::app(Expr::const_(nm_tree_node(), Vec::new()), Expr::bvar(3)),
                            Expr::bvar(2),
                        ),
                    ),
                ),
            ),
        ),
    );
    Expr::pi(
        bi_implicit(),
        motive_dom,
        Expr::pi(
            bi_default(),
            ml_dom,
            Expr::pi(
                bi_default(),
                mn_dom,
                Expr::pi(
                    bi_default(),
                    tree_ty_e(),
                    Expr::app(Expr::bvar(3), Expr::bvar(0)),
                ),
            ),
        ),
    )
}

// ════════════════════════════════════════════════════════════════════════════
// Build the recursor + constructor registry for a family, baking in the armed
// `poison` (0 none / 1 minor-selection / 2 dropped-IH).
// ════════════════════════════════════════════════════════════════════════════

fn build_rec_env(which_family: u64, poison: u64) -> RecEnv {
    let poison_minor = poison == 1;
    let poison_ih = poison == 2;
    let all_types = if which_family == 0 {
        family_nat()
    } else {
        family_tree()
    };
    let level_params: Vec<Name> = Vec::new(); // monomorphic families
    let ind = &all_types[0];
    let num_params: u32 = 0;
    let ind_name = ind.name.clone();
    let rec_name = name_append_rec(&ind_name);
    let u = nm_u();
    // rec_level_params = [u] ++ level_params
    let mut rec_level_params: Vec<Name> = Vec::new();
    rec_level_params.push(u.clone());
    {
        let mut i = 0usize;
        while i < level_params.len() {
            rec_level_params.push(level_params[i].clone());
            i += 1;
        }
    }
    let num_motives: u32 = 1;
    let type_arity = count_pi_args(&ind.type_);
    let num_indices = type_arity.saturating_sub(num_params);
    let num_ctors = ind.constructors.len();
    let num_minors = num_ctors as u32;
    let elim_ty = if which_family == 0 {
        build_elim_type_nat(&u)
    } else {
        build_elim_type_tree(&u)
    };

    let mut ind_name_set: Vec<Name> = Vec::new();
    ind_name_set.push(ind_name.clone());

    let mut rules: Vec<RecursorRule> = Vec::new();
    let mut ctors: Vec<ConstructorVal> = Vec::new();
    {
        let mut idx = 0usize;
        while idx < ind.constructors.len() {
            let ctor = &ind.constructors[idx];
            let ctor_arity = count_pi_args(&ctor.type_);
            let num_fields = ctor_arity.saturating_sub(num_params);
            let recursive_flags = get_recursive_field_flags(&ctor.type_, &ind_name_set, num_params);
            let field_types = get_constructor_field_types(&ctor.type_, num_params);
            let rhs = build_recursor_rule_rhs(
                &rec_name,
                &rec_level_params,
                num_params,
                num_motives,
                num_indices,
                num_fields,
                &recursive_flags,
                &field_types,
                num_ctors,
                idx,
                &elim_ty,
                &all_types,
                poison_minor,
                poison_ih,
            );
            rules.push(RecursorRule {
                constructor_name: ctor.name.clone(),
                num_fields,
                recursive_fields: recursive_flags,
                rhs,
            });
            ctors.push(ConstructorVal {
                name: ctor.name.clone(),
                inductive_name: ind_name.clone(),
                num_params,
                num_fields,
                constructor_idx: idx as u32,
            });
            idx += 1;
        }
    }
    let rec_val = RecursorVal {
        name: rec_name,
        arg_order: RecursorArgOrder::MajorAfterMinors,
        level_params: rec_level_params,
        inductive_name: ind_name,
        num_params,
        num_indices,
        num_motives,
        num_minors,
        rules,
        is_k: false,
    };
    let mut recs: Vec<RecursorVal> = Vec::new();
    recs.push(rec_val);
    RecEnv { recs, ctors }
}

// ════════════════════════════════════════════════════════════════════════════
// Scenario terms + driver.
// ════════════════════════════════════════════════════════════════════════════

fn c_e() -> Expr {
    Expr::cnst(nm1("C"))
}
fn z_e() -> Expr {
    Expr::cnst(nm1("z"))
}
fn s_e() -> Expr {
    Expr::cnst(nm1("s"))
}
fn ml_e() -> Expr {
    Expr::cnst(nm1("ml"))
}
fn mn_e() -> Expr {
    Expr::cnst(nm1("mn"))
}
fn a_e() -> Expr {
    Expr::cnst(nm1("a"))
}
fn b_e() -> Expr {
    Expr::cnst(nm1("b"))
}
fn extra_e() -> Expr {
    Expr::cnst(nm1("extra"))
}

fn lvl_u_vec() -> Vec<Level> {
    let mut v: Vec<Level> = Vec::new();
    v.push(Level::param(nm_u()));
    v
}

fn nat_rec_head() -> Expr {
    Expr::const_(nm_nat_rec(), lvl_u_vec())
}
fn nat_num(k: u64) -> Expr {
    let mut e = Expr::const_(nm_nat_zero(), Vec::new());
    let mut i = 0u64;
    while i < k {
        e = Expr::app(Expr::const_(nm_nat_succ(), Vec::new()), e);
        i += 1;
    }
    e
}
fn nat_rec_app(major: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::app(Expr::app(nat_rec_head(), c_e()), z_e()), s_e()),
        major,
    )
}
fn tree_leaf(x: Expr) -> Expr {
    Expr::app(Expr::const_(nm_tree_leaf(), Vec::new()), x)
}
fn tree_node(l: Expr, r: Expr) -> Expr {
    Expr::app(Expr::app(Expr::const_(nm_tree_node(), Vec::new()), l), r)
}
fn tree_rec_head() -> Expr {
    Expr::const_(nm_tree_rec(), lvl_u_vec())
}
fn tree_rec_app(major: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::app(Expr::app(tree_rec_head(), c_e()), ml_e()), mn_e()),
        major,
    )
}

fn run_scenario(scenario: u64, poison: u64) -> Expr {
    if scenario == 4 {
        let env = build_rec_env(1, poison); // Tree
        let v = Verifier { env: &env };
        let term = tree_rec_app(tree_node(tree_leaf(a_e()), tree_leaf(b_e())));
        return v.nf(&term);
    }
    let env = build_rec_env(0, poison); // Nat
    let v = Verifier { env: &env };
    if scenario == 0 {
        let term = nat_rec_app(nat_num(0));
        v.whnf_impl(&term)
    } else if scenario == 1 {
        let term = nat_rec_app(nat_num(1));
        v.whnf_impl(&term)
    } else if scenario == 2 {
        let term = nat_rec_app(nat_num(2));
        v.nf(&term)
    } else if scenario == 3 {
        let term = nat_rec_app(nat_num(3));
        v.nf(&term)
    } else if scenario == 5 {
        let term = nat_rec_app(Expr::from_kind(ExprKind::FVar(FVarId(7))));
        v.whnf_impl(&term)
    } else if scenario == 6 {
        let term = nat_rec_app(Expr::from_kind(ExprKind::Lit(Literal::Nat(2))));
        v.nf(&term)
    } else if scenario == 7 {
        let term = Expr::app(nat_rec_app(nat_num(1)), extra_e());
        v.whnf_impl(&term)
    } else {
        nat_rec_app(nat_num(0))
    }
}

// ════════════════════════════════════════════════════════════════════════════
// MONO ROOTS (#[no_mangle]).
// ════════════════════════════════════════════════════════════════════════════

/// ROOT 1 — run the iota reduction for a scenario and write the result (deep-
/// compared native == JIT + meta). `poison` arms 0 none / 1 minor / 2 IH.
#[unsafe(no_mangle)]
pub extern "C" fn iota_reduce_root(out: *mut Expr, scenario: u64, poison: u64) {
    let e = run_scenario(scenario, poison);
    unsafe {
        std::ptr::write(out, e);
    }
}

/// ROOT 2 — the real family Names (for cached_hash golden pins):
///   0 Nat | 1 Nat.zero | 2 Nat.succ | 3 Nat.rec | 4 Tree | 5 Tree.leaf
///   6 Tree.node | 7 Tree.rec | 8 u
#[unsafe(no_mangle)]
pub extern "C" fn iota_names_probe_root(out: *mut Name, idx: u64) {
    let n = if idx == 0 {
        nm_nat()
    } else if idx == 1 {
        nm_nat_zero()
    } else if idx == 2 {
        nm_nat_succ()
    } else if idx == 3 {
        nm_nat_rec()
    } else if idx == 4 {
        nm_tree()
    } else if idx == 5 {
        nm_tree_leaf()
    } else if idx == 6 {
        nm_tree_node()
    } else if idx == 7 {
        nm_tree_rec()
    } else if idx == 8 {
        nm_u()
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

fn via_reduce(scenario: u64, poison: u64) -> Expr {
    let mut slot = std::mem::MaybeUninit::<Expr>::uninit();
    unsafe {
        iota_reduce_root(slot.as_mut_ptr(), scenario, poison);
        slot.assume_init()
    }
}

fn main() {
    for scenario in 0u64..8 {
        let e = via_reduce(scenario, 0);
        println!("scenario {scenario}: meta={:#018x}", e.meta.raw());
    }

    // Expected correct results.
    // scenario 0: base -> z
    assert!(deep_eq(&via_reduce(0, 0), &z_e()), "base iota -> z");
    // scenario 2: succ^2 -> s (succ zero) (s zero z)
    let exp2 = Expr::app(
        Expr::app(s_e(), nat_num(1)),
        Expr::app(Expr::app(s_e(), nat_num(0)), z_e()),
    );
    assert!(deep_eq(&via_reduce(2, 0), &exp2), "multi-step succ^2");
    // scenario 4: tree -> mn (leaf a) (leaf b) (ml a) (ml b)
    let exp4 = Expr::app(
        Expr::app(
            Expr::app(Expr::app(mn_e(), tree_leaf(a_e())), tree_leaf(b_e())),
            Expr::app(ml_e(), a_e()),
        ),
        Expr::app(ml_e(), b_e()),
    );
    assert!(deep_eq(&via_reduce(4, 0), &exp4), "tree minor+IH order");

    // Poison divergences (the centerpiece).
    assert!(
        !deep_eq(&via_reduce(2, 0), &via_reduce(2, 1)),
        "poison_minor must diverge (Nat succ^2)"
    );
    assert!(
        !deep_eq(&via_reduce(2, 0), &via_reduce(2, 2)),
        "poison_ih must diverge (Nat succ^2)"
    );
    assert!(
        !deep_eq(&via_reduce(4, 0), &via_reduce(4, 1)),
        "poison_minor must diverge (Tree)"
    );
    assert!(
        !deep_eq(&via_reduce(4, 0), &via_reduce(4, 2)),
        "poison_ih must diverge (Tree)"
    );

    // Stuck non-redex (scenario 5) is unchanged.
    let stuck = via_reduce(5, 0);
    let stuck_expected = nat_rec_app(Expr::from_kind(ExprKind::FVar(FVarId(7))));
    assert!(
        deep_eq(&stuck, &stuck_expected),
        "stuck non-redex unchanged"
    );

    for idx in 0u64..9 {
        let mut slot = std::mem::MaybeUninit::<Name>::uninit();
        let n = unsafe {
            iota_names_probe_root(slot.as_mut_ptr(), idx);
            slot.assume_init()
        };
        println!("name {idx}: {:#018x}", n.cached_hash);
    }
    println!("recursor-iota slice smoke OK");
}
