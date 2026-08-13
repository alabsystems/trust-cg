// R4 STAGE 2 — str BYTE ACCESS + str-ITERATOR elements + the `.rec`-interning
// de-modeling (thread R4). Regeneration source for the trust-ir modules embedded
// in ../e2e_str_stage2.rs. Emitted with the r4-str-stage2 trust-ir frontend
// (worktree branch off 6787ae6; frontend/src/mir_lower.rs only — the R4
// `StrInlineOp` + `IterKind::StrBytes` additive inlines).
//
// EMIT (one module per root; see ../slices/README.md for the env):
//   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//   cd <r4-str-stage2 worktree>/frontend && env -u RUSTUP_TOOLCHAIN \
//     RUSTC=$S/bin/rustc \
//     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//     $S/bin/cargo run --bin trust_ir_mir -- \
//     ../../trust-cg/crates/trust-cg-codegen/tests/slices/str_stage2_slice.rs \
//     --crate-type=lib --mir-emit-closure <root> <out.tir>
//   roots: str_stage2_bytes_root | str_stage2_name_root |
//          str_stage2_name_eq_root | str_stage2_rec_scenario_root
//
// WHAT THIS SLICE TRANSCRIBES (clean-kernel truth):
//   * `Name` / `NameInner` — VERBATIM the production (non-kani) declarations
//     (name.rs:150-159, 233-239): the recursive `Arc<Name>` parent chain with
//     `Arc<str>` string components and the construction-time `cached_hash`.
//   * `Name::anon` / `Name::str` / `Name::num` / `compute_hash` — the
//     production construction chain (name.rs:339-364, 483-527): anon = 1723,
//     str-part = `mix_hash(parent.cached_hash, murmur_hash_64a(s.as_bytes(), 11))`,
//     num-part = `mix_hash(parent.cached_hash, n)`. `mix_hash` is VERBATIM
//     (expr/meta.rs:264-273). Here `name_str_part`/`name_num_part` fuse
//     `from_inner` + `compute_hash` into the construction (the hash is computed
//     from the SAME bytes production reads back out of the stored `Arc<str>` —
//     `Arc::from` copies them verbatim, so the value is identical; note
//     [T-hash-src] below).
//   * `murmur_hash_64a` — an INDEX-LOOP transcription of the production
//     implementation (env/native_reducers_string.rs:357-393, MurmurHash2-64A):
//     the production 8-byte blocks come from `slice::as_chunks::<8>()` (a fat
//     tuple-return shape out of lowering scope); here the same block words are
//     assembled little-endian byte-by-byte, and the <8-byte tail is folded by
//     index instead of `.iter().enumerate()`. Bit-identical output — the e2e
//     harness proves it against BOTH a verbatim `as_chunks` oracle AND golden
//     constants pinned from the real clean-kernel binary ([T-murmur-idx]).
//   * `Name::from_string_uncached` (name.rs:557-565) — UNROLLED over literal
//     parts: `s.split('.').fold(anon, step)` with the split done AT
//     TRANSCRIPTION TIME over string literals (format!/split lowering stays out
//     of scope — the R3/R4 boundary), so e.g. "Tree.rec" becomes
//     `step(step(anon, "Tree"), "rec")` ([T-unroll]). The per-part step is the
//     verbatim fold body: parse-as-u64 -> num else str.
//   * `part.parse::<u64>()` — `parse_u64_ascii` transcribes the u64 FromStr
//     decimal path (optional leading '+', digits only, overflow rejects); the
//     e2e verifies it against the REAL `str::parse::<u64>` on every tested part
//     ([T-parse]).
//   * `Name::eq` (name.rs:367-377) — the production PartialEq: cached_hash
//     fast-path, then inner comparison. The derived-recursive `NameInner::eq`
//     is transcribed as an ITERATIVE parent-chain walk (same shape as the
//     production `Ord::cmp` walk, name.rs:410-458), with `str` equality =
//     length + bytewise compare, value-identical to `str::eq` ([T-eq-iter]).
//   * `rec_name_of` — THE DE-MODELED BOUNDARY. The mutual-recursor slice
//     (clean_mutual_recursor_slice.rs) models the production
//     `Name::from_string(&format!("{name}.rec"))` (inductive rec-rule
//     construction) as a lookup in a caller-provided PRE-INTERNED
//     `&[RecPair{ind,rec}]` table. Here `rec_name_of_constructed` CONSTRUCTS
//     the ind and rec names IN-MODULE from literal parts and selects by REAL
//     `Name` equality — no table, no pre-interned inputs. The `format!` render
//     of the head name is resolved at transcription time to its literal parts
//     (the heads are literal-built, so render->reparse is the identity;
//     [T-unroll] again). The production miss-fallback (the fn's own rec_name)
//     is transcribed as a distinct "Dead.rec" name, PROVABLY DEAD on every
//     harness input (both heads are covered) — same note as the
//     mutual-recursor slice's `rec_name_of` fallback.
//
// MODELED BOUNDARIES (beyond the R3 stage-1 address-identity/allocation-count
// boundary, which applies to every literal materialization here):
//   * `Arc<str>` CROSSINGS: `Arc::<str>::from(&str)` (the allocation) and
//     `<Arc<str> as Deref>::deref` (identity-shaped: data ptr + len) lower to
//     extern decls; the e2e binds FAITHFUL host shims that call the REAL alloc
//     `Arc` machinery. Arc<str>-deref-as-extern is the LANDED convention (the
//     round-1 micro-checker fixtures declare the same extern); inlining it in
//     R4 would have drifted their re-emits, so it stays a shim boundary.
//     `Arc::new(Name)` (thin) and `Arc<Name>` deref are INLINED in-module by
//     the landed RUNG 5/6 models — the parent chain never leaves the module.
//   * `u64::wrapping_mul` / `u64::wrapping_add` / `usize::wrapping_mul` extern
//     leaf shims — the established fixture convention (the whnf gold module
//     itself declares `wrapping_mul`; inlining would drift it).
//   * Drops are not emitted (the landed leak model): every Name / Arc built
//     in-module is immortal, like every other verified structure builder.
//
// NEGATIVE-SPACE NOTES: no HashMap/interner (`Name::interned` and the
// NameInterner stay out — this is `from_string_uncached`, the UNCACHED path,
// exactly the fn named by the handoff's stage-2 plan); no format!/split (gap
// (4) and the runtime-split half of gap (3) remain open — literal parts only).

#![allow(dead_code)]

use std::sync::Arc;

// ── clean-kernel name.rs — the production Name (verbatim declarations) ───────

/// name.rs:150-159 (production, non-kani): the recursive inner representation.
pub enum NameInner {
    /// Anonymous name
    Anon,
    /// String component
    Str(Arc<Name>, Arc<str>),
    /// Numeric component (for auto-generated names)
    Num(Arc<Name>, u64),
}

/// name.rs:233-239: hierarchical name with construction-time cached hash.
pub struct Name {
    pub inner: NameInner,
    /// Cached hash value, computed at creation time
    pub cached_hash: u64,
}

// ── clean-kernel expr/meta.rs:264-273 — mix_hash (VERBATIM) ──────────────────

/// MurmurHash2-64A mixing step. Matches Lean 4's `lean_uint64_mix_hash`.
pub fn mix_hash(h: u64, k: u64) -> u64 {
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
// [T-murmur-idx] index-loop transcription: the production `as_chunks::<8>()`
// block iteration becomes an index loop assembling each 8-byte little-endian
// word; the tail fold's `.iter().enumerate()` becomes an index loop. Same
// words, same folds, bit-identical output (harness-proved).

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
// harness-verified against the REAL `str::parse::<u64>` on every tested part.

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

// ── THE DE-MODELED `.rec` INTERNING ──────────────────────────────────────────
// Production (inductive rec-rule construction):
//   `Name::from_string(&format!("{name}.rec"))`
// The mutual-recursor slice modeled this as a pre-interned `&[RecPair]` scan.
// Here: the ind names and their `.rec` names are CONSTRUCTED in-module from
// literal parts (`from_string_uncached` unrolled — [T-unroll]), selected by
// REAL Name equality. No table, no pre-interned inputs. The final fallback
// (production: the fn's own rec_name) is a distinct "Dead.rec", provably dead
// on every harness input.

pub fn rec_name_of_constructed(head: &Name) -> Name {
    // from_string_uncached("Tree") / ("Forest"), unrolled (single parts).
    let tree_ind = fold_step(name_anon(), "Tree");
    let forest_ind = fold_step(name_anon(), "Forest");
    if name_eq(head, &tree_ind) {
        // from_string_uncached("Tree.rec") continues the SAME chain: the ind
        // name is the fold accumulator after part 1.
        fold_step(tree_ind, "rec")
    } else if name_eq(head, &forest_ind) {
        fold_step(forest_ind, "rec")
    } else {
        fold_step(fold_step(name_anon(), "Dead"), "rec")
    }
}

// ── the in-module byte-access consumers (roots) ──────────────────────────────

/// Literal pick shared by the byte roots: murmur shape coverage — 3B (tail
/// only), 8B (exactly one block, no tail), 16B (two blocks, no tail), 20B
/// (two blocks + 4B tail), and "" (empty: no blocks, no tail).
fn pick_lit(idx: u64) -> &'static str {
    if idx == 0 {
        "rec"
    } else if idx == 1 {
        "Tree.rec"
    } else if idx == 2 {
        "VeryLongPartName"
    } else if idx == 3 {
        "VeryLongPartName.rec"
    } else {
        ""
    }
}

/// ROOT M1 — every priority-1/2 byte-access shape, mode-selected:
///   mode 0: `murmur_hash_64a_idx(s.as_bytes(), 11)` — the REAL kernel string
///           hash over a literal, fully in-module (as_bytes inline + index
///           loads + PtrMetadata bounds checks).
///   mode 1: `str::len` inline.
///   mode 2: `for b in s.bytes()` — the str BYTES iterator walk (cursor init +
///           blanket-identity into_iter + StrBytes next, all in-module).
///   mode 3: `for &b in s.as_bytes().iter()` — the u8 slice-iterator walk
///           (`<[u8]>::iter` cursor init + SliceIter next).
///   mode 4: `str_bytes_eq` polarity probe over literal pairs (sel = idx):
///           0: ("Tree","Tree")=1  1: ("Tree","TreX")=0 (same length, last
///           byte differs — the byte loop must catch it)  2: ("Tree","Tre")=0
///           (length lane)  3: ("",""))=1.
#[no_mangle]
pub fn str_stage2_bytes_root(mode: u64, idx: u64) -> u64 {
    if mode == 0 {
        let s = pick_lit(idx);
        murmur_hash_64a_idx(s.as_bytes(), 11)
    } else if mode == 1 {
        let s = pick_lit(idx);
        s.len() as u64
    } else if mode == 2 {
        let s = pick_lit(idx);
        let mut h = 0u64;
        for b in s.bytes() {
            h = h.wrapping_mul(31).wrapping_add(b as u64);
        }
        h
    } else if mode == 3 {
        let s = pick_lit(idx);
        let mut h = 0u64;
        for &b in s.as_bytes().iter() {
            h = h.wrapping_mul(31).wrapping_add(b as u64);
        }
        h
    } else {
        let r = if idx == 0 {
            str_bytes_eq("Tree", "Tree")
        } else if idx == 1 {
            str_bytes_eq("Tree", "TreX")
        } else if idx == 2 {
            str_bytes_eq("Tree", "Tre")
        } else {
            str_bytes_eq("", "")
        };
        if r {
            1
        } else {
            0
        }
    }
}

/// ROOT M2 — `from_string_uncached` UNROLLED over literal parts ([T-unroll]),
/// returning the constructed Name (sret; the harness walks the structure and
/// checks the hash BIT-IDENTICAL against the real clean-kernel golden values):
///   sel 0: "Tree.rec"             = step(step(anon,"Tree"),"rec")
///   sel 1: "Forest.rec"           = step(step(anon,"Forest"),"rec")
///   sel 2: "Nat.42.rec"           = step(step(step(anon,"Nat"),"42"),"rec")
///          (the "42" part takes the parse->num branch: NameInner::Num)
///   sel 3: "VeryLongPartName.rec" (16B part: murmur BLOCK path in-chain)
///   sel 4+: "0.rec"               = step(step(anon,"0"),"rec") (num edge: 0)
#[no_mangle]
pub fn str_stage2_name_root(sel: u64) -> Name {
    if sel == 0 {
        fold_step(fold_step(name_anon(), "Tree"), "rec")
    } else if sel == 1 {
        fold_step(fold_step(name_anon(), "Forest"), "rec")
    } else if sel == 2 {
        fold_step(fold_step(fold_step(name_anon(), "Nat"), "42"), "rec")
    } else if sel == 3 {
        fold_step(fold_step(name_anon(), "VeryLongPartName"), "rec")
    } else {
        fold_step(fold_step(name_anon(), "0"), "rec")
    }
}

/// ROOT M3b — production `Name::eq` over in-module-constructed names:
///   sel 0: Tree.rec == Tree.rec      -> 1 (hashes equal; FULL WALK runs:
///          str bytes x2 + Anon==Anon)
///   sel 1: Tree.rec == Forest.rec    -> 0 (hash fast-path)
///   sel 2: Nat.42   == Nat.42        -> 1 (num arm walk)
///   sel 3: Nat.42   == Nat.43        -> 0 (hash fast-path via num)
#[no_mangle]
pub fn str_stage2_name_eq_root(sel: u64) -> u64 {
    let r = if sel == 0 {
        let a = fold_step(fold_step(name_anon(), "Tree"), "rec");
        let b = fold_step(fold_step(name_anon(), "Tree"), "rec");
        name_eq(&a, &b)
    } else if sel == 1 {
        let a = fold_step(fold_step(name_anon(), "Tree"), "rec");
        let b = fold_step(fold_step(name_anon(), "Forest"), "rec");
        name_eq(&a, &b)
    } else if sel == 2 {
        let a = fold_step(fold_step(name_anon(), "Nat"), "42");
        let b = fold_step(fold_step(name_anon(), "Nat"), "42");
        name_eq(&a, &b)
    } else {
        let a = fold_step(fold_step(name_anon(), "Nat"), "42");
        let b = fold_step(fold_step(name_anon(), "Nat"), "43");
        name_eq(&a, &b)
    };
    if r {
        1
    } else {
        0
    }
}

/// ROOT M3a — the mutual-recursor SCENARIO with the interning DE-MODELED: the
/// head ind name is constructed in-module (Tree for 0, Forest otherwise — the
/// two types of the verified even/odd Tree/Forest family), and the cross-type
/// IH rec name comes from `rec_name_of_constructed` — real equality over
/// constructed names, NOT a passed-in pre-interned RecPair table.
#[no_mangle]
pub fn str_stage2_rec_scenario_root(head_is_forest: u64) -> Name {
    let head = if head_is_forest == 0 {
        fold_step(name_anon(), "Tree")
    } else {
        fold_step(name_anon(), "Forest")
    };
    rec_name_of_constructed(&head)
}
