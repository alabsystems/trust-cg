// Other hosts compile no native test; a Darwin host must meet every prerequisite.
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// The integer-lane `BTreeMap` / `HashMap` model admits a key, value and hasher
// only when every trait method std would call on them is the builtin behavior
// the model implements; any other map with integer lanes refuses by name.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The model stores keys and values as raw i64 lanes, finds a key by comparing
// lanes, frees only the entry buffer, and runs no user code. Its admission used
// to be the LAYOUT of `K` and `V` alone, and `rust_ty_to_trust_ir_ty` sees
// through a single-field struct and maps a tag-only enum to its tag, so a key
// with a hand-written `Ord` / `PartialEq` / `Hash`, a value with a hand-written
// `Default`, a `Drop` key or value, and a user `BuildHasher` were all modeled
// and silently miscompiled: keys equal under the user's impl stayed distinct,
// the impl's calls, side effects and panics vanished, `or_default` stored 0,
// and no key, value or hasher was ever dropped. A lookup `&Q` with `Q != K`
// skipped `K: Borrow<Q>` the same way.
//
// The trait check behind the admission (`trait_claim_holds`) trusts an impl as
// builtin only when rustc's builtin derive macro expanded it, local or
// upstream: the `#[automatically_derived]` attribute alone is ungated, and a
// dependency's hand-written impl under it was modeled. A derived `Default` is
// the zero lane only when no field has a default value
// (`#![feature(default_field_values)]`).
//
// REFUSAL ROWS: every one compiled and diverged from LLVM at -O0..-O3 before
// the admission covered it (the "Baseline" line beside each guest says at
// which revision; measured on Darwin AArch64 with a standalone driver passing
// these compile flags); each must now refuse with `[TCG-MAP-MODEL-TRAIT]` at
// -O0..-O3, never compile.
//
// CONTROL ROWS: primitive integer and `char` keys and values, keys with
// builtin-derived `Ord` / `PartialEq` + `Hash` (newtypes, a nested newtype, a
// tag-only enum, a struct with a unit or `PhantomData` field, core's derived
// `Wrapping` / `Ordering` and `Reverse`'s derived `PartialEq` + `Hash`, a
// dependency's derives), `or_default` on a primitive or a builtin-derived
// `Default` (local or upstream), and an explicit `RandomState`: each must
// compile and match LLVM at -O0..-O3. A control's baseline line says where it
// did not (the `PhantomData` key was refused at e71a322f1; `.cloned()` over a
// dependency's hand-written `clone` of a `Copy` type, which the same trait
// check decides, diverged).
//
// A guest with a `dep` source links an upstream crate `dep`, built by the same
// lane (LLVM or the bridge) with the same flags.
//
// PROOF GATE: compiled with `no-proof-certs`; an execution differential, not a
// certification claim.

use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const TARGET: &str = "aarch64-apple-darwin";
const OPTS: [u32; 4] = [0, 1, 2, 3];
const REFUSAL: &str = "[TCG-MAP-MODEL-TRAIT]";
const RUN_LIMIT: Duration = Duration::from_secs(20);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Expect {
    /// The bridge must refuse with `REFUSAL` at every level.
    Refuse,
    /// The bridge must compile, and the program must end exactly as LLVM's.
    Match,
}

/// One guest program. `unwind` builds both sides with `-Cpanic=unwind` (the
/// guest's observable is a panic out of a user trait method, or the row pins
/// the same verdict under unwinding); every other guest is built with
/// `-Cpanic=abort`. `dep` is the source of an upstream crate named `dep`.
struct Guest {
    name: &'static str,
    unwind: bool,
    dep: Option<&'static str>,
    expect: Expect,
    src: &'static str,
}

/// The guests. Each one's baseline line is the measurement before the
/// admission covered it, LLVM against the bridge, -O0..-O3: at origin/main
/// 33eefbf58 unless the line names another revision.
const GUESTS: &[Guest] = &[
    // A `Drop` value: the displaced value and the map's live values.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 10, bridge exit 2.
    Guest {
        name: "d01_hm_value_drop",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, Ordering::Relaxed};
static DROPS: AtomicU32 = AtomicU32::new(0);
struct D(u32);
impl Drop for D { fn drop(&mut self) { DROPS.fetch_add(self.0, Relaxed); } }
fn main() {
    {
        let mut m: HashMap<u32, D> = HashMap::new();
        m.insert(1, D(std::hint::black_box(2)));
        m.insert(1, D(3));
        m.insert(2, D(5));
    }
    std::process::exit(DROPS.load(Relaxed) as i32);
}
"#,
    },
    // A `Drop` key with derived `Ord`: the duplicate key, the removed key, the live key.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 48, bridge exit 45.
    Guest {
        name: "d02_btm_key_drop",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU32, Ordering::Relaxed};
static DROPS: AtomicU32 = AtomicU32::new(0);
#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct D(u32);
impl Drop for D { fn drop(&mut self) { DROPS.fetch_add(1, Relaxed); } }
fn main() {
    {
        let mut m: BTreeMap<D, u32> = BTreeMap::new();
        m.insert(D(std::hint::black_box(2)), 1);
        m.insert(D(2), 2);
        m.insert(D(5), 3);
        let r = m.remove(&D(5)).unwrap_or(0);
        DROPS.fetch_add(r * 100, Relaxed);
    }
    std::process::exit(DROPS.load(Relaxed) as i32 % 256);
}
"#,
    },
    // An unused `or_insert` default and live values that are `Drop`.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 33, bridge exit 0.
    Guest {
        name: "d03_map_or_insert_unused_default_drop",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicU32, Ordering::Relaxed};
static DROPS: AtomicU32 = AtomicU32::new(0);
struct D(u32);
impl Drop for D { fn drop(&mut self) { DROPS.fetch_add(self.0, Relaxed); } }
fn main() {
    {
        let mut m: BTreeMap<u32, D> = BTreeMap::new();
        m.entry(std::hint::black_box(1)).or_insert(D(1));
        m.entry(1).or_insert(D(2));
        let mut h: HashMap<u32, D> = HashMap::new();
        h.entry(std::hint::black_box(1)).or_insert(D(10));
        h.entry(1).or_insert(D(20));
    }
    std::process::exit(DROPS.load(Relaxed) as i32);
}
"#,
    },
    // A `Drop` key with derived `Eq` + `Hash`.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 3, bridge exit 0.
    Guest {
        name: "d04_hm_key_drop_derived",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, Ordering::Relaxed};
static DROPS: AtomicU32 = AtomicU32::new(0);
#[derive(PartialEq, Eq, Hash)]
struct D(u32);
impl Drop for D { fn drop(&mut self) { DROPS.fetch_add(1, Relaxed); } }
fn main() {
    {
        let mut m: HashMap<D, u32> = HashMap::new();
        m.insert(D(std::hint::black_box(2)), 1);
        m.insert(D(2), 2);
        m.insert(D(5), 3);
    }
    std::process::exit(DROPS.load(Relaxed) as i32);
}
"#,
    },
    // A hand-written `Ord` (x % 10) on a newtype key: K(1) and K(11) are one key.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 120, bridge exit 218.
    Guest {
        name: "k01_btm_user_ord_newtype",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::cmp::Ordering;
use std::collections::BTreeMap;
#[derive(Clone, Copy)]
struct K(u32);
impl PartialEq for K { fn eq(&self, o: &K) -> bool { self.cmp(o) == Ordering::Equal } }
impl Eq for K {}
impl PartialOrd for K { fn partial_cmp(&self, o: &K) -> Option<Ordering> { Some(self.cmp(o)) } }
impl Ord for K { fn cmp(&self, o: &K) -> Ordering { (self.0 % 10).cmp(&(o.0 % 10)) } }
fn main() {
    let mut m: BTreeMap<K, u32> = BTreeMap::new();
    m.insert(K(std::hint::black_box(1)), 10);
    let old = m.insert(K(std::hint::black_box(11)), 20).unwrap_or(9);
    let g = m.get(&K(21)).copied().unwrap_or(9);
    let c = m.contains_key(&K(31)) as u32;
    std::process::exit((m.len() as u32 * 100 + c * 10 + g % 10 + old) as i32);
}
"#,
    },
    // A derived `Eq` but hand-written, call-counting `Ord`.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 81, bridge exit 1.
    Guest {
        name: "k02_btm_user_cmp_counted",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU32, Ordering::Relaxed};
static CMPS: AtomicU32 = AtomicU32::new(0);
#[derive(Clone, Copy, PartialEq, Eq)]
struct K(u64);
impl PartialOrd for K { fn partial_cmp(&self, o: &K) -> Option<Ordering> { Some(self.cmp(o)) } }
impl Ord for K { fn cmp(&self, o: &K) -> Ordering { CMPS.fetch_add(1, Relaxed); self.0.cmp(&o.0) } }
fn main() {
    let mut m: BTreeMap<K, u64> = BTreeMap::new();
    for i in 0..5u64 { m.insert(K(std::hint::black_box(4 - i)), i); }
    let g = m.get(&K(3)).copied().unwrap_or(99);
    std::process::exit((CMPS.load(Relaxed) * 10 + g as u32) as i32 % 256);
}
"#,
    },
    // `entry` / `remove` / `get` under a hand-written `Ord` (|x|).
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 132, bridge exit 55.
    Guest {
        name: "k03_btm_entry_remove_user_ord",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::cmp::Ordering;
use std::collections::BTreeMap;
#[derive(Clone, Copy)]
struct K(i32);
impl PartialEq for K { fn eq(&self, o: &K) -> bool { self.0.abs() == o.0.abs() } }
impl Eq for K {}
impl PartialOrd for K { fn partial_cmp(&self, o: &K) -> Option<Ordering> { Some(self.cmp(o)) } }
impl Ord for K { fn cmp(&self, o: &K) -> Ordering { self.0.abs().cmp(&o.0.abs()) } }
fn main() {
    let mut m: BTreeMap<K, u32> = BTreeMap::new();
    for x in [3i32, -3, 4, std::hint::black_box(-4), 3] { *m.entry(K(x)).or_insert(0) += 1; }
    let r = m.remove(&K(-3)).unwrap_or(0);
    let g = m.get(&K(4)).copied().unwrap_or(0);
    std::process::exit((m.len() as u32 * 100 + r * 10 + g) as i32);
}
"#,
    },
    // A tag-only enum key whose hand-written `Ord` puts A and B together.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 22, bridge exit 31.
    Guest {
        name: "k04_btm_tag_enum_user_ord",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::cmp::Ordering;
use std::collections::BTreeMap;
#[derive(Clone, Copy)]
enum E { A, B, C }
fn rank(e: &E) -> u8 { match e { E::C => 1, _ => 0 } }
impl PartialEq for E { fn eq(&self, o: &E) -> bool { rank(self) == rank(o) } }
impl Eq for E {}
impl PartialOrd for E { fn partial_cmp(&self, o: &E) -> Option<Ordering> { Some(self.cmp(o)) } }
impl Ord for E { fn cmp(&self, o: &E) -> Ordering { rank(self).cmp(&rank(o)) } }
fn main() {
    let mut m: BTreeMap<E, u32> = BTreeMap::new();
    let k = if std::hint::black_box(true) { E::B } else { E::C };
    m.insert(E::A, 1);
    m.insert(k, 2);
    m.insert(E::C, 3);
    std::process::exit((m.len() as u32 * 10 + m.get(&E::A).copied().unwrap_or(0)) as i32);
}
"#,
    },
    // A hand-written `Ord` that exits the process on one key.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 42, bridge exit 2.
    Guest {
        name: "k05_btm_panicking_ord",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::cmp::Ordering;
use std::collections::BTreeMap;
#[derive(Clone, Copy, PartialEq, Eq)]
struct K(u32);
impl PartialOrd for K { fn partial_cmp(&self, o: &K) -> Option<Ordering> { Some(self.cmp(o)) } }
impl Ord for K {
    fn cmp(&self, o: &K) -> Ordering {
        if self.0 == 13 || o.0 == 13 { std::process::exit(42) }
        self.0.cmp(&o.0)
    }
}
fn main() {
    let mut m: BTreeMap<K, u32> = BTreeMap::new();
    m.insert(K(1), 1);
    m.insert(K(std::hint::black_box(13)), 2);
    std::process::exit(m.len() as i32);
}
"#,
    },
    // A hand-written `PartialEq` + `Hash` (x % 10) on a newtype key.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 120, bridge exit 218.
    Guest {
        name: "k06_hm_user_eq_hash_newtype",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::collections::HashMap;
use std::hash::{Hash, Hasher};
#[derive(Clone, Copy)]
struct K(u32);
impl PartialEq for K { fn eq(&self, o: &K) -> bool { self.0 % 10 == o.0 % 10 } }
impl Eq for K {}
impl Hash for K { fn hash<H: Hasher>(&self, h: &mut H) { (self.0 % 10).hash(h) } }
fn main() {
    let mut m: HashMap<K, u32> = HashMap::new();
    m.insert(K(std::hint::black_box(1)), 10);
    let old = m.insert(K(std::hint::black_box(11)), 20).unwrap_or(9);
    let g = m.get(&K(21)).copied().unwrap_or(9);
    let c = m.contains_key(&K(31)) as u32;
    std::process::exit((m.len() as u32 * 100 + c * 10 + g % 10 + old) as i32);
}
"#,
    },
    // A derived `Eq` but hand-written, call-counting `Hash`.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 66, bridge exit 6.
    Guest {
        name: "k07_hm_user_hash_counted",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU32, Ordering::Relaxed};
static HASHES: AtomicU32 = AtomicU32::new(0);
#[derive(Clone, Copy, PartialEq, Eq)]
struct K(u64);
impl Hash for K { fn hash<H: Hasher>(&self, h: &mut H) { HASHES.fetch_add(1, Relaxed); self.0.hash(h) } }
fn main() {
    let mut m: HashMap<K, u64> = HashMap::with_capacity(16);
    for i in 0..5u64 { m.insert(K(std::hint::black_box(i)), i * 2); }
    let g = m.get(&K(3)).copied().unwrap_or(0);
    std::process::exit((HASHES.load(Relaxed) * 10 + g as u32) as i32 % 256);
}
"#,
    },
    // A tag-only enum key whose hand-written `PartialEq` + `Hash` merge A and B.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 22, bridge exit 31.
    Guest {
        name: "k08_hm_tag_enum_user_eq",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::collections::HashMap;
use std::hash::{Hash, Hasher};
#[derive(Clone, Copy)]
enum E { A, B, C }
fn rank(e: &E) -> u8 { match e { E::C => 1, _ => 0 } }
impl PartialEq for E { fn eq(&self, o: &E) -> bool { rank(self) == rank(o) } }
impl Eq for E {}
impl Hash for E { fn hash<H: Hasher>(&self, h: &mut H) { rank(self).hash(h) } }
fn main() {
    let mut m: HashMap<E, u32> = HashMap::new();
    let k = if std::hint::black_box(true) { E::B } else { E::C };
    m.insert(E::A, 1);
    m.insert(k, 2);
    m.insert(E::C, 3);
    std::process::exit((m.len() as u32 * 10 + m.get(&E::A).copied().unwrap_or(0)) as i32);
}
"#,
    },
    // `get_mut` / `remove` / `is_empty` under a case-insensitive key `PartialEq`.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 111, bridge exit 0.
    Guest {
        name: "k09_hm_get_mut_remove_user_eq",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::collections::HashMap;
use std::hash::{Hash, Hasher};
#[derive(Clone, Copy)]
struct K(u8);
impl PartialEq for K { fn eq(&self, o: &K) -> bool { self.0.to_ascii_lowercase() == o.0.to_ascii_lowercase() } }
impl Eq for K {}
impl Hash for K { fn hash<H: Hasher>(&self, h: &mut H) { self.0.to_ascii_lowercase().hash(h) } }
fn main() {
    let mut m: HashMap<K, u32> = HashMap::new();
    m.insert(K(std::hint::black_box(b'A')), 1);
    if let Some(v) = m.get_mut(&K(b'a')) { *v += 10; }
    let r = m.remove(&K(b'a')).unwrap_or(0);
    std::process::exit((r * 10 + m.is_empty() as u32) as i32);
}
"#,
    },
    // A single-variant enum key with a hand-written `PartialEq` + `Hash`.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 12, bridge exit 20.
    Guest {
        name: "k10_hm_single_variant_enum_key",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::collections::HashMap;
use std::hash::{Hash, Hasher};
#[derive(Clone, Copy)]
enum K { Id(u32) }
impl PartialEq for K { fn eq(&self, o: &K) -> bool { let (K::Id(a), K::Id(b)) = (self, o); a / 100 == b / 100 } }
impl Eq for K {}
impl Hash for K { fn hash<H: Hasher>(&self, h: &mut H) { let K::Id(a) = self; (a / 100).hash(h) } }
fn main() {
    let mut m: HashMap<K, u32> = HashMap::new();
    m.insert(K::Id(std::hint::black_box(101)), 1);
    m.insert(K::Id(std::hint::black_box(150)), 2);
    let g = m.get(&K::Id(199)).copied().unwrap_or(0);
    std::process::exit((m.len() as u32 * 10 + g) as i32);
}
"#,
    },
    // A key `Hash` that panics under panic=unwind (a drop guard observes the unwind).
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 30, bridge exit 2.
    Guest {
        name: "k11b_hm_panicking_hash_unwind_guard",
        unwind: true,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::collections::HashMap;
use std::hash::{Hash, Hasher};
struct Guard(u32);
impl Drop for Guard { fn drop(&mut self) { std::process::exit(self.0 as i32) } }
#[derive(Clone, Copy, PartialEq, Eq)]
struct K(u32);
impl Hash for K {
    fn hash<H: Hasher>(&self, h: &mut H) {
        if self.0 == 13 { panic!("unlucky hash") }
        self.0.hash(h)
    }
}
fn main() {
    let _guard = Guard(std::hint::black_box(30));
    let mut m: HashMap<K, u32> = HashMap::new();
    m.insert(K(1), 1);
    m.insert(K(std::hint::black_box(13)), 2);
    std::mem::forget(_guard);
    std::process::exit(m.len() as i32);
}
"#,
    },
    // A `&u32` lookup in a map keyed by K: std calls the user's call-counting `Borrow<u32>`.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 61, bridge exit 17.
    Guest {
        name: "k12_btm_borrow_lookup_counted",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::borrow::Borrow;
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU32, Ordering::Relaxed};
static BORROWS: AtomicU32 = AtomicU32::new(0);
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct K(u32);
impl Borrow<u32> for K { fn borrow(&self) -> &u32 { BORROWS.fetch_add(1, Relaxed); &self.0 } }
fn main() {
    let mut m: BTreeMap<K, u32> = BTreeMap::new();
    m.insert(K(std::hint::black_box(4)), 40);
    m.insert(K(7), 70);
    let g = m.get(&7u32).copied().unwrap_or(0);
    let c = m.contains_key(&4u32) as u32;
    std::process::exit((BORROWS.load(Relaxed) * 100 + g / 10 + c * 10) as i32 % 256);
}
"#,
    },
    // A user `BuildHasher` whose `Hasher` counts `write` / `finish`.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 55, bridge exit 0.
    Guest {
        name: "s01_hm_user_buildhasher",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::collections::HashMap;
use std::hash::{BuildHasher, Hasher};
use std::sync::atomic::{AtomicU32, Ordering::Relaxed};
static WRITES: AtomicU32 = AtomicU32::new(0);
static FINISH: AtomicU32 = AtomicU32::new(0);
struct H(u64);
impl Hasher for H {
    fn write(&mut self, b: &[u8]) {
        WRITES.fetch_add(1, Relaxed);
        for x in b { self.0 = self.0.wrapping_mul(31).wrapping_add(*x as u64); }
    }
    fn finish(&self) -> u64 { FINISH.fetch_add(1, Relaxed); self.0 }
}
struct B;
impl BuildHasher for B { type Hasher = H; fn build_hasher(&self) -> H { H(7) } }
fn main() {
    let mut m: HashMap<u32, u32, B> = HashMap::with_capacity_and_hasher(64, B);
    for i in 0..4u32 { m.insert(std::hint::black_box(i), i + 100); }
    let g = m.get(&2).copied().unwrap_or(0);
    std::process::exit(((WRITES.load(Relaxed) * 10 + FINISH.load(Relaxed)) + g - 102) as i32 % 256);
}
"#,
    },
    // A `with_hasher` hasher with a `Drop`.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 5, bridge exit 0.
    Guest {
        name: "s02_hm_hasher_drop",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::collections::HashMap;
use std::hash::{BuildHasher, DefaultHasher};
use std::sync::atomic::{AtomicU32, Ordering::Relaxed};
static DROPS: AtomicU32 = AtomicU32::new(0);
struct B(u32);
impl BuildHasher for B { type Hasher = DefaultHasher; fn build_hasher(&self) -> DefaultHasher { DefaultHasher::new() } }
impl Drop for B { fn drop(&mut self) { DROPS.fetch_add(self.0, Relaxed); } }
fn main() {
    {
        let mut m: HashMap<u32, u32, B> = HashMap::with_hasher(B(std::hint::black_box(5)));
        m.insert(1, 2);
    }
    std::process::exit(DROPS.load(Relaxed) as i32);
}
"#,
    },
    // `BuildHasherDefault` over a user call-counting `Hasher`.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 116, bridge exit 16.
    Guest {
        name: "s03_hm_buildhasherdefault_user_hasher",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::sync::atomic::{AtomicU32, Ordering::Relaxed};
static CALLS: AtomicU32 = AtomicU32::new(0);
#[derive(Default)]
struct H(u64);
impl Hasher for H {
    fn write(&mut self, b: &[u8]) {
        CALLS.fetch_add(1, Relaxed);
        for x in b { self.0 = self.0.wrapping_mul(131).wrapping_add(*x as u64); }
    }
    fn finish(&self) -> u64 { self.0 }
}
fn main() {
    let mut m: HashMap<u64, u64, BuildHasherDefault<H>> = HashMap::with_hasher(BuildHasherDefault::default());
    for i in 0..std::hint::black_box(6u64) { m.insert(i, i * i); }
    let g = m.get(&4).copied().unwrap_or(0);
    std::process::exit((CALLS.load(Relaxed) * 10 + g as u32) as i32 % 256);
}
"#,
    },
    // `or_default` with a hand-written `Default` (V(7)).
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 8, bridge exit 1.
    Guest {
        name: "v01_hm_or_default_user_default",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::collections::HashMap;
#[derive(Clone, Copy)]
struct V(u32);
impl Default for V { fn default() -> V { V(7) } }
fn main() {
    let mut m: HashMap<u32, V> = HashMap::new();
    m.entry(std::hint::black_box(1)).or_default().0 += 1;
    std::process::exit(m.get(&1).map(|x| x.0).unwrap_or(99) as i32);
}
"#,
    },
    // `or_default` with a hand-written `Default` (V(-5)) on a BTreeMap.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 46, bridge exit 51.
    Guest {
        name: "v02_btm_or_default_user_default",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::collections::BTreeMap;
#[derive(Clone, Copy)]
struct V(i32);
impl Default for V { fn default() -> V { V(-5) } }
fn main() {
    let mut m: BTreeMap<u32, V> = BTreeMap::new();
    m.entry(std::hint::black_box(1)).or_default().0 += 1;
    std::process::exit((m.get(&1).map(|x| x.0).unwrap_or(99) + 50) as i32);
}
"#,
    },
    // `or_default` of a derived enum `Default` whose discriminant is 2 (no variant is 0).
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 11, bridge killed by SIGTRAP.
    Guest {
        name: "v03_btm_or_default_enum_nonzero_default",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::collections::BTreeMap;
#[derive(Clone, Copy, Default)]
#[repr(u8)]
enum E { A = 1, #[default] B = 2 }
fn main() {
    let mut m: BTreeMap<u32, E> = BTreeMap::new();
    let e = *m.entry(std::hint::black_box(1)).or_default();
    std::process::exit(match e { E::A => 10, E::B => 11 });
}
"#,
    },
    // `or_default` of a derived tag-only enum `Default` selecting the third variant.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 12, bridge exit 10.
    Guest {
        name: "v04_hm_or_default_derived_enum_default",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::collections::HashMap;
#[derive(Clone, Copy, Default)]
enum E { A, B, #[default] C }
fn main() {
    let mut m: HashMap<u32, E> = HashMap::new();
    let e = *m.entry(std::hint::black_box(1)).or_default();
    std::process::exit(match e { E::A => 10, E::B => 11, E::C => 12 });
}
"#,
    },
    // `or_default` with a call-counting `Default` that returns zero.
    // Baseline: compiled at O0-O3 and diverged: LLVM exit 12, bridge exit 2.
    Guest {
        name: "v05_hm_or_default_counted",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, Ordering::Relaxed};
static CALLS: AtomicU32 = AtomicU32::new(0);
#[derive(Clone, Copy)]
struct V(u32);
impl Default for V { fn default() -> V { CALLS.fetch_add(1, Relaxed); V(0) } }
fn main() {
    let mut m: HashMap<u32, V> = HashMap::new();
    m.entry(std::hint::black_box(1)).or_default().0 += 1;
    m.entry(1).or_default().0 += 1;
    std::process::exit((CALLS.load(Relaxed) * 10 + m.get(&1).map(|x| x.0).unwrap_or(0)) as i32);
}
"#,
    },
    // Unsigned keys and values (u8..u64, usize, i64) on BTreeMap.
    // Baseline: compiled and matched at O0-O3 (exit 223).
    Guest {
        name: "c01_btm_unsigned_keys",
        unwind: false,
        dep: None,
        expect: Expect::Match,
        src: r#"use std::collections::BTreeMap;
use std::hint::black_box;
macro_rules! exercise {
    ($k:ty, $v:ty, $a:expr, $b:expr) => {{
        let mut m: BTreeMap<$k, $v> = BTreeMap::new();
        m.insert(black_box($a), 3);
        let old = m.insert($a, 4).unwrap_or(0) as u64;
        m.insert($b, 5);
        *m.entry($b).or_insert(9) += 1;
        let g = m.get(&$a).copied().unwrap_or(0) as u64;
        let c = m.contains_key(&$b) as u64;
        let r = m.remove(&$a).unwrap_or(0) as u64;
        old * 1000 + g * 100 + c * 10 + r + m.len() as u64 * 7
    }};
}
fn main() {
    let mut acc = 0u64;
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(u8, u16, 200u8, 7u8));
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(u16, u32, 60000u16, 1u16));
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(u32, u8, 4_000_000_000u32, 0u32));
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(u64, u64, u64::MAX, 1u64 << 63));
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(usize, i64, usize::MAX - 1, 5usize));
    std::process::exit((acc % 251) as i32);
}
"#,
    },
    // Signed keys and values (i8..i64, isize), extreme values, on BTreeMap.
    // Baseline: compiled and matched at O0-O3 (exit 113).
    Guest {
        name: "c02_btm_signed_keys",
        unwind: false,
        dep: None,
        expect: Expect::Match,
        src: r#"use std::collections::BTreeMap;
use std::hint::black_box;
macro_rules! exercise {
    ($k:ty, $v:ty, $a:expr, $b:expr) => {{
        let mut m: BTreeMap<$k, $v> = BTreeMap::new();
        m.insert(black_box($a), -3);
        let old = m.insert($a, 4).unwrap_or(0) as i64;
        m.insert($b, -5);
        *m.entry($b).or_insert(9) += 1;
        let g = m.get(&$a).copied().unwrap_or(0) as i64;
        let c = m.contains_key(&$b) as i64;
        let r = m.remove(&$a).unwrap_or(0) as i64;
        (old * 1000 + g * 100 + c * 10 + r + m.len() as i64 * 7) as u64
    }};
}
fn main() {
    let mut acc = 0u64;
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(i8, i16, -128i8, 127i8));
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(i16, i8, -1i16, 1i16));
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(i32, i64, i32::MIN, -7i32));
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(i64, i32, -1i64, i64::MAX));
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(isize, i16, isize::MIN, 0isize));
    std::process::exit((acc % 251) as i32);
}
"#,
    },
    // `char` keys and values on BTreeMap.
    // Baseline: compiled and matched at O0-O3 (exit 142).
    Guest {
        name: "c03_btm_char_keys",
        unwind: false,
        dep: None,
        expect: Expect::Match,
        src: r#"use std::collections::BTreeMap;
use std::hint::black_box;
fn main() {
    let mut c: BTreeMap<char, u32> = BTreeMap::new();
    c.insert(black_box('\u{10FFFF}'), 1);
    let old = c.insert('\u{10FFFF}', 2).unwrap_or(0);
    *c.entry('a').or_insert(5) += 1;
    *c.entry('a').or_default() += 1;
    let g = c.get(&'a').copied().unwrap_or(0);
    let k = c.contains_key(&'\u{10FFFF}') as u32;
    let r = c.remove(&'\u{10FFFF}').unwrap_or(0);
    let mut v: BTreeMap<u8, char> = BTreeMap::new();
    v.insert(black_box(3), 'z');
    let gv = v.get(&3).copied().unwrap_or('0') as u32;
    let acc = old * 100000 + g * 10000 + k * 1000 + r * 100 + gv + (c.len() + v.len()) as u32;
    std::process::exit((acc % 251) as i32);
}
"#,
    },
    // Unsigned keys and values on HashMap.
    // Baseline: compiled and matched at O0-O3 (exit 223).
    Guest {
        name: "c04_hm_unsigned_keys",
        unwind: false,
        dep: None,
        expect: Expect::Match,
        src: r#"use std::collections::HashMap;
use std::hint::black_box;
macro_rules! exercise {
    ($k:ty, $v:ty, $a:expr, $b:expr) => {{
        let mut m: HashMap<$k, $v> = HashMap::new();
        m.insert(black_box($a), 3);
        let old = m.insert($a, 4).unwrap_or(0) as u64;
        m.insert($b, 5);
        *m.entry($b).or_insert(9) += 1;
        let g = m.get(&$a).copied().unwrap_or(0) as u64;
        let c = m.contains_key(&$b) as u64;
        let r = m.remove(&$a).unwrap_or(0) as u64;
        old * 1000 + g * 100 + c * 10 + r + m.len() as u64 * 7
    }};
}
fn main() {
    let mut acc = 0u64;
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(u8, u16, 200u8, 7u8));
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(u16, u32, 60000u16, 1u16));
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(u32, u8, 4_000_000_000u32, 0u32));
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(u64, u64, u64::MAX, 1u64 << 63));
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(usize, i64, usize::MAX - 1, 5usize));
    std::process::exit((acc % 251) as i32);
}
"#,
    },
    // Signed keys and values on HashMap.
    // Baseline: compiled and matched at O0-O3 (exit 113).
    Guest {
        name: "c05_hm_signed_keys",
        unwind: false,
        dep: None,
        expect: Expect::Match,
        src: r#"use std::collections::HashMap;
use std::hint::black_box;
macro_rules! exercise {
    ($k:ty, $v:ty, $a:expr, $b:expr) => {{
        let mut m: HashMap<$k, $v> = HashMap::new();
        m.insert(black_box($a), -3);
        let old = m.insert($a, 4).unwrap_or(0) as i64;
        m.insert($b, -5);
        *m.entry($b).or_insert(9) += 1;
        let g = m.get(&$a).copied().unwrap_or(0) as i64;
        let c = m.contains_key(&$b) as i64;
        let r = m.remove(&$a).unwrap_or(0) as i64;
        (old * 1000 + g * 100 + c * 10 + r + m.len() as i64 * 7) as u64
    }};
}
fn main() {
    let mut acc = 0u64;
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(i8, i16, -128i8, 127i8));
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(i16, i8, -1i16, 1i16));
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(i32, i64, i32::MIN, -7i32));
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(i64, i32, -1i64, i64::MAX));
    acc = acc.wrapping_mul(31).wrapping_add(exercise!(isize, i16, isize::MIN, 0isize));
    std::process::exit((acc % 251) as i32);
}
"#,
    },
    // `char` keys and values on HashMap.
    // Baseline: compiled and matched at O0-O3 (exit 142).
    Guest {
        name: "c06_hm_char_keys",
        unwind: false,
        dep: None,
        expect: Expect::Match,
        src: r#"use std::collections::HashMap;
use std::hint::black_box;
fn main() {
    let mut c: HashMap<char, u32> = HashMap::new();
    c.insert(black_box('\u{10FFFF}'), 1);
    let old = c.insert('\u{10FFFF}', 2).unwrap_or(0);
    *c.entry('a').or_insert(5) += 1;
    *c.entry('a').or_default() += 1;
    let g = c.get(&'a').copied().unwrap_or(0);
    let k = c.contains_key(&'\u{10FFFF}') as u32;
    let r = c.remove(&'\u{10FFFF}').unwrap_or(0);
    let mut v: HashMap<u8, char> = HashMap::new();
    v.insert(black_box(3), 'z');
    let gv = v.get(&3).copied().unwrap_or('0') as u32;
    let acc = old * 100000 + g * 10000 + k * 1000 + r * 100 + gv + (c.len() + v.len()) as u32;
    std::process::exit((acc % 251) as i32);
}
"#,
    },
    // Derived `Ord` keys: a newtype, a nested newtype, a tag-only enum, a struct with a unit field.
    // Baseline: compiled and matched at O0-O3 (exit 24).
    Guest {
        name: "c07_btm_derived_keys",
        unwind: false,
        dep: None,
        expect: Expect::Match,
        src: r#"use std::collections::BTreeMap;
use std::hint::black_box;
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct K(u32);
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Outer(K);
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum E { A, B, C }
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Pair((), i16);
fn main() {
    let mut m: BTreeMap<K, u32> = BTreeMap::new();
    m.insert(K(black_box(1)), 10);
    let old = m.insert(K(1), 20).unwrap_or(0);
    m.insert(K(11), 30);
    let g = m.get(&K(11)).copied().unwrap_or(0);
    let mut o: BTreeMap<Outer, u8> = BTreeMap::new();
    *o.entry(Outer(K(black_box(3)))).or_insert(1) += 1;
    *o.entry(Outer(K(3))).or_insert(1) += 1;
    let go = o.get(&Outer(K(3))).copied().unwrap_or(0) as u32;
    let mut e: BTreeMap<E, u16> = BTreeMap::new();
    let k = if black_box(true) { E::B } else { E::C };
    e.insert(E::A, 1);
    e.insert(k, 2);
    e.insert(E::B, 3);
    let ge = e.get(&E::B).copied().unwrap_or(0) as u32;
    let re = e.remove(&E::A).unwrap_or(0) as u32;
    let mut p: BTreeMap<Pair, u8> = BTreeMap::new();
    p.insert(Pair((), black_box(-2)), 6);
    let gp = p.get(&Pair((), -2)).copied().unwrap_or(0) as u32;
    let acc = old * 10000 + g * 100 + go * 50 + ge * 7 + re * 3 + gp
        + (m.len() + o.len() + e.len() + p.len()) as u32;
    std::process::exit((acc % 251) as i32);
}
"#,
    },
    // Derived `PartialEq` + `Eq` + `Hash` keys of the same four shapes.
    // Baseline: compiled and matched at O0-O3 (exit 24).
    Guest {
        name: "c08_hm_derived_keys",
        unwind: false,
        dep: None,
        expect: Expect::Match,
        src: r#"use std::collections::HashMap;
use std::hint::black_box;
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct K(u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Outer(K);
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum E { A, B, C }
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Pair((), i16);
fn main() {
    let mut m: HashMap<K, u32> = HashMap::new();
    m.insert(K(black_box(1)), 10);
    let old = m.insert(K(1), 20).unwrap_or(0);
    m.insert(K(11), 30);
    let g = m.get(&K(11)).copied().unwrap_or(0);
    let mut o: HashMap<Outer, u8> = HashMap::new();
    *o.entry(Outer(K(black_box(3)))).or_insert(1) += 1;
    *o.entry(Outer(K(3))).or_insert(1) += 1;
    let go = o.get(&Outer(K(3))).copied().unwrap_or(0) as u32;
    let mut e: HashMap<E, u16> = HashMap::new();
    let k = if black_box(true) { E::B } else { E::C };
    e.insert(E::A, 1);
    e.insert(k, 2);
    e.insert(E::B, 3);
    let ge = e.get(&E::B).copied().unwrap_or(0) as u32;
    let re = e.remove(&E::A).unwrap_or(0) as u32;
    let mut p: HashMap<Pair, u8> = HashMap::new();
    p.insert(Pair((), black_box(-2)), 6);
    let gp = p.get(&Pair((), -2)).copied().unwrap_or(0) as u32;
    let acc = old * 10000 + g * 100 + go * 50 + ge * 7 + re * 3 + gp
        + (m.len() + o.len() + e.len() + p.len()) as u32;
    std::process::exit((acc % 251) as i32);
}
"#,
    },
    // `or_default` on a primitive, a derived `Default` newtype, a nested one, and `char`.
    // Baseline: compiled and matched at O0-O3 (exit 138).
    Guest {
        name: "c09_map_or_default_zero",
        unwind: false,
        dep: None,
        expect: Expect::Match,
        src: r#"use std::collections::{BTreeMap, HashMap};
use std::hint::black_box;
#[derive(Clone, Copy, Default)]
struct W(u64);
#[derive(Clone, Copy, Default)]
struct Nested(W, ());
fn main() {
    let mut a: HashMap<u32, i16> = HashMap::new();
    *a.entry(black_box(1)).or_default() -= 3;
    *a.entry(1).or_default() -= 3;
    let mut b: BTreeMap<u8, W> = BTreeMap::new();
    b.entry(black_box(2)).or_default().0 += 5;
    let mut c: HashMap<i64, Nested> = HashMap::new();
    c.entry(black_box(-1)).or_default().0 .0 += 7;
    c.entry(-1).or_default().0 .0 += 7;
    let mut d: BTreeMap<u16, char> = BTreeMap::new();
    let z = *d.entry(black_box(9)).or_default() as u32;
    let acc = (a.get(&1).copied().unwrap_or(0) + 100) as u64 * 1000
        + b.get(&2).map(|w| w.0).unwrap_or(0) * 100
        + c.get(&-1).map(|n| n.0 .0).unwrap_or(0)
        + z as u64;
    std::process::exit((acc % 251) as i32);
}
"#,
    },
    // An explicit `RandomState` through `with_hasher` and `with_capacity_and_hasher`.
    // Baseline: compiled and matched at O0-O3 (exit 115).
    Guest {
        name: "c10_hm_explicit_random_state",
        unwind: false,
        dep: None,
        expect: Expect::Match,
        src: r#"use std::collections::HashMap;
use std::hash::RandomState;
use std::hint::black_box;
fn main() {
    let mut m: HashMap<u32, u64, RandomState> = HashMap::with_hasher(RandomState::new());
    m.insert(black_box(3), 30);
    m.insert(4, 40);
    let old = m.insert(3, 31).unwrap_or(0);
    let g = m.get(&4).copied().unwrap_or(0);
    let mut n: HashMap<u8, u8> = HashMap::with_capacity_and_hasher(8, RandomState::new());
    n.insert(black_box(1), 2);
    let gn = n.get(&1).copied().unwrap_or(0) as u64;
    std::process::exit(((old + g * 2 + gn + (m.len() + n.len()) as u64) % 251) as i32);
}
"#,
    },
    // `or_default` on a builtin-derived `Default` whose field has a default
    // value: std stores `W { x: 7 }`, the zero lane stored 0.
    // Baseline (e71a322f1 and 33eefbf58): compiled at O0-O3 and diverged:
    // LLVM exit 8, bridge exit 1.
    Guest {
        name: "v06_hm_or_default_field_default_value",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: V06_SRC,
    },
    // The same program under panic=unwind.
    // Baseline (e71a322f1 and 33eefbf58): compiled at O0-O3 and diverged:
    // LLVM exit 8, bridge exit 1.
    Guest {
        name: "v06u_hm_or_default_field_default_value_unwind",
        unwind: true,
        dep: None,
        expect: Expect::Refuse,
        src: V06_SRC,
    },
    // A `BTreeMap` value with a `u64` default field value, `or_default` twice.
    // Baseline (e71a322f1 and 33eefbf58): compiled at O0-O3 and diverged:
    // LLVM exit 43, bridge exit 3.
    Guest {
        name: "v07_btm_or_default_field_default_value",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"#![feature(default_field_values)]
use std::collections::BTreeMap;
#[derive(Default)]
struct W { n: u64 = 40 }
fn main() {
    let mut m: BTreeMap<u32, W> = BTreeMap::new();
    m.entry(std::hint::black_box(3)).or_default().n += 2;
    m.entry(3).or_default().n += 1;
    let g = m.get(&3).map(|w| w.n).unwrap_or(99);
    std::process::exit(g as i32);
}
"#,
    },
    // The default field value one level down: a derived newtype over a derived
    // struct whose `i32` field defaults to -5.
    // Baseline (e71a322f1 and 33eefbf58): compiled at O0-O3 and diverged:
    // LLVM exit 94, bridge exit 99.
    Guest {
        name: "v08_hm_or_default_nested_field_default_value",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"#![feature(default_field_values)]
use std::collections::HashMap;
#[derive(Default)]
struct Inner { v: i32 = -5 }
#[derive(Default)]
struct W(Inner);
fn main() {
    let mut m: HashMap<u8, W> = HashMap::new();
    let e = m.entry(std::hint::black_box(9)).or_default();
    e.0.v -= 1;
    let g = m.get(&9).map(|w| w.0.v).unwrap_or(99);
    std::process::exit((g + 100) as i32);
}
"#,
    },
    // A `u8` default field value in a `BTreeMap<i16, _>`, including an entry
    // whose default is never modified.
    // Baseline (e71a322f1 and 33eefbf58): compiled at O0-O3 and diverged:
    // LLVM exit 204, bridge exit 2.
    Guest {
        name: "v09_btm_or_default_u8_field_default_value",
        unwind: false,
        dep: None,
        expect: Expect::Refuse,
        src: r#"#![feature(default_field_values)]
use std::collections::BTreeMap;
#[derive(Default)]
struct W { a: u8 = 200 }
fn main() {
    let mut m: BTreeMap<i16, W> = BTreeMap::new();
    m.entry(std::hint::black_box(-3)).or_default().a += 1;
    m.entry(-3).or_default().a += 1;
    m.entry(4).or_default();
    let a = m.get(&-3).map(|w| w.a as u32).unwrap_or(9);
    let b = m.get(&4).map(|w| w.a as u32).unwrap_or(9);
    std::process::exit((a + b / 100) as i32);
}
"#,
    },
    // The default field value is in an upstream crate's derived `Default`.
    // Baseline (e71a322f1 and 33eefbf58): compiled at O0-O3 and diverged:
    // LLVM exit 8, bridge exit 1.
    Guest {
        name: "v10_btm_or_default_upstream_field_default_value",
        unwind: false,
        dep: Some(DEP_FIELD_DEFAULT_VALUE),
        expect: Expect::Refuse,
        src: r#"use std::collections::BTreeMap;
use dep::W;
fn main() {
    let mut m: BTreeMap<u32, W> = BTreeMap::new();
    m.entry(std::hint::black_box(1)).or_default().x += 1;
    std::process::exit(m.get(&1).map(|w| w.x).unwrap_or(99) as i32);
}
"#,
    },
    // An upstream key whose hand-written `Ord` (x % 10) carries
    // `#[automatically_derived]`: K(1), K(11) and K(21) are one key in std.
    // Baseline (e71a322f1 and 33eefbf58): compiled at O0-O3 and diverged:
    // LLVM exit 120, bridge exit 218.
    Guest {
        name: "u01_btm_upstream_attributed_handwritten_ord",
        unwind: false,
        dep: Some(DEP_ATTRIBUTED_HANDWRITTEN),
        expect: Expect::Refuse,
        src: U01_SRC,
    },
    // The same program under panic=unwind.
    // Baseline (e71a322f1 and 33eefbf58): compiled at O0-O3 and diverged:
    // LLVM exit 120, bridge exit 218.
    Guest {
        name: "u01u_btm_upstream_attributed_handwritten_ord_unwind",
        unwind: true,
        dep: Some(DEP_ATTRIBUTED_HANDWRITTEN),
        expect: Expect::Refuse,
        src: U01_SRC,
    },
    // The same key in a `HashMap`: its `PartialEq` / `Hash` are hand-written
    // under `#[automatically_derived]` too.
    // Baseline (e71a322f1 and 33eefbf58): compiled at O0-O3 and diverged:
    // LLVM exit 120, bridge exit 218.
    Guest {
        name: "u02_hm_upstream_attributed_handwritten_eq_hash",
        unwind: false,
        dep: Some(DEP_ATTRIBUTED_HANDWRITTEN),
        expect: Expect::Refuse,
        src: r#"use std::collections::HashMap;
use dep::K;
fn main() {
    let mut m: HashMap<K, u32> = HashMap::new();
    m.insert(K(std::hint::black_box(1)), 10);
    let old = m.insert(K(std::hint::black_box(11)), 20).unwrap_or(9);
    let g = m.get(&K(21)).copied().unwrap_or(9);
    let c = m.contains_key(&K(31)) as u32;
    std::process::exit((m.len() as u32 * 100 + c * 10 + g % 10 + old) as i32);
}
"#,
    },
    // The upstream hand-written `Default` (K(7)) under `#[automatically_derived]`
    // as an `or_default` value.
    // Baseline (e71a322f1 and 33eefbf58): compiled at O0-O3 and diverged:
    // LLVM exit 8, bridge exit 1.
    Guest {
        name: "u03_hm_or_default_upstream_attributed_handwritten_default",
        unwind: false,
        dep: Some(DEP_ATTRIBUTED_HANDWRITTEN),
        expect: Expect::Refuse,
        src: r#"use std::collections::HashMap;
use dep::K;
fn main() {
    let mut m: HashMap<u32, K> = HashMap::new();
    m.entry(std::hint::black_box(1)).or_default().0 += 1;
    let g = m.get(&1).map(|k| k.0).unwrap_or(99);
    std::process::exit(g as i32);
}
"#,
    },
    // A builtin-derived key with a `PhantomData` field, in a `BTreeMap` and a
    // `HashMap`, and a derived `PhantomData`-field value through `or_default`.
    // Baseline: refused at O0-O3 at e71a322f1 ([TCG-MAP-MODEL-TRAIT]; LLVM exit
    // 121). The keys alone (no `V`) matched at 33eefbf58 (exit 112).
    Guest {
        name: "c11_map_phantom_field_derived_key",
        unwind: false,
        dep: None,
        expect: Expect::Match,
        src: r#"use std::collections::{BTreeMap, HashMap};
use std::marker::PhantomData;
use std::hint::black_box as bb;
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
struct K(u32, PhantomData<u8>);
#[derive(Clone, Copy, Default)]
struct V(u16, PhantomData<fn() -> u8>);
fn main() {
    let mut a: BTreeMap<K, u32> = BTreeMap::new();
    a.insert(K(bb(3), PhantomData), 1);
    a.insert(K(3, PhantomData), 2);
    let mut b: HashMap<K, u32> = HashMap::new();
    b.insert(K(bb(3), PhantomData), 5);
    let mut c: HashMap<u8, V> = HashMap::new();
    c.entry(bb(1)).or_default().0 += 9;
    let acc = a.len() as u32 * 10
        + a.get(&K(3, PhantomData)).copied().unwrap_or(0)
        + b.get(&K(3, PhantomData)).copied().unwrap_or(0) * 20
        + c.get(&1).map(|v| v.0 as u32).unwrap_or(0);
    std::process::exit(acc as i32);
}
"#,
    },
    // Upstream keys and values whose impls are rustc's builtin derives.
    // Baseline: compiled and matched at O0-O3 at e71a322f1 (exit 239).
    Guest {
        name: "c12_map_upstream_builtin_derives",
        unwind: false,
        dep: Some(DEP_BUILTIN_DERIVES),
        expect: Expect::Match,
        src: r#"use std::collections::{BTreeMap, HashMap};
use dep::{D, K};
fn main() {
    let mut m: BTreeMap<K, u32> = BTreeMap::new();
    m.insert(K(std::hint::black_box(1)), 10);
    let old = m.insert(K(std::hint::black_box(11)), 20).unwrap_or(9);
    let g = m.get(&K(11)).copied().unwrap_or(9);
    let mut h: HashMap<K, u32> = HashMap::new();
    h.insert(K(std::hint::black_box(3)), 4);
    h.insert(K(3), 5);
    let mut d: HashMap<u32, K> = HashMap::new();
    d.entry(std::hint::black_box(2)).or_default().0 += 6;
    let mut e: BTreeMap<u8, D> = BTreeMap::new();
    e.entry(std::hint::black_box(2)).or_default().0 += 4;
    let acc = m.len() as u32 * 100 + g % 10 + old
        + h.len() as u32 * 7
        + h.get(&K(3)).copied().unwrap_or(0)
        + d.get(&2).map(|k| k.0).unwrap_or(99)
        + e.get(&2).map(|v| v.0 as u32).unwrap_or(99) * 3;
    std::process::exit((acc % 256) as i32);
}
"#,
    },
    // core's derived `Wrapping` and `Ordering` keys and a `Wrapping` `or_default`
    // value, and `Reverse` keys in a `HashMap` (derived `PartialEq` + `Hash`).
    // Baseline: compiled and matched at O0-O3 at e71a322f1 (exit 216).
    Guest {
        name: "c13_map_core_derived_keys",
        unwind: false,
        dep: None,
        expect: Expect::Match,
        src: r#"use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeMap, HashMap};
use std::num::Wrapping;
use std::hint::black_box as bb;
fn main() {
    let mut s: u32 = 0;
    let mut a: BTreeMap<Wrapping<u32>, u32> = BTreeMap::new();
    a.insert(Wrapping(bb(5)), 1);
    a.insert(Wrapping(5), 2);
    a.insert(Wrapping(6), 3);
    s += a.len() as u32 * 10 + a.get(&Wrapping(5)).copied().unwrap_or(0);
    let mut b: HashMap<Wrapping<u16>, Wrapping<u64>> = HashMap::new();
    b.insert(Wrapping(bb(7)), Wrapping(3));
    *b.entry(Wrapping(7)).or_default() += Wrapping(4);
    b.entry(Wrapping(8)).or_default();
    s += b.len() as u32 * 10
        + b.get(&Wrapping(7)).map(|w| w.0 as u32).unwrap_or(0)
        + b.get(&Wrapping(8)).map(|w| w.0 as u32).unwrap_or(50);
    let mut c: BTreeMap<Ordering, u8> = BTreeMap::new();
    c.insert(bb(Ordering::Less), 1);
    c.insert(Ordering::Greater, 2);
    c.insert(Ordering::Less, 3);
    s += c.len() as u32 + c.get(&Ordering::Less).copied().unwrap_or(0) as u32;
    let mut r: HashMap<Reverse<u32>, u32> = HashMap::new();
    r.insert(Reverse(bb(3)), 1);
    r.insert(Reverse(3), 2);
    r.insert(Reverse(4), 7);
    s += r.len() as u32 * 10 + r.get(&Reverse(3)).copied().unwrap_or(0)
        + r.get(&Reverse(4)).copied().unwrap_or(0) * 20;
    std::process::exit((s % 251) as i32);
}
"#,
    },
    // `.cloned()` over a dependency's `Copy` type whose hand-written `clone`
    // returns `N(self.0 + 1)`: std runs it, so `N(5)` clones to `N(6)`.
    // Baseline (e71a322f1 and 33eefbf58): diverged at O0/O1, LLVM exit 11,
    // bridge exit 10 (the clone was modeled as a load); matched at O2/O3.
    Guest {
        name: "c14_cloned_upstream_copy_handwritten_clone",
        unwind: false,
        dep: Some(DEP_COPY_HANDWRITTEN_CLONE),
        expect: Expect::Match,
        src: C14_SRC,
    },
    // The same program under panic=unwind.
    // Baseline (e71a322f1): diverged at O0/O1, LLVM exit 11, bridge exit 10;
    // matched at O2/O3.
    Guest {
        name: "c14u_cloned_upstream_copy_handwritten_clone_unwind",
        unwind: true,
        dep: Some(DEP_COPY_HANDWRITTEN_CLONE),
        expect: Expect::Match,
        src: C14_SRC,
    },
    // `.cloned()` over core's own hand-written `clone` of a `Copy` type
    // (`NonZeroU32`), which the same check keeps as a load.
    // Baseline: compiled and matched at O0-O3 at e71a322f1 (exit 11).
    Guest {
        name: "c15_cloned_core_copy_clone",
        unwind: false,
        dep: None,
        expect: Expect::Match,
        src: r#"use std::num::NonZeroU32;
fn main() {
    let c = [NonZeroU32::new(std::hint::black_box(3)).unwrap(), NonZeroU32::new(4).unwrap()];
    std::process::exit(c.iter().cloned().any(|n| n.get() == 4) as i32 + 10);
}
"#,
    },
];

/// `or_default` on a value whose builtin-derived `Default` has a default field
/// value (shared by an abort and an unwind row).
const V06_SRC: &str = r#"#![feature(default_field_values)]
use std::collections::HashMap;
#[derive(Default, Clone, Copy)]
struct W { x: u32 = 7 }
fn main() {
    let mut m: HashMap<u32, W> = HashMap::new();
    m.entry(std::hint::black_box(1)).or_default().x += 1;
    let g = m.get(&1).map(|w| w.x).unwrap_or(99);
    std::process::exit(g as i32);
}
"#;

/// A `BTreeMap` keyed by the upstream `K` of `DEP_ATTRIBUTED_HANDWRITTEN`
/// (shared by an abort and an unwind row).
const U01_SRC: &str = r#"use std::collections::BTreeMap;
use dep::K;
fn main() {
    let mut m: BTreeMap<K, u32> = BTreeMap::new();
    m.insert(K(std::hint::black_box(1)), 10);
    let old = m.insert(K(std::hint::black_box(11)), 20).unwrap_or(9);
    let g = m.get(&K(21)).copied().unwrap_or(9);
    let c = m.contains_key(&K(31)) as u32;
    std::process::exit((m.len() as u32 * 100 + c * 10 + g % 10 + old) as i32);
}
"#;

/// An upstream key whose `PartialEq` / `Eq` / `PartialOrd` / `Ord` / `Hash` /
/// `Default` are hand-written (on `x % 10`, and `K(7)`) and each carries the
/// ungated `#[automatically_derived]` attribute.
const DEP_ATTRIBUTED_HANDWRITTEN: &str = r#"use std::cmp::Ordering;
#[derive(Clone, Copy)]
pub struct K(pub u32);
#[automatically_derived]
impl PartialEq for K { fn eq(&self, o: &K) -> bool { self.0 % 10 == o.0 % 10 } }
#[automatically_derived]
impl Eq for K {}
#[automatically_derived]
impl PartialOrd for K { fn partial_cmp(&self, o: &K) -> Option<Ordering> { Some(self.cmp(o)) } }
#[automatically_derived]
impl Ord for K { fn cmp(&self, o: &K) -> Ordering { (self.0 % 10).cmp(&(o.0 % 10)) } }
#[automatically_derived]
impl std::hash::Hash for K { fn hash<H: std::hash::Hasher>(&self, h: &mut H) { (self.0 % 10).hash(h) } }
#[automatically_derived]
impl Default for K { fn default() -> K { K(7) } }
"#;

/// An upstream value whose builtin-derived `Default` has a default field value.
const DEP_FIELD_DEFAULT_VALUE: &str = r#"#![feature(default_field_values)]
#[derive(Clone, Copy, Default)]
pub struct W { pub x: u32 = 7 }
"#;

/// Upstream types whose impls are rustc's builtin derives.
const DEP_BUILTIN_DERIVES: &str = r#"#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Debug)]
pub struct K(pub u32);
#[derive(Clone, Copy, Default)]
pub struct D(pub u16);
"#;

/// `.cloned().any(..)` over the upstream `N` of `DEP_COPY_HANDWRITTEN_CLONE`
/// (shared by an abort and an unwind row).
const C14_SRC: &str = r#"use dep::N;
fn main() {
    let b = [N(std::hint::black_box(1)), N(5)];
    std::process::exit(b.iter().cloned().any(|n| n.0 == 6) as i32 + 10);
}
"#;

/// An upstream `Copy` type whose `clone` is hand-written (not `*self`).
const DEP_COPY_HANDWRITTEN_CLONE: &str = r#"#[derive(Copy, PartialEq)]
pub struct N(pub u32);
impl Clone for N { fn clone(&self) -> N { N(self.0 + 1) } }
"#;

/// How one side of a cell ended.
#[derive(Debug, PartialEq, Eq)]
enum Ending {
    Exit { code: Option<i32>, stdout: String },
    TimedOut,
}

/// How one `(guest, opt)` cell came out.
struct Cell {
    guest: &'static Guest,
    opt: u32,
    llvm: Result<Ending, String>,
    bridge: Result<Ending, String>,
}

fn compile(
    dir: &Path,
    guest: &Guest,
    opt: u32,
    backend: Option<(&Path, &str)>,
) -> Result<PathBuf, String> {
    let lane = if backend.is_some() { "tcg" } else { "llvm" };
    // One lane's compiler command for a crate of `crate_type`.
    let command_for = |crate_type: &str| {
        let mut command = toolchain_support::rustc_command_with_edition("2021");
        command
            .args([
                "--target",
                TARGET,
                "--crate-type",
                crate_type,
                "-Ccodegen-units=1",
            ])
            .arg(if guest.unwind {
                "-Cpanic=unwind"
            } else {
                "-Cpanic=abort"
            })
            .arg(format!("-Copt-level={opt}"));
        if let Some((dylib, knobs)) = backend {
            let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
            arg.push(dylib);
            command.arg(arg).arg(knobs);
        }
        command
    };
    let finish = |output: std::process::Output, artifact: PathBuf| {
        if output.status.success() {
            Ok(artifact)
        } else {
            Err(String::from_utf8_lossy(&output.stderr).into_owned())
        }
    };
    let mut command = command_for("bin");
    if let Some(dep) = guest.dep {
        let dep_src = dir.join(format!("{}_dep.rs", guest.name));
        std::fs::write(&dep_src, dep).expect("write dependency");
        let rlib = dir.join(format!("libdep-{lane}-O{opt}.rlib"));
        let output = command_for("rlib")
            .args(["--crate-name", "dep", "-o"])
            .arg(&rlib)
            .arg(&dep_src)
            .output()
            .expect("spawn the compiler");
        let rlib = finish(output, rlib).map_err(|stderr| format!("dependency: {stderr}"))?;
        let mut arg = std::ffi::OsString::from("dep=");
        arg.push(&rlib);
        command.arg("--extern").arg(arg);
    }
    let src = dir.join(format!("{}.rs", guest.name));
    std::fs::write(&src, guest.src).expect("write guest");
    let exe = dir.join(format!("{}-{lane}-O{opt}", guest.name));
    let output = command
        .arg("-o")
        .arg(&exe)
        .arg(&src)
        .output()
        .expect("spawn the compiler");
    finish(output, exe)
}

fn run(exe: &Path) -> Ending {
    let mut child = Command::new(exe)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("run guest");
    let started = Instant::now();
    loop {
        if let Some(status) = child.try_wait().expect("wait for guest") {
            let mut stdout = String::new();
            child
                .stdout
                .take()
                .expect("guest stdout")
                .read_to_string(&mut stdout)
                .expect("read guest stdout");
            return Ending::Exit {
                code: status.code(),
                stdout,
            };
        }
        if started.elapsed() > RUN_LIMIT {
            let _ = child.kill();
            let _ = child.wait();
            return Ending::TimedOut;
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}

/// Build and run every `(guest, opt)` cell of `expect`, LLVM and bridge, on a
/// few worker threads. `knobs` is the one traced knob argument, built on the
/// test's own thread.
fn run_cells(label: &str, expect: Expect, knobs: &str) -> Vec<Cell> {
    let backend = backend_artifact_support::current_test_backend();
    let dir = std::env::temp_dir().join(format!("tcg_map_model_{label}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("cell dir");
    let work: Vec<(&'static Guest, u32)> = GUESTS
        .iter()
        .filter(|guest| guest.expect == expect)
        .flat_map(|guest| OPTS.iter().map(move |&opt| (guest, opt)))
        .collect();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let workers = std::thread::available_parallelism().map_or(2, |n| n.get().clamp(2, 8));
    let mut cells: Vec<Cell> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..workers)
            .map(|_| {
                scope.spawn(|| {
                    let mut done = Vec::new();
                    loop {
                        let index = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        let Some(&(guest, opt)) = work.get(index) else {
                            return done;
                        };
                        let cell_dir = dir.join(format!("{}-O{opt}", guest.name));
                        std::fs::create_dir_all(&cell_dir).expect("cell dir");
                        let llvm = compile(&cell_dir, guest, opt, None).map(|exe| run(&exe));
                        let bridge = compile(&cell_dir, guest, opt, Some((&backend, knobs)))
                            .map(|exe| run(&exe));
                        done.push(Cell {
                            guest,
                            opt,
                            llvm,
                            bridge,
                        });
                    }
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|handle| handle.join().expect("cell worker"))
            .collect()
    });
    let _ = std::fs::remove_dir_all(&dir);
    cells.sort_by_key(|cell| (cell.guest.name, cell.opt));
    cells
}

/// Whether a failed compile's stderr is a crash rather than a refusal.
fn crashed(stderr: &str) -> bool {
    stderr.contains("panicked at") || stderr.contains("internal compiler error")
}

/// The bracketed `[TCG-...]` codes in `stderr`, for a failure message.
fn codes(stderr: &str) -> Vec<&str> {
    let mut found: Vec<&str> = stderr
        .match_indices("[TCG-")
        .filter_map(|(start, _)| {
            stderr[start..]
                .find(']')
                .map(|end| &stderr[start..=start + end])
        })
        .collect();
    found.sort_unstable();
    found.dedup();
    found
}

#[test]
fn map_model_refuses_user_traits_drops_and_hashers_aarch64() {
    darwin_native::require("map_model_user_trait_differential_aarch64", &[]);
    let knobs = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    let cells = run_cells("refuse", Expect::Refuse, &knobs);
    let mut wrong = Vec::new();
    for cell in &cells {
        let at = format!("{} O{}", cell.guest.name, cell.opt);
        match &cell.llvm {
            Ok(Ending::Exit { .. }) => {}
            other => wrong.push(format!(
                "{at}: the LLVM oracle did not run to an exit: {other:?}"
            )),
        }
        match &cell.bridge {
            Err(stderr) if stderr.contains(REFUSAL) && !crashed(stderr) => {}
            Err(stderr) => wrong.push(format!(
                "{at}: failed without {REFUSAL} (codes {:?}, crash={})",
                codes(stderr),
                crashed(stderr)
            )),
            Ok(ending) => wrong.push(format!(
                "{at}: COMPILED (the model was applied): bridge {ending:?}, LLVM {:?}",
                cell.llvm
            )),
        }
    }
    assert!(
        wrong.is_empty(),
        "{} of {} refusal cells are wrong:\n{}",
        wrong.len(),
        cells.len(),
        wrong.join("\n")
    );
    let guests = GUESTS.iter().filter(|g| g.expect == Expect::Refuse).count();
    eprintln!(
        "MAP_MODEL_USER_TRAIT_REFUSALS guests={guests} cells={} refused={} llvm_runs={} opts=0,1,2,3",
        cells.len(),
        cells.len(),
        cells.len()
    );
    positive_evidence::record(
        positive_evidence::Evidence::ExpectedRefusal,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn map_model_still_serves_primitive_and_derived_types_aarch64() {
    darwin_native::require("map_model_user_trait_differential_aarch64", &[]);
    let knobs = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    let cells = run_cells("match", Expect::Match, &knobs);
    let mut wrong = Vec::new();
    for cell in &cells {
        let at = format!("{} O{}", cell.guest.name, cell.opt);
        match (&cell.llvm, &cell.bridge) {
            (Ok(llvm @ Ending::Exit { .. }), Ok(bridge)) if llvm == bridge => {}
            (Ok(llvm), Ok(bridge)) => {
                wrong.push(format!("{at}: DIVERGES: LLVM {llvm:?}, bridge {bridge:?}"))
            }
            (Err(stderr), _) => wrong.push(format!("{at}: the LLVM oracle failed: {stderr}")),
            (Ok(_), Err(stderr)) => wrong.push(format!(
                "{at}: the bridge refused a control (codes {:?}, crash={})",
                codes(stderr),
                crashed(stderr)
            )),
        }
    }
    assert!(
        wrong.is_empty(),
        "{} of {} control cells are wrong:\n{}",
        wrong.len(),
        cells.len(),
        wrong.join("\n")
    );
    let guests = GUESTS.iter().filter(|g| g.expect == Expect::Match).count();
    eprintln!(
        "MAP_MODEL_LANE_CONTROLS guests={guests} cells={} matched={} opts=0,1,2,3",
        cells.len(),
        cells.len()
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
