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

// Constant-index slice and array places — `(*s)[k of n]`, `(*s)[-k of n]`,
// `a[from..to]` — through std's slice algorithms, slice patterns and raw
// pointers: stdout and exit code of every guest, LLVM against the bridge, at
// -O0 through -O3, over `i64`, `u8`, `(u32, u32)` and a struct.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// MEASURED before the fix (2026-10-03, backend built from trust-cg 33eefbf58):
//   * `&raw (*s)[k of n]` — GVN's fold of `&raw mut s[0]` in `<[T]>::swap`
//     (core's `heapsort`), of `get_unchecked(1)` (`find_existing_run`), and a
//     slice-pattern binding cast to a pointer — refused with `Rvalue::RawPtr
//     (unsupported &raw shape ...)`: `sort_unstable` at -O2/-O3 for every
//     element type, the shared corpus's `p13_sort_std`, and every raw-pointer
//     use here above -O0.
//   * `[.., last]` / `[.., p, _]` over `&[&dyn Trait]` at -O1..-O3 COMPILED AND
//     READ ELEMENT 0: `fromend_dyn` printed `k2 1001001012` where LLVM printed
//     `k2 1002001012` (`min_length - offset` taken as the index).
//   * a whole aggregate element copied out of a slice from its end, a payload
//     field borrowed from it, and its discriminant (`[.., Some(x)]`) refused
//     with `from-end ConstantIndex ... needs the runtime slice length`; a whole
//     aggregate element of a local array at a GVN-folded constant index refused
//     with `memory aggregate field projection ConstantIndex`; an array's
//     `[_, mid @ .., _]` subarray refused with `indexed memory place
//     projection Subslice`.
//
// Cells another lowering family refuses are pinned by name in KNOWN_REFUSALS
// (shrink-only): a listed cell that compiles fails until its row is deleted,
// and an unlisted refusal fails. No bridge compile here may print a refusal of
// this family (FAMILY_REFUSALS).
//
// PROOF GATE: compiled with `no-proof-certs`; an execution differential, not a
// certification claim.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

const TARGET: &str = "aarch64-apple-darwin";
const OPTS: [u32; 4] = [0, 1, 2, 3];

/// Shared by the element guests: `ELEM` names the element type, `case` is the
/// guest's body, and `main` prints one hash per slice length and exits with
/// the total.
const PRELUDE: &str = r##"
#![allow(dead_code)]
use std::hint::black_box;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Rec {
    key: u32,
    tag: u8,
    w: i16,
}

trait Elem: Copy + Ord {
    fn h(&self) -> u64;
    fn make(x: u64) -> Self;
}
impl Elem for i64 {
    fn h(&self) -> u64 {
        *self as u64
    }
    fn make(x: u64) -> Self {
        (x % 97) as i64 - 48
    }
}
impl Elem for u8 {
    fn h(&self) -> u64 {
        *self as u64
    }
    fn make(x: u64) -> Self {
        (x % 61) as u8
    }
}
impl Elem for (u32, u32) {
    fn h(&self) -> u64 {
        ((self.0 as u64) << 32) | self.1 as u64
    }
    fn make(x: u64) -> Self {
        ((x % 11) as u32, (x % 13) as u32)
    }
}
impl Elem for Rec {
    fn h(&self) -> u64 {
        (self.key as u64) * 1000 + (self.tag as u64) * 7 + (self.w as u16 as u64)
    }
    fn make(x: u64) -> Self {
        Rec { key: (x % 23) as u32, tag: (x % 5) as u8, w: (x % 17) as i16 - 8 }
    }
}

fn mix(h: u64, x: u64) -> u64 {
    (h ^ x).wrapping_mul(0x100000001b3).wrapping_add(x >> 7)
}

fn gen<T: Elem>(n: usize, seed: u64) -> Vec<T> {
    let mut v = Vec::new();
    let mut x = seed;
    let mut i = 0;
    while i < n {
        x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        v.push(T::make(x >> 33));
        i += 1;
    }
    v
}

fn fold<T: Elem>(mut h: u64, s: &[T]) -> u64 {
    let mut i = 0;
    while i < s.len() {
        h = mix(h, s[i].h());
        i += 1;
    }
    mix(h, s.len() as u64)
}

const SIZES: [usize; 9] = [0, 1, 2, 3, 4, 7, 20, 33, 100];

fn main() {
    let mut total = 17u64;
    let mut i = 0;
    while i < SIZES.len() {
        let n = black_box(SIZES[i]);
        let x = case::<ELEM>(n, 11 + n as u64);
        println!("n{} {}", n as u64, x);
        total = mix(total, x);
        i += 1;
    }
    println!("total {}", total);
    std::process::exit((total % 251) as i32);
}
"##;

/// Patterns, `split_first`/`split_last`/`first`/`last`, rotations.
const SHAPE: &str = r##"
// Slice patterns, split_first/split_last/first/last and rotations: the
// `(*s)[k of n]`, `(*s)[-k of n]` and `(*s)[a:b]` places, read by reference
// and copied out by value.
#[inline(never)]
fn patterns<T: Elem>(s: &[T]) -> u64 {
    let mut h = 1u64;
    match s {
        [a, b, rest @ ..] => {
            h = mix(h, a.h());
            h = mix(h, b.h());
            h = fold(h, rest);
        }
        [a] => h = mix(h, a.h() + 5),
        [] => h = mix(h, 9),
    }
    if let &[.., x] = s {
        h = mix(h, x.h());
    }
    if let &[x, .., y] = s {
        h = mix(h, x.h().wrapping_sub(y.h()));
    }
    if let [_, mid @ .., _] = s {
        h = fold(h, mid);
    }
    if let [.., p, _] = s {
        h = mix(h, p.h());
    }
    if let Some((f, rest)) = s.split_first() {
        h = mix(h, f.h());
        h = fold(h, rest);
    }
    if let Some((l, rest)) = s.split_last() {
        h = mix(h, l.h());
        h = fold(h, rest);
    }
    h = mix(h, match s.first() { Some(x) => x.h(), None => 77 });
    h = mix(h, match s.last() { Some(x) => x.h(), None => 78 });
    h
}

fn case<T: Elem>(n: usize, seed: u64) -> u64 {
    let mut v: Vec<T> = gen(n, seed);
    let mut h = mix(seed, patterns(&v));
    if n > 0 {
        v.rotate_left(3 % n);
        h = fold(h, &v);
        v.rotate_right(1);
        h = fold(h, &v);
        h = mix(h, patterns(&v));
    }
    h
}
"##;

/// Raw pointers to constant-index places, `get_unchecked`, arrays.
const RAW: &str = r##"
// Raw pointers to constant-index places: `&raw (*s)[k]` (GVN folds a known
// index), pattern bindings turned into raw pointers (`[first, .., last]`,
// `[.., pen, _]`, from the end), `get_unchecked`, and arrays (`&raw a[k]`,
// `[f, .., l]` on `[T; 5]`, the `[_, mid @ .., _]` subarray).
#[inline(never)]
fn raw_ends<T: Elem>(s: &mut [T]) -> u64 {
    let mut h = 3u64;
    if s.len() >= 3 {
        unsafe {
            let p0 = &raw const s[0];
            let p1 = &raw mut s[1];
            let p2 = &raw const s[2];
            h = mix(h, (*p0).h());
            h = mix(h, (*p2).h());
            core::ptr::swap(p1, &raw mut s[0]);
            *p1 = *p2;
        }
    }
    if let [first, .., last] = s {
        let a = first as *mut T;
        let b = last as *mut T;
        unsafe {
            core::ptr::swap(a, b);
            h = mix(h, (*a).h());
            h = mix(h, (b as *const T).offset_from(a as *const T) as u64);
        }
    }
    if let [.., pen, _] = s {
        let p = pen as *const T;
        unsafe {
            h = mix(h, (*p).h());
        }
    }
    if let [x, y, .., z] = s {
        let px = x as *mut T;
        let py = y as *const T;
        let pz = z as *const T;
        unsafe {
            *px = *pz;
            h = mix(h, (*py).h());
        }
    }
    fold(h, s)
}

#[inline(never)]
fn raw_shared<T: Elem>(s: &[T]) -> u64 {
    let mut h = 5u64;
    if s.len() >= 2 {
        unsafe {
            let a = s.get_unchecked(1) as *const T;
            let b = s.get_unchecked(0) as *const T;
            h = mix(h, (*a).h().wrapping_sub((*b).h()));
            h = mix(h, a.offset_from(b) as u64);
        }
    }
    if let [.., l] = s {
        let p = l as *const T;
        unsafe {
            h = mix(h, (*p).h());
            h = mix(h, p.offset_from(s.as_ptr()) as u64);
        }
    }
    h
}

#[inline(never)]
fn raw_array<T: Elem>(a: &mut [T; 5], seed: u64) -> u64 {
    let mut h = seed;
    let mut local = *a;
    unsafe {
        let p = &raw mut local[3];
        let q = &raw const a[1];
        *p = *q;
        let [f, .., l] = &mut local;
        let pf = f as *mut T;
        let pl = l as *const T;
        *pf = *pl;
        let [_, mid @ .., _] = &*a;
        h = fold(h, mid);
        let r = &raw mut a[4];
        *r = local[0];
    }
    h = fold(h, &local);
    fold(h, &a[..])
}

fn case<T: Elem>(n: usize, seed: u64) -> u64 {
    let mut v: Vec<T> = gen(n, seed);
    let mut h = mix(seed, raw_ends(&mut v));
    h = mix(h, raw_shared(&v));
    let mut arr = [T::make(seed), T::make(seed + 22), T::make(3), T::make(seed * 7), T::make(5)];
    h = mix(h, raw_array(&mut arr, seed));
    fold(h, &arr)
}
"##;

/// Writes through slice-pattern places.
const WRITE: &str = r##"
// Writes through slice-pattern places, from the front and from the end.
#[inline(never)]
fn write_ends<T: Elem>(s: &mut [T]) -> u64 {
    if let [first, .., last] = s {
        core::mem::swap(first, last);
    }
    if let [.., p, l] = s {
        *p = *l;
    }
    if let [a, b, ..] = s {
        *b = *a;
    }
    fold(5, s)
}

fn case<T: Elem>(n: usize, seed: u64) -> u64 {
    let mut v: Vec<T> = gen(n, seed);
    let h = mix(seed, write_ends(&mut v));
    fold(h, &v)
}
"##;

/// `sort_unstable`, `binary_search`, `dedup`.
const UNSTABLE: &str = r##"
// `sort_unstable` (core's ipnsort, `find_existing_run`, `heapsort`), `dedup`
// and `binary_search`.
fn case<T: Elem>(n: usize, seed: u64) -> u64 {
    let mut b: Vec<T> = gen(n, seed);
    b.sort_unstable();
    let mut h = fold(seed, &b);
    let probe = T::make(seed / 2);
    h = mix(h, match b.binary_search(&probe) { Ok(i) => b[i].h() + 1, Err(i) => i as u64 * 3 });
    b.dedup();
    h = fold(h, &b);
    // 24 elements (above ipnsort's insertion-sort cutoff) whose first pair
    // descends and whose tail from index 1 ascends: `find_existing_run` must
    // compare `v[1]` (its `get_unchecked(1)`) with `v[0]`, find a run of 2, and
    // quicksort. Read at any other index, the whole slice looks like one
    // ascending run and is returned unsorted. `make` is monotone below 11.
    let mut r: Vec<T> = Vec::new();
    r.push(T::make(5));
    r.push(T::make(3));
    let mut k = 0u64;
    while k < 22 {
        r.push(T::make(6 + k / 5));
        k += 1;
    }
    r.sort_unstable();
    h = fold(h, &r);
    h
}
"##;

/// `sort`, `sort_by_key`.
const STABLE: &str = r##"
// The stable sorts: `sort` and `sort_by_key`.
fn case<T: Elem>(n: usize, seed: u64) -> u64 {
    let mut a: Vec<T> = gen(n, seed);
    a.sort();
    let mut h = fold(seed, &a);
    let mut c: Vec<T> = gen(n, seed);
    c.sort_by_key(|x| 7 - x.h() % 7);
    h = fold(h, &c);
    h
}
"##;

/// `select_nth_unstable`.
const SELECT: &str = r##"
// `select_nth_unstable`.
fn case<T: Elem>(n: usize, seed: u64) -> u64 {
    let mut h = seed;
    if n > 0 {
        let mut d: Vec<T> = gen(n, seed);
        let (lo, mid, hi) = d.select_nth_unstable(n / 2);
        let m = *mid;
        h = mix(h, m.h());
        let mut ok = 0u64;
        let mut i = 0;
        while i < lo.len() {
            ok += (lo[i] <= m) as u64;
            i += 1;
        }
        let mut j = 0;
        while j < hi.len() {
            ok += (hi[j] >= m) as u64;
            j += 1;
        }
        h = mix(h, ok * 1000 + lo.len() as u64);
    }
    h
}
"##;

/// From-end places over `&dyn` elements: the live miscompile (see the header).
const FROMEND_DYN: &str = r##"
// From-end places over `&dyn` elements (two pointer lanes per element).
use std::hint::black_box;

trait Val {
    fn v(&self) -> u64;
}
struct A(u64);
impl Val for A {
    fn v(&self) -> u64 {
        self.0
    }
}

#[inline(never)]
fn dyn_ends(s: &[&dyn Val]) -> u64 {
    let mut h = 1u64;
    if let [.., l] = s {
        h = h * 1000 + l.v();
    }
    if let [.., p, _] = s {
        h = h * 1000 + p.v();
    }
    if let [f, .., l] = s {
        h = h * 1000 + f.v() * 10 + l.v();
    }
    h
}

fn main() {
    let a = A(1);
    let b = A(2);
    let c = A(3);
    let d = A(4);
    let e = A(5);
    let all: [&dyn Val; 5] = [&a, &b, &c, &d, &e];
    let mut total = 0u64;
    let mut n = 0usize;
    while n <= 5 {
        let k = black_box(n);
        let x = dyn_ends(&all[..k]);
        println!("k{} {}", k as u64, x);
        total = total.wrapping_mul(1_000_003).wrapping_add(x);
        n += 1;
    }
    println!("total {}", total);
    std::process::exit((total % 251) as i32);
}
"##;

/// From-end places over `Option<u32>` elements.
const FROMEND_OPT: &str = r##"
// From-end places over `Option<u32>` elements: matched by discriminant, a
// payload field borrowed, the whole element copied out.
use std::hint::black_box;

#[inline(never)]
fn opt_ends(s: &[Option<u32>]) -> u64 {
    let mut h = 2u64;
    match s {
        [.., Some(x)] => h = h * 1000 + *x as u64,
        [.., None] => h = h * 1000 + 999,
        [] => h += 1,
    }
    if let &[.., p, _] = s {
        h = h * 1000 + match p { Some(v) => v as u64, None => 998 };
    }
    if let [Some(a), .., Some(z)] = s {
        h = h * 1000 + (*a as u64) * 10 + *z as u64;
    }
    h
}

fn main() {
    let opts = [Some(7u32), None, Some(9), Some(11), Some(13), None, Some(17)];
    let mut total = 0u64;
    let mut n = 0usize;
    while n <= 7 {
        let k = black_box(n);
        let y = opt_ends(&opts[k..]);
        println!("k{} {}", k as u64, y);
        total = total.wrapping_mul(1_000_003).wrapping_add(y);
        n += 1;
    }
    println!("total {}", total);
    std::process::exit((total % 251) as i32);
}
"##;

/// From-end places over `bool` and `f64` elements.
const FROMEND_SCALAR: &str = r##"
// From-end places over `bool` and `f64` elements, read and written.
use std::hint::black_box;

#[inline(never)]
fn bool_ends(s: &[bool]) -> u64 {
    let mut h = 3u64;
    if let [.., a, b] = s {
        h = h * 10 + (*a as u64) * 2 + *b as u64;
    }
    if let [first, .., last] = s {
        h = h * 10 + (*first as u64) * 2 + *last as u64;
    }
    h
}

#[inline(never)]
fn f64_ends(s: &mut [f64]) -> u64 {
    if let [first, .., last] = s {
        *first = *first + *last * 2.0;
    }
    let mut h = 4u64;
    if let [.., p, l] = s {
        h = h.wrapping_mul(31).wrapping_add((*p * 4.0) as u64 + (*l * 8.0) as u64);
    }
    if let [f, ..] = s {
        h = h.wrapping_mul(31).wrapping_add((*f * 16.0) as u64);
    }
    h
}

fn main() {
    let bools = [true, false, false, true, true, false];
    let mut floats = [1.5f64, 2.25, 3.0, 4.75, 5.5];
    let mut total = 0u64;
    let mut n = 0usize;
    while n <= 6 {
        let k = black_box(n);
        let z = bool_ends(&bools[..k]);
        println!("k{} {}", k as u64, z);
        total = total.wrapping_mul(1_000_003).wrapping_add(z);
        n += 1;
    }
    let mut m = 0usize;
    while m <= 5 {
        let w = f64_ends(black_box(&mut floats[..m]));
        println!("f{} {} {}", m as u64, w, floats[0] as u64);
        total = total.wrapping_add(w);
        m += 1;
    }
    println!("total {}", total);
    std::process::exit((total % 251) as i32);
}
"##;

/// The element types every generic guest is instantiated at: (suffix, type).
const ELEMS: [(&str, &str); 4] = [
    ("i64", "i64"),
    ("u8", "u8"),
    ("pair", "(u32, u32)"),
    ("rec", "Rec"),
];

/// Bridge refusals of OTHER lowering families, by name: (guest, opt levels,
/// the diagnostic the bridge must print). Shrink-only. Measured 2026-10-03.
const KNOWN_REFUSALS: &[(&str, &[u32], &str)] = &[
    // `<[T]>::sort`/`sort_unstable` interception models integer elements only.
    (
        "unstable_pair",
        &[0, 1],
        "<[(u32, u32)]>::sort over a non-integer element is not modeled",
    ),
    (
        "unstable_rec",
        &[0, 1],
        "<[Rec]>::sort over a non-integer element is not modeled",
    ),
    (
        "stable_pair",
        &[0, 1],
        "<[(u32, u32)]>::sort over a non-integer element is not modeled",
    ),
    (
        "stable_pair",
        &[2, 3],
        "<[(u32, u32)]>::sort_by_key over a non-integer element is not modeled",
    ),
    (
        "stable_rec",
        &[0, 1],
        "<[Rec]>::sort over a non-integer element is not modeled",
    ),
    (
        "stable_rec",
        &[2, 3],
        "<[Rec]>::sort_by_key over a non-integer element is not modeled",
    ),
    // core's `driftsort_main` scratch buffer.
    (
        "stable_i64",
        &[2, 3],
        "Vec::<i64>::as_uninit_slice_mut is not an intercepted Vec method",
    ),
    (
        "stable_u8",
        &[2, 3],
        "Vec::<u8>::as_uninit_slice_mut is not an intercepted Vec method",
    ),
    // core's `select::min_index` / `max_index` (`Enumerate::reduce`).
    (
        "select_i64",
        &[0, 1, 2, 3],
        "iterator fold over a tuple-yielding chain is not modeled",
    ),
    (
        "select_u8",
        &[0, 1, 2, 3],
        "iterator fold over a tuple-yielding chain is not modeled",
    ),
    (
        "select_pair",
        &[0, 1, 2, 3],
        "[TCG-ITER-UNMODELED] iterator `fold` terminal over an unmodeled chain",
    ),
    (
        "select_rec",
        &[0, 1, 2, 3],
        "[TCG-ITER-UNMODELED] iterator `fold` terminal over an unmodeled chain",
    ),
];

/// The refusals this lowering closed. A bridge compile that prints one of these
/// has lost the capability this file pins.
const FAMILY_REFUSALS: &[&str] = &[
    "unsupported &raw shape",
    "from-end ConstantIndex",
    "memory aggregate field projection ConstantIndex",
    "indexed memory place projection Subslice",
];

struct Guest {
    name: String,
    src: String,
}

/// One guest per (body, element type): `<body name>_<element suffix>`.
fn element_guests(bodies: &[(&str, &str)]) -> Vec<Guest> {
    let mut guests = Vec::new();
    for (body_name, body) in bodies {
        for (suffix, ty) in ELEMS {
            guests.push(Guest {
                name: format!("{body_name}_{suffix}"),
                src: format!("{}\n{body}", PRELUDE.replace("ELEM", ty)),
            });
        }
    }
    guests
}

fn compile(dir: &Path, guest: &Guest, opt: u32, backend: Option<&Path>) -> Result<PathBuf, String> {
    let lane = if backend.is_some() { "cg" } else { "llvm" };
    let src = dir.join(format!("{}.rs", guest.name));
    std::fs::write(&src, &guest.src).expect("write guest");
    let exe = dir.join(format!("{}_{lane}_O{opt}", guest.name));
    let mut command = toolchain_support::rustc_command_with_edition("2021");
    command
        .args([
            "--target",
            TARGET,
            "-Cpanic=abort",
            "-Coverflow-checks=off",
            "-Ccodegen-units=1",
        ])
        .arg(format!("-Copt-level={opt}"));
    if let Some(backend) = backend {
        let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
        arg.push(backend);
        command
            .arg(arg)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    let output = command
        .arg("-o")
        .arg(&exe)
        .arg(&src)
        .output()
        .expect("spawn compiler");
    if output.status.success() {
        Ok(exe)
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

fn run(exe: &Path) -> (Option<i32>, String) {
    let output = Command::new(exe).output().expect("run guest");
    (
        output.status.code(),
        String::from_utf8_lossy(&output.stdout).into_owned(),
    )
}

/// Every (guest, opt) cell: LLVM and the bridge compile and run, and must print
/// the same stdout and exit the same, or the bridge refuses by a listed name.
/// Returns (matched, refused by name).
fn check(test: &str, guests: &[Guest]) -> (usize, usize) {
    darwin_native::require(test, &[]);
    let backend = backend_artifact_support::current_test_backend();
    let dir = std::env::temp_dir().join(format!("tcg_{test}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("cell dir");
    let cells: Vec<(usize, u32)> = (0..guests.len())
        .flat_map(|g| OPTS.iter().map(move |&opt| (g, opt)))
        .collect();
    let next = AtomicUsize::new(0);
    let failures = Mutex::new(Vec::new());
    let matched = AtomicUsize::new(0);
    let refused = AtomicUsize::new(0);
    let workers = std::thread::available_parallelism()
        .map_or(4, |n| n.get())
        .min(8);
    std::thread::scope(|scope| {
        for _ in 0..workers {
            scope.spawn(|| {
                loop {
                    let index = next.fetch_add(1, Ordering::SeqCst);
                    let Some(&(g, opt)) = cells.get(index) else {
                        break;
                    };
                    let guest = &guests[g];
                    let cell_dir = dir.join(format!("{}_O{opt}", guest.name));
                    std::fs::create_dir_all(&cell_dir).expect("cell dir");
                    let label = format!("{} O{opt}", guest.name);
                    let listed = KNOWN_REFUSALS
                        .iter()
                        .find(|(name, opts, _)| *name == guest.name && opts.contains(&opt));
                    let oracle = match compile(&cell_dir, guest, opt, None) {
                        Ok(exe) => run(&exe),
                        Err(stderr) => {
                            failures
                                .lock()
                                .unwrap()
                                .push(format!("{label}: LLVM compile failed:\n{stderr}"));
                            continue;
                        }
                    };
                    let outcome = compile(&cell_dir, guest, opt, Some(&backend));
                    let mut failed = failures.lock().unwrap();
                    match (outcome, listed) {
                        (Ok(_), Some((_, _, code))) => failed.push(format!(
                            "{label}: compiles now; delete its KNOWN_REFUSALS row ({code})"
                        )),
                        (Ok(exe), None) => {
                            let got = run(&exe);
                            if got == oracle {
                                matched.fetch_add(1, Ordering::SeqCst);
                            } else {
                                failed.push(format!(
                                    "{label}: WRONG exit {:?} stdout {:?}; LLVM exit {:?} \
                                     stdout {:?}",
                                    got.0, got.1, oracle.0, oracle.1
                                ));
                            }
                        }
                        (Err(stderr), listed) => {
                            if let Some(family) =
                                FAMILY_REFUSALS.iter().find(|text| stderr.contains(*text))
                            {
                                failed.push(format!(
                                    "{label}: refused by this lowering family ({family}):\n{stderr}"
                                ));
                            } else if listed.is_some_and(|(_, _, code)| stderr.contains(code)) {
                                refused.fetch_add(1, Ordering::SeqCst);
                            } else {
                                failed.push(format!("{label}: the bridge refused:\n{stderr}"));
                            }
                        }
                    }
                }
            });
        }
    });
    let failures = failures.into_inner().unwrap();
    assert!(
        failures.is_empty(),
        "{} of {} cells failed (artifacts {}):\n{}",
        failures.len(),
        cells.len(),
        dir.display(),
        failures.join("\n")
    );
    let _ = std::fs::remove_dir_all(&dir);
    let (matched, refused) = (matched.into_inner(), refused.into_inner());
    assert_eq!(matched + refused, cells.len());
    eprintln!(
        "SLICE_CONSTANT_INDEX test={test} cells={} matched={matched} refused_by_name={refused} \
         opts=0,1,2,3",
        cells.len()
    );
    (matched, refused)
}

/// Slice patterns, raw pointers, writes and `sort_unstable` over the four
/// element types: every cell runs except the pinned `sort_unstable`
/// interception refusals of the two aggregate elements at -O0/-O1.
#[test]
fn slice_constant_index_element_guests_match_llvm() {
    let guests = element_guests(&[
        ("shape", SHAPE),
        ("raw", RAW),
        ("write", WRITE),
        ("unstable", UNSTABLE),
    ]);
    assert_eq!(check("elements", &guests), (60, 4));
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// From-end places over elements with their own read paths: `&dyn`,
/// `Option<u32>`, `bool`, `f64`.
#[test]
fn slice_from_end_element_kinds_match_llvm() {
    let guests = [
        ("fromend_dyn", FROMEND_DYN),
        ("fromend_opt", FROMEND_OPT),
        ("fromend_scalar", FROMEND_SCALAR),
    ]
    .map(|(name, src)| Guest {
        name: name.to_owned(),
        src: src.to_owned(),
    });
    assert_eq!(check("from_end_kinds", &guests), (12, 0));
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// `sort`, `sort_by_key` and `select_nth_unstable`: the integer stable sorts
/// run at -O0/-O1; every other cell is another family's named refusal.
#[test]
fn std_stable_sort_and_select_match_llvm_or_refuse_by_name() {
    let guests = element_guests(&[("stable", STABLE), ("select", SELECT)]);
    assert_eq!(check("stable_select", &guests), (4, 28));
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
