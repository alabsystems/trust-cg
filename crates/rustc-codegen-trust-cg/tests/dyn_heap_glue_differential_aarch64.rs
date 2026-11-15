#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native_prerequisites;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/real_map_dyn_origin.rs"]
mod real_map_dyn_origin;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: heap drop glue reached through a `dyn` vtable
// ([TCG-HEAP-IMAGE-GLUE], `src/heap_image_glue.rs`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS. A dropped `Box<dyn Trait>` runs the vtable's drop slot,
// `drop_glue::<C>` for the concrete `C`. For an intercepted heap value (a `Box`
// chain, a `BTreeMap`) rustc's body for that glue reads `C` at rustc's layout
// and never lowered; it was a trap stub (SIGTRAP at the drop), then, since
// 0e8241693, a compile-time refusal in an executable and still a stub in a
// library. The glue is now lowered from its definition, `drop((*_1))`, with the
// same emission a direct `drop(Box<C>)` uses. Measured on 16a86a97b WITHOUT
// this change (same host, same programs): `dyn_mix_const` (a `Box<Box<u32>>`
// payload: "Drop of a projected Box place") and `dyn_btreemap_empty`
// ("`BTreeMap::<u64, u64>::drop` is not an intercepted BTreeMap method") refuse
// at all four levels, and every other row already behaves as pinned below:
// that base lowers a top-level `Vec`/`String` glue itself
// (`normalize_real_collection_drop_glue`, rustc-layout headers) and a
// `Box<i64>` one. With it, every `must_match` cell builds and matches LLVM.
//
// THE ORACLE IS EXIT STATUS + STDOUT + A HEAP LEDGER. Every program installs a
// `#[global_allocator]` that keeps NET live blocks and bytes (alloc +1/+size,
// dealloc -1/-size, realloc +new-old) and prints the change across the measured
// region, read before anything prints (the first print allocates stdout's
// buffer). `0 0` means nothing leaked and nothing was freed twice or with a
// different size than it was allocated with. A `BTreeMap` is the one payload
// here the bridge still models as a forwarding pointer to a separate 24-byte
// heap {ptr,cap,len} slot block; a glue that skips that block leaves `2 48`
// live in `dyn_btreemap_empty`, one block per map (mutation-checked: that
// mutant MISMATCHES there). The
// bridge's `Vec::new` / `BTreeMap::new` reserve a real buffer where LLVM's do
// not, so raw alloc COUNTS legitimately differ; only the net is compared. The
// binaries also run under `MallocScribble` / `MallocGuardEdges` /
// `MallocErrorAbort`, so a double free or a free of a non-heap address aborts.
//
// VERDICTS. A `must_match` cell must build and match. A `refuse_or_match` cell
// may instead fail closed — at `-O2`/`-O3` most of these refuse inside the
// TRAIT METHOD (`self.len()` inlines into a field read the bridge does not
// model), not in the glue; `dyn_mix_const` keeps every method a constant so the
// glue itself is exercised at all four levels. A mismatch is a failure
// everywhere. The `HashMap` rows are refuse-or-match on purpose:
// `heap_image_glue` does not admit a chain that holds a `HashMap`, because the
// bridge's -O2/-O3 empty-`HashMap` construction leaks one 16-byte buffer (on
// 16a86a97b a plain local `HashMap::<u64, u64>::new()` nets `1 16` there);
// re-admitting it before that is fixed makes those rows build and MISMATCH.
//
// The borrowed half. A `Vec` / `String` header is rustc's own inline layout
// wherever it lives, and its glue frees only the data buffer that header names,
// so a vtable for one built from a borrow is valid and must build and match
// (`dyn_heap_glue_borrowed_vec_string_vtable_matches_llvm_aarch64`; a refusal
// by [TCG-HEAP-IMAGE-VTABLE] there is a regression — 16a86a97b builds them).
// A `BTreeMap`'s glue frees the slot block a `Box<C>`'s heap image owns, which
// is wrong for any other pointer, so a vtable for one built from a borrow
// refuses ([TCG-HEAP-IMAGE-VTABLE]); a borrowed `HashMap` still refuses because
// its glue does not lower (`dyn_heap_glue_borrowed_map_vtable_fails_closed_aarch64`).
// A library stub a vtable references refuses ([TCG-HEAP-GLUE-STUB-REACHABLE]).
//
// Executes on an AArch64 host; the staticlib test needs Darwin's `nm`/`cc`.
// The bridge side passes `no-proof-certs` (certificates on refuse every AArch64
// program with `[TCG-PROOF-465]`, unrelated to this lane). Measured on
// aarch64-apple-darwin only; the Linux AArch64 unsize paths
// (`pointer_coercions`) carry the same origin check but were not executed.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const TARGET: &str = host_target_support::AARCH64_TARGET;

fn host_is_aarch64() -> bool {
    cfg!(target_arch = "aarch64") && host_target_support::HOST_OS_SUPPORTED
}

/// The shared guard: `true` when the caller must return (reason printed).
fn skip(test: &str) -> bool {
    if !host_is_aarch64() {
        eprintln!("{test}: skipping: the AArch64 run requires an AArch64 Linux or macOS host");
        return true;
    }
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    darwin_native_prerequisites::require(test, &[]);
    #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
    if toolchain_support::skip_without_backend_knobs(test) {
        return true;
    }
    if !toolchain_support::target_std_available(TARGET) {
        eprintln!("{test}: skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return true;
    }
    false
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_dyn_heap_glue_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> OsString {
    let mut s = OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// The counting allocator and print helpers every program starts with.
const PRELUDE: &str = r#"#![allow(dead_code)]
use std::alloc::{GlobalAlloc, Layout};
use std::hint::black_box;
unsafe extern "C" {
    fn malloc(size: usize) -> *mut u8;
    fn calloc(n: usize, size: usize) -> *mut u8;
    fn realloc(ptr: *mut u8, size: usize) -> *mut u8;
    fn free(ptr: *mut u8);
}
struct Count;
static mut BLOCKS: usize = 0;
static mut BYTES: usize = 0;
unsafe impl GlobalAlloc for Count {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        unsafe { BLOCKS = BLOCKS.wrapping_add(1); BYTES = BYTES.wrapping_add(l.size()); malloc(l.size()) }
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        unsafe { BLOCKS = BLOCKS.wrapping_add(1); BYTES = BYTES.wrapping_add(l.size()); calloc(1, l.size()) }
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        unsafe { BYTES = BYTES.wrapping_sub(l.size()).wrapping_add(n); realloc(p, n) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        unsafe { BLOCKS = BLOCKS.wrapping_sub(1); BYTES = BYTES.wrapping_sub(l.size()); free(p) }
    }
}
#[global_allocator]
static GLOBAL: Count = Count;
// Lower-case helper names must not collide with the statics' names on a
// case-insensitive file system: the bridge names one object per symbol.
#[inline(never)]
fn live_blocks() -> usize { unsafe { BLOCKS } }
#[inline(never)]
fn live_bytes() -> usize { unsafe { BYTES } }
#[inline(never)]
fn emit(x: usize) { println!("{}", x); }
// Keeps `__rust_alloc_zeroed` referenced for the std objects that call it.
#[inline(never)]
fn touch_alloc_zeroed() {
    let l = Layout::new::<u64>();
    unsafe { std::alloc::dealloc(std::alloc::alloc_zeroed(l), l) };
}
#[inline(never)]
fn report(b0: usize, y0: usize) {
    let b1 = live_blocks();
    let y1 = live_bytes();
    emit(b1.wrapping_sub(b0));
    emit(y1.wrapping_sub(y0));
}
trait Tr { fn n(&self) -> usize; }
"#;

/// How a program ended.
#[derive(Debug, PartialEq, Eq)]
enum Exit {
    Code(i32),
    Signal(i32),
}

struct Row {
    name: &'static str,
    body: &'static str,
    /// LLVM's exit and stdout (asserted on the oracle too, so a corrupted
    /// oracle cannot make a wrong value agree).
    exit: Exit,
    stdout: &'static str,
    must_match: &'static [&'static str],
    refuse_or_match: &'static [&'static str],
}

const ROWS: &[Row] = &[
    Row {
        name: "dyn_vec",
        body: r#"impl Tr for Vec<u8> { fn n(&self) -> usize { self.len() + self[2] as usize } }
#[inline(never)] fn make(k: u8) -> Box<dyn Tr> { Box::new(vec![1u8, 2, k]) }
fn main() {
    touch_alloc_zeroed();
    emit(0);
    let b0 = live_blocks(); let y0 = live_bytes();
    let b = make(black_box(3));
    let n = b.n();
    drop(b);
    report(b0, y0);
    emit(n);
}
"#,
        exit: Exit::Code(0),
        stdout: "0\n0\n0\n6",
        must_match: &["0", "1", "2", "3"],
        refuse_or_match: &[],
    },
    Row {
        name: "dyn_mix_const",
        body: r#"impl Tr for Vec<u8> { fn n(&self) -> usize { 1 } }
impl Tr for Vec<u64> { fn n(&self) -> usize { 2 } }
impl Tr for String { fn n(&self) -> usize { 4 } }
impl Tr for Box<i64> { fn n(&self) -> usize { 8 } }
impl Tr for Box<Box<u32>> { fn n(&self) -> usize { 16 } }
impl Tr for Box<Vec<u8>> { fn n(&self) -> usize { 32 } }
#[inline(never)] fn mk(i: usize, k: u8) -> Box<dyn Tr> {
    match i % 8 {
        0 => Box::new(vec![k; 5]),
        1 => Box::new(vec![k as u64, 9, 9, 9, 9, 9, 9, 9, 9]),
        2 => Box::new(String::from("hello world")),
        3 => Box::new(Vec::<u8>::new()),
        4 => Box::new(String::new()),
        5 => Box::new(Box::new(k as i64)),
        6 => Box::new(Box::new(Box::new(k as u32))),
        _ => Box::new(Box::new(vec![k, k, k])),
    }
}
fn main() {
    touch_alloc_zeroed();
    emit(0);
    let b0 = live_blocks(); let y0 = live_bytes();
    let mut total = 0usize;
    for i in 0..black_box(24usize) { let b = mk(i, black_box(3)); total += b.n(); }
    report(b0, y0);
    emit(total);
}
"#,
        exit: Exit::Code(0),
        stdout: "0\n0\n0\n204",
        must_match: &["0", "1", "2", "3"],
        refuse_or_match: &[],
    },
    Row {
        // Empty buffers from the other constructors (`to_vec` of an empty slice,
        // `collect` of an empty range): the glue must not free a dangling
        // pointer (MallocErrorAbort would abort) and must free what was reserved.
        name: "dyn_empty_src",
        body: r#"impl Tr for Vec<u8> { fn n(&self) -> usize { 1 } }
#[inline(never)] fn e1(s: &[u8]) -> Box<dyn Tr> { Box::new(s.to_vec()) }
#[inline(never)] fn e2(n: u8) -> Box<dyn Tr> { Box::new((0..n).collect::<Vec<u8>>()) }
fn main() {
    touch_alloc_zeroed();
    emit(0);
    let b0 = live_blocks(); let y0 = live_bytes();
    let a = e1(black_box(&[]));
    let b = e2(black_box(0));
    let n = a.n() + b.n();
    drop(a); drop(b);
    report(b0, y0);
    emit(n);
}
"#,
        exit: Exit::Code(0),
        stdout: "0\n0\n0\n2",
        must_match: &["0", "1", "2", "3"],
        refuse_or_match: &[],
    },
    Row {
        name: "dyn_string",
        body: r#"impl Tr for String { fn n(&self) -> usize { self.len() } }
#[inline(never)] fn make(s: &str) -> Box<dyn Tr> { Box::new(String::from(s)) }
fn main() {
    touch_alloc_zeroed();
    emit(0);
    let b0 = live_blocks(); let y0 = live_bytes();
    let b = make(black_box("hello"));
    let n = b.n();
    drop(b);
    report(b0, y0);
    emit(n);
}
"#,
        exit: Exit::Code(0),
        stdout: "0\n0\n0\n5",
        must_match: &["0", "1"],
        refuse_or_match: &["2", "3"],
    },
    Row {
        // Capacity zero: LLVM allocates nothing and frees nothing; the bridge's
        // empty `Vec`/`String` reserve a buffer and the glue frees it. Both nets
        // are zero.
        name: "dyn_cap0",
        body: r#"impl Tr for Vec<u8> { fn n(&self) -> usize { self.len() } }
impl Tr for String { fn n(&self) -> usize { self.len() + 100 } }
#[inline(never)] fn e1() -> Box<dyn Tr> { Box::new(Vec::<u8>::new()) }
#[inline(never)] fn e2() -> Box<dyn Tr> { Box::new(String::new()) }
#[inline(never)] fn e3() -> Box<dyn Tr> { Box::new(Vec::<u8>::with_capacity(0)) }
#[inline(never)] fn e4(s: &str) -> Box<dyn Tr> { Box::new(String::from(s)) }
fn main() {
    touch_alloc_zeroed();
    emit(0);
    let b0 = live_blocks(); let y0 = live_bytes();
    let a = e1(); let b = e2(); let c = e3(); let d4 = e4(black_box(""));
    let n = a.n() + b.n() + c.n() + d4.n();
    drop(a); drop(b); drop(c); drop(d4);
    report(b0, y0);
    emit(n);
}
"#,
        exit: Exit::Code(0),
        stdout: "0\n0\n0\n200",
        must_match: &["0", "1"],
        refuse_or_match: &["2", "3"],
    },
    Row {
        // `mem::forget` runs no glue: both sides leak (the counts differ by
        // design, so only "something leaked" is printed).
        name: "dyn_forget",
        body: r#"impl Tr for Vec<u8> { fn n(&self) -> usize { self.len() } }
#[inline(never)] fn make(k: u8) -> Box<dyn Tr> { Box::new(vec![1u8, 2, k]) }
fn main() {
    touch_alloc_zeroed();
    emit(0);
    let b0 = live_blocks(); let y0 = live_bytes();
    let b = make(black_box(3));
    let n = b.n();
    std::mem::forget(b);
    let leaked = live_blocks() != b0 && live_bytes() != y0;
    emit(leaked as usize);
    emit(n);
}
"#,
        exit: Exit::Code(0),
        stdout: "0\n1\n3",
        must_match: &["0", "1"],
        refuse_or_match: &[],
    },
    Row {
        name: "dyn_into_raw",
        body: r#"impl Tr for Vec<u8> { fn n(&self) -> usize { self.len() } }
#[inline(never)] fn make(k: u8) -> Box<dyn Tr> { Box::new(vec![1u8, 2, k]) }
fn main() {
    touch_alloc_zeroed();
    emit(0);
    let b0 = live_blocks(); let y0 = live_bytes();
    let b = make(black_box(3));
    let p = Box::into_raw(b);
    let b2 = unsafe { Box::from_raw(p) };
    let n = b2.n();
    drop(b2);
    report(b0, y0);
    emit(n);
}
"#,
        exit: Exit::Code(0),
        stdout: "0\n0\n0\n3",
        must_match: &["0", "1"],
        refuse_or_match: &[],
    },
    Row {
        name: "dyn_loop",
        body: r#"impl Tr for Vec<u8> { fn n(&self) -> usize { self.len() } }
impl Tr for String { fn n(&self) -> usize { self.len() * 10 } }
#[inline(never)] fn make(i: usize) -> Box<dyn Tr> { if i % 2 == 0 { Box::new(vec![7u8; i + 1]) } else { Box::new(String::from("xyz")) } }
fn main() {
    touch_alloc_zeroed();
    emit(0);
    let b0 = live_blocks(); let y0 = live_bytes();
    let mut total = 0usize;
    for i in 0..black_box(9) { let b = make(i); total += b.n(); }
    report(b0, y0);
    emit(total);
}
"#,
        exit: Exit::Code(0),
        stdout: "0\n0\n0\n145",
        must_match: &["0", "1"],
        refuse_or_match: &[],
    },
    Row {
        name: "dyn_vec_of_box",
        body: r#"impl Tr for Vec<u8> { fn n(&self) -> usize { self.len() } }
fn main() {
    touch_alloc_zeroed();
    emit(0);
    let b0 = live_blocks(); let y0 = live_bytes();
    let mut v: Vec<Box<dyn Tr>> = Vec::new();
    for i in 0..black_box(5) { v.push(Box::new(vec![1u8; i + 1])); }
    let mut total = 0;
    for b in v.iter() { total += b.n(); }
    drop(v);
    report(b0, y0);
    emit(total);
}
"#,
        exit: Exit::Code(0),
        stdout: "0\n0\n0\n15",
        must_match: &["0", "1"],
        refuse_or_match: &[],
    },
    Row {
        // `panic=abort`: the first box drops through the vtable before the
        // panic; the live one at the panic is not dropped (abort, SIGABRT).
        name: "dyn_panic",
        body: r#"impl Tr for Vec<u8> { fn n(&self) -> usize { self.len() } }
#[inline(never)] fn make(k: u8) -> Box<dyn Tr> { Box::new(vec![1u8, 2, k]) }
fn main() {
    touch_alloc_zeroed();
    emit(0);
    let a = make(black_box(3));
    let n = a.n();
    drop(a);
    emit(n);
    let b = make(black_box(4));
    if b.n() == black_box(3) { panic!("boom"); }
    emit(999);
}
"#,
        exit: Exit::Signal(6),
        stdout: "0\n3",
        must_match: &["0", "1"],
        refuse_or_match: &[],
    },
    Row {
        name: "dyn_boxbox",
        body: r#"impl Tr for Box<i64> { fn n(&self) -> usize { **self as usize } }
impl Tr for Box<Vec<u8>> { fn n(&self) -> usize { self.len() } }
#[inline(never)] fn mk1(k: i64) -> Box<dyn Tr> { Box::new(Box::new(k)) }
#[inline(never)] fn mk2(k: u8) -> Box<dyn Tr> { Box::new(Box::new(vec![k, k, k, k])) }
fn main() {
    touch_alloc_zeroed();
    emit(0);
    let b0 = live_blocks(); let y0 = live_bytes();
    let a = mk1(black_box(40));
    let b = mk2(black_box(2));
    let n = a.n() + b.n();
    drop(a); drop(b);
    report(b0, y0);
    emit(n);
}
"#,
        exit: Exit::Code(0),
        stdout: "0\n0\n0\n44",
        must_match: &["0"],
        refuse_or_match: &["2"],
    },
    Row {
        // The one slot-modeled payload left: a `BTreeMap`'s glue frees its data
        // buffer AND the 24-byte {ptr,cap,len} block its box's heap image
        // forwards to (directly, and one `Box` deeper).
        name: "dyn_btreemap_empty",
        body: r#"use std::collections::BTreeMap;
impl Tr for BTreeMap<u64, u64> { fn n(&self) -> usize { 9 } }
impl Tr for Box<BTreeMap<u64, u64>> { fn n(&self) -> usize { 90 } }
#[inline(never)] fn mk1() -> Box<dyn Tr> { Box::new(BTreeMap::<u64, u64>::new()) }
#[inline(never)] fn mk2() -> Box<dyn Tr> { Box::new(Box::new(BTreeMap::<u64, u64>::new())) }
fn main() {
    touch_alloc_zeroed();
    emit(0);
    let b0 = live_blocks(); let y0 = live_bytes();
    let a = mk1();
    let b = mk2();
    let n = a.n() + b.n();
    drop(a); drop(b);
    report(b0, y0);
    emit(n);
}
"#,
        exit: Exit::Code(0),
        stdout: "0\n0\n0\n99",
        must_match: &["0", "1", "2", "3"],
        refuse_or_match: &[],
    },
    Row {
        // `heap_image_glue` does not admit a chain holding a `HashMap`
        // (`holds_hashmap`): the bridge's -O2/-O3 empty-`HashMap` construction
        // leaks a 16-byte buffer, and admitting this glue made the -O2/-O3 cells
        // build and print `1 16` where LLVM prints `0 0`. Pinned so that it can
        // never start to build and disagree.
        name: "dyn_hashmap_empty",
        body: r#"use std::collections::HashMap;
impl Tr for HashMap<u64, u64> { fn n(&self) -> usize { 9 } }
#[inline(never)] fn make() -> Box<dyn Tr> { Box::new(HashMap::<u64, u64>::new()) }
fn main() {
    touch_alloc_zeroed();
    emit(0);
    let b0 = live_blocks(); let y0 = live_bytes();
    let b = make();
    let n = b.n();
    drop(b);
    report(b0, y0);
    emit(n);
}
"#,
        exit: Exit::Code(0),
        stdout: "0\n0\n0\n9",
        must_match: &[],
        refuse_or_match: &["0", "1", "2", "3"],
    },
    Row {
        // The same exclusion one `Box` deeper.
        name: "dyn_boxbox_hashmap_empty",
        body: r#"use std::collections::HashMap;
impl Tr for Box<HashMap<u64, u64>> { fn n(&self) -> usize { 9 } }
#[inline(never)] fn make() -> Box<dyn Tr> { Box::new(Box::new(HashMap::<u64, u64>::new())) }
fn main() {
    touch_alloc_zeroed();
    emit(0);
    let b0 = live_blocks(); let y0 = live_bytes();
    let b = make();
    let n = b.n();
    drop(b);
    report(b0, y0);
    emit(n);
}
"#,
        exit: Exit::Code(0),
        stdout: "0\n0\n0\n9",
        must_match: &[],
        refuse_or_match: &["0", "1", "2", "3"],
    },
    Row {
        // A `Vec<String>` is not slot-modeled; it refuses at construction today.
        // Pinned so that it can never start to build and disagree.
        name: "dyn_vec_string",
        body: r#"impl Tr for Vec<String> { fn n(&self) -> usize { self.len() } }
#[inline(never)] fn make() -> Box<dyn Tr> { Box::new(vec![String::from("a"), String::from("bc")]) }
fn main() {
    touch_alloc_zeroed();
    emit(0);
    let b0 = live_blocks(); let y0 = live_bytes();
    let b = make();
    let n = b.n();
    drop(b);
    report(b0, y0);
    emit(n);
}
"#,
        exit: Exit::Code(0),
        stdout: "0\n0\n0\n2",
        must_match: &[],
        refuse_or_match: &["0", "2"],
    },
    Row {
        // A concrete type with its own `Drop` AND a heap field: refused at
        // construction today ([TCG-COLLECTION-IMAGE] family). Same pin.
        name: "dyn_struct_drop",
        body: r#"static mut DROPS: usize = 0;
struct S { v: Vec<u8>, tag: u64 }
impl Drop for S { fn drop(&mut self) { unsafe { DROPS += self.tag as usize } } }
impl Tr for S { fn n(&self) -> usize { self.v.len() } }
#[inline(never)] fn make(k: u8) -> Box<dyn Tr> { Box::new(S { v: vec![k; 5], tag: 7 }) }
fn main() {
    touch_alloc_zeroed();
    emit(0);
    let b0 = live_blocks(); let y0 = live_bytes();
    let b = make(black_box(3));
    let n = b.n();
    drop(b);
    report(b0, y0);
    emit(n);
    emit(unsafe { DROPS });
}
"#,
        exit: Exit::Code(0),
        stdout: "0\n0\n0\n5\n7",
        must_match: &[],
        refuse_or_match: &["0", "2"],
    },
];

/// Compile `src` as a binary (with the bridge when `backend` is `Some`).
fn compile(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt: &str,
) -> (Output, PathBuf) {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);
    let _ = std::fs::remove_file(&bin);
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin"]);
    if let Some(dylib) = backend {
        cmd.arg(backend_arg(dylib));
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.args([
        "--target",
        TARGET,
        "-Cpanic=abort",
        "-Coverflow-checks=off",
        "-Ccodegen-units=1",
    ])
    .arg(format!("-Copt-level={opt}"))
    .arg("-o")
    .arg(&bin)
    .arg(&src_path);
    (cmd.output().expect("spawn rustc"), bin)
}

/// Run `bin` under the macOS malloc debugging switches (inert elsewhere).
fn run(bin: &Path) -> (Exit, String) {
    let out = Command::new(bin)
        .env("MallocScribble", "1")
        .env("MallocGuardEdges", "1")
        .env("MallocErrorAbort", "1")
        .output()
        .expect("run binary");
    let stdout = String::from_utf8_lossy(&out.stdout).trim().to_owned();
    if let Some(code) = out.status.code() {
        return (Exit::Code(code), stdout);
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        if let Some(signal) = out.status.signal() {
            return (Exit::Signal(signal), stdout);
        }
    }
    (Exit::Code(-1), stdout)
}

fn stderr_tail(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr)
        .lines()
        .rev()
        .take(8)
        .collect::<Vec<_>>()
        .join(" | ")
}

/// The bridge's verdict on `src` at `opt`: `Ok(None)` for a fail-closed
/// refusal (with its stderr), `Ok(Some(run))` for a binary, `Err` for any other
/// compile failure.
fn bridge_verdict(
    dir: &Path,
    dylib: &Path,
    name: &str,
    src: &str,
    opt: &str,
) -> Result<Result<(Exit, String), String>, String> {
    let (output, bin) = compile(dir, &format!("{name}_o{opt}_tcg"), src, Some(dylib), opt);
    if output.status.success() && bin.exists() {
        return Ok(Ok(run(&bin)));
    }
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    if stderr.contains("failing closed") {
        Ok(Err(stderr))
    } else {
        Err(stderr_tail(&output))
    }
}

#[test]
fn dyn_heap_glue_matches_llvm_aarch64() {
    if skip("dyn_heap_glue_matches_llvm_aarch64") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("diff");
    let mut failures = Vec::new();
    let mut matched = 0usize;
    let mut refused = 0usize;
    let mut cells = 0usize;
    let mut must_cells = 0usize;
    for row in ROWS {
        let src = format!("{PRELUDE}{}", row.body);
        for opt in row.must_match.iter().chain(row.refuse_or_match.iter()) {
            let (out, bin) = compile(&dir, &format!("{}_o{opt}_llvm", row.name), &src, None, opt);
            assert!(
                out.status.success(),
                "LLVM compile of `{}` failed at -O{opt}: <<<{}>>>",
                row.name,
                String::from_utf8_lossy(&out.stderr)
            );
            let oracle = run(&bin);
            assert_eq!(
                (&oracle.0, oracle.1.as_str()),
                (&row.exit, row.stdout),
                "LLVM oracle for `{}` at -O{opt}",
                row.name
            );
            let must = row.must_match.contains(opt);
            cells += 1;
            must_cells += usize::from(must);
            match bridge_verdict(&dir, &dylib, row.name, &src, opt) {
                Ok(Ok(ran)) if ran == oracle => matched += 1,
                Ok(Ok(ran)) => failures.push(format!(
                    "-O{opt} `{}`: trust-cg binary DISAGREES with LLVM: {ran:?} vs {oracle:?} \
                     (stdout lines 2-3 are net live heap blocks/bytes; nonzero = leak or \
                     wrong-size free)",
                    row.name
                )),
                Ok(Err(_)) if !must => refused += 1,
                Ok(Err(stderr)) => failures.push(format!(
                    "-O{opt} `{}`: trust-cg REFUSED a program whose vtable drop glue now \
                     lowers (heap_image_glue) — a capability regression: <<<{}>>>",
                    row.name,
                    stderr
                        .lines()
                        .filter(|l| l.contains(" - "))
                        .take(3)
                        .collect::<Vec<_>>()
                        .join(" | ")
                )),
                Err(tail) => failures.push(format!(
                    "-O{opt} `{}`: trust-cg failed, but not with a fail-closed verdict: \
                     <<<{tail}>>>",
                    row.name
                )),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "{} dyn heap-glue cell(s) failed ({matched} matched):\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    assert!(
        matched > 0,
        "no cell built through the bridge — nothing was compared"
    );
    assert_eq!(
        matched + refused,
        cells,
        "every dyn heap-glue cell must close"
    );
    eprintln!(
        "DYN_HEAP_GLUE cells={cells} must_match={must_cells} matched={matched} refused={refused}"
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// A `Vec` / `String` vtable built from a BORROW (`&`, `&mut`, `*mut`). Its drop
/// slot frees only the data buffer the rustc-layout header at the data pointer
/// names, which is right whoever owns that header, so these must build and
/// match LLVM as they do on 16a86a97b — a [TCG-HEAP-IMAGE-*] refusal of any
/// cell here is the regression this test exists for. `dyn_raw_dyn_drop` runs the
/// drop slot through the borrowed pointer itself; it refuses today for reasons
/// outside the glue (`Vec::forget` at -O0/-O1, a `dyn` drop at -O2/-O3), so it
/// may refuse, but never by a heap-image check and never build and disagree.
const BORROWED_VEC_STRING: &[Row] = &[
    Row {
        name: "dyn_ref_vec",
        body: r#"impl Tr for Vec<u8> { fn n(&self) -> usize { self.len() } }
#[inline(never)] fn show(v: &Vec<u8>) -> usize { let d: &dyn Tr = v; d.n() }
fn main() { touch_alloc_zeroed(); emit(0); let v = vec![1u8, 2, black_box(3)]; emit(show(&v)); }
"#,
        exit: Exit::Code(0),
        stdout: "0\n3",
        must_match: &["0", "1", "2", "3"],
        refuse_or_match: &[],
    },
    Row {
        name: "dyn_ref_string",
        body: r#"impl Tr for String { fn n(&self) -> usize { self.len() } }
#[inline(never)] fn show(v: &String) -> usize { let d: &dyn Tr = v; d.n() }
fn main() { touch_alloc_zeroed(); emit(0); let v = String::from(black_box("abcd")); emit(show(&v)); }
"#,
        exit: Exit::Code(0),
        stdout: "0\n4",
        must_match: &["0", "1", "2", "3"],
        refuse_or_match: &[],
    },
    Row {
        // Borrowed and owned vtables for the same types in one program (one
        // vtable per (type, trait) per module), under the heap ledger: all three
        // values are dropped at the end of the block, before the report.
        name: "dyn_ref_and_box_mixed",
        body: r#"impl Tr for Vec<u8> { fn n(&self) -> usize { self.len() } }
impl Tr for String { fn n(&self) -> usize { self.len() + 10 } }
#[inline(never)] fn show(d: &dyn Tr) -> usize { d.n() }
#[inline(never)] fn make(k: u8) -> Box<dyn Tr> { Box::new(vec![k; 4]) }
fn main() {
    touch_alloc_zeroed();
    emit(0);
    let b0 = live_blocks(); let y0 = live_bytes();
    let n = {
        let v = vec![1u8, 2, black_box(3)];
        let s = String::from(black_box("ab"));
        let b = make(black_box(7));
        show(&v) + show(&s) + show(&*b)
    };
    report(b0, y0);
    emit(n);
}
"#,
        exit: Exit::Code(0),
        stdout: "0\n0\n0\n19",
        must_match: &["0", "1", "2", "3"],
        refuse_or_match: &[],
    },
    Row {
        name: "dyn_mut_ref_vec",
        body: r#"trait Tm { fn bump(&mut self) -> usize; }
impl Tm for Vec<u8> { fn bump(&mut self) -> usize { self.len() + 1 } }
#[inline(never)] fn go(v: &mut Vec<u8>) -> usize { let d: &mut dyn Tm = v; d.bump() }
fn main() { touch_alloc_zeroed(); emit(0); let mut v = vec![1u8, 2, black_box(3)]; emit(go(&mut v)); }
"#,
        exit: Exit::Code(0),
        stdout: "0\n4",
        must_match: &["0", "1", "2", "3"],
        refuse_or_match: &[],
    },
    Row {
        name: "dyn_raw_dyn_drop",
        body: r#"impl Tr for Vec<u8> { fn n(&self) -> usize { self.len() } }
#[inline(never)] fn kill(v: &mut Vec<u8>) { let p: *mut dyn Tr = v; unsafe { std::ptr::drop_in_place(p) } }
fn main() { touch_alloc_zeroed(); emit(0); let mut v = vec![1u8, 2, black_box(3)]; let n = v.len(); kill(&mut v); std::mem::forget(v); emit(n); }
"#,
        exit: Exit::Code(0),
        stdout: "0\n3",
        must_match: &[],
        refuse_or_match: &["0", "1", "2", "3"],
    },
];

#[test]
fn dyn_heap_glue_borrowed_vec_string_vtable_matches_llvm_aarch64() {
    if skip("dyn_heap_glue_borrowed_vec_string_vtable_matches_llvm_aarch64") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("borrowed_vec_string");
    let mut failures = Vec::new();
    let (mut cells, mut must_cells, mut matched, mut refused) = (0usize, 0usize, 0usize, 0usize);
    for row in BORROWED_VEC_STRING {
        let src = format!("{PRELUDE}{}", row.body);
        for opt in row.must_match.iter().chain(row.refuse_or_match.iter()) {
            let (out, bin) = compile(&dir, &format!("{}_o{opt}_llvm", row.name), &src, None, opt);
            assert!(
                out.status.success(),
                "LLVM compile of `{}` failed at -O{opt}: <<<{}>>>",
                row.name,
                String::from_utf8_lossy(&out.stderr)
            );
            let oracle = run(&bin);
            assert_eq!(
                (&oracle.0, oracle.1.as_str()),
                (&row.exit, row.stdout),
                "LLVM oracle for `{}` at -O{opt}",
                row.name
            );
            let must = row.must_match.contains(opt);
            cells += 1;
            must_cells += usize::from(must);
            match bridge_verdict(&dir, &dylib, row.name, &src, opt) {
                Ok(Ok(ran)) if ran == oracle => matched += 1,
                Ok(Ok(ran)) => failures.push(format!(
                    "-O{opt} `{}`: trust-cg binary DISAGREES with LLVM: {ran:?} vs {oracle:?}",
                    row.name
                )),
                Ok(Err(stderr)) if stderr.contains("[TCG-HEAP-IMAGE-") => failures.push(format!(
                    "-O{opt} `{}`: a borrowed Vec/String vtable was refused by a heap-image \
                     check, but its glue frees only the data buffer the rustc-layout header \
                     names and is valid from any origin: <<<{}>>>",
                    row.name,
                    stderr
                        .lines()
                        .filter(|l| l.contains(" - "))
                        .take(2)
                        .collect::<Vec<_>>()
                        .join(" | ")
                )),
                Ok(Err(_)) if !must => refused += 1,
                Ok(Err(stderr)) => failures.push(format!(
                    "-O{opt} `{}`: trust-cg REFUSED a borrowed Vec/String vtable program \
                     that must build and match: <<<{}>>>",
                    row.name,
                    stderr
                        .lines()
                        .filter(|l| l.contains(" - "))
                        .take(2)
                        .collect::<Vec<_>>()
                        .join(" | ")
                )),
                Err(tail) => failures.push(format!(
                    "-O{opt} `{}`: compile failed without a fail-closed verdict: <<<{tail}>>>",
                    row.name
                )),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "{} borrowed Vec/String cell(s) failed ({matched} matched):\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    assert_eq!(
        matched + refused,
        cells,
        "every borrowed Vec/String cell must close"
    );
    assert!(
        matched >= must_cells,
        "every must-match cell must have matched"
    );
    eprintln!(
        "DYN_HEAP_GLUE_BORROWED_VEC_STRING cells={cells} must_match={must_cells} \
         matched={matched} refused={refused}"
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// `(name, body, opts, LLVM's stdout, required refusal)`: a map vtable built
/// from a BORROW. A `BTreeMap`'s glue frees a `Box<C>` heap image's slot block;
/// called through this pointer it would free a frame address, so the vtable
/// refuses ([TCG-HEAP-IMAGE-VTABLE]). A `HashMap`'s glue is not lowered at all
/// (`holds_hashmap`), so its borrowed vtable refuses on the unlowerable glue
/// instead; either way the program must FAIL CLOSED, never build.
// BTreeMap's origin control below uses a real LLVM-created incoming address.
// The synthetic in-program map has no stable reference storage on Linux and
// would refuse earlier, failing to exercise the vtable-origin protection.
const BORROWED_MAP: [(&str, &str, &[&str], &str, &str); 1] = [(
    "dyn_ref_hashmap",
    r#"use std::collections::HashMap;
impl Tr for HashMap<u64, u64> { fn n(&self) -> usize { 7 } }
#[inline(never)] fn show(m: &HashMap<u64, u64>) -> usize { let d: &dyn Tr = m; d.n() }
fn main() { touch_alloc_zeroed(); emit(0); let m = HashMap::<u64, u64>::new(); emit(show(&m)); }
"#,
    &["0", "1", "2", "3"],
    "0\n7",
    "failing closed",
)];

#[test]
fn dyn_heap_glue_borrowed_map_vtable_fails_closed_aarch64() {
    if skip("dyn_heap_glue_borrowed_map_vtable_fails_closed_aarch64") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("borrowed_map");
    let mut failures = Vec::new();
    let mut refused = 0usize;
    let real_map_cells = real_map_dyn_origin::qualify(
        &dir,
        &dylib,
        false,
        &["0", "1", "2", "3"],
        &toolchain_support::backend_knobs_arg(&["no-proof-certs"]),
    );
    let mut heap_image_vtable = real_map_cells;
    refused += real_map_cells;
    for (name, body, opts, expected, required) in BORROWED_MAP {
        let src = format!("{PRELUDE}{body}");
        for opt in opts {
            let (out, bin) = compile(&dir, &format!("{name}_o{opt}_llvm"), &src, None, opt);
            assert!(
                out.status.success(),
                "LLVM compile of `{name}` failed at -O{opt}"
            );
            assert_eq!(
                run(&bin),
                (Exit::Code(0), expected.to_owned()),
                "LLVM oracle `{name}`"
            );
            match bridge_verdict(&dir, &dylib, name, &src, opt) {
                Ok(Err(stderr)) if stderr.contains(required) => {
                    refused += 1;
                    heap_image_vtable += usize::from(stderr.contains("[TCG-HEAP-IMAGE-VTABLE]"));
                }
                Ok(Err(stderr)) => failures.push(format!(
                    "-O{opt} `{name}`: refused, but not by {required}: <<<{}>>>",
                    stderr
                        .lines()
                        .filter(|l| l.contains(" - "))
                        .take(2)
                        .collect::<Vec<_>>()
                        .join(" | ")
                )),
                Ok(Ok(ran)) => failures.push(format!(
                    "-O{opt} `{name}`: built a borrowed-origin map vtable (ran: {ran:?}; LLVM: \
                     {expected:?}) — it must FAIL CLOSED"
                )),
                Err(tail) => failures.push(format!(
                    "-O{opt} `{name}`: compile failed without a fail-closed verdict: <<<{tail}>>>"
                )),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "{} row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    assert_eq!(
        refused, 8,
        "all four real BTreeMap and four HashMap negative cells must close"
    );
    assert_eq!(
        heap_image_vtable, 4,
        "every real BTreeMap borrow must reach its origin boundary"
    );
    eprintln!("DYN_HEAP_GLUE_BORROWED_MAP refused={refused} heap_image_vtable={heap_image_vtable}");
    positive_evidence::record(
        positive_evidence::Evidence::ExpectedRefusal,
        positive_evidence::Certs::Off,
    );
}

/// A genuine Box<Map> from an independently LLVM-built provider contains
/// rustc's real map image. Its owning type alone cannot authorize the bridge's
/// private modeled heap image; require the same exact origin refusal as a borrow.
#[test]
fn dyn_heap_glue_real_owned_map_origin_fails_closed_aarch64() {
    if skip("dyn_heap_glue_real_owned_map_origin_fails_closed_aarch64") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("real_owned_map");
    let refused = real_map_dyn_origin::qualify(
        &dir,
        &dylib,
        true,
        &["0", "1", "2", "3"],
        &toolchain_support::backend_knobs_arg(&["no-proof-certs"]),
    );
    assert_eq!(refused, 4, "all real owning-map origin controls must close");
    eprintln!("DYN_HEAP_GLUE_REAL_OWNED_MAP refused={refused}");
    positive_evidence::record(
        positive_evidence::Evidence::ExpectedRefusal,
        positive_evidence::Certs::Off,
    );
}

/// A `Box<dyn Get>` owning a two-level box chain, in a STATICLIB: the vtable's
/// drop slot is `drop_glue::<Box<Box<i64>>>`. Measured before this lane (same
/// host): rustc's body for it did not lower, a library takes the trap-stub
/// route, and the linked program died with SIGTRAP (exit 133) at the drop.
const STATICLIB_CHAIN: &str = "\
pub trait Get { fn get(&self) -> i64; }
impl Get for Box<Box<i64>> { fn get(&self) -> i64 { ***self } }
#[inline(never)] fn make(n: i64) -> Box<dyn Get> { Box::new(Box::new(Box::new(n))) }
#[no_mangle] pub extern \"C\" fn tcg_lib_entry(n: i64) -> i64 { let b = make(n); let k = b.get(); drop(b); k + 1 }
";

/// The same shape six boxes deep, past `boxed_payload_drop_recursively_lowerable`'s
/// depth cap. Measured before this lane: SIGTRAP at the drop; then refused at
/// compile time ([TCG-HEAP-GLUE-STUB-REACHABLE]) while its glue did not lower.
/// Since L06-P8 each level's glue calls the next level's rustc drop glue on the
/// box pointer and frees it (`box_payload_drop`), so it lowers, links and frees
/// all seven allocations.
const STATICLIB_DEEP: &str = "\
pub trait Get { fn get(&self) -> i64; }
type B6 = Box<Box<Box<Box<Box<Box<i64>>>>>>;
impl Get for B6 { fn get(&self) -> i64 { 7 } }
#[inline(never)] fn make(n: i64) -> Box<dyn Get> { let b: B6 = Box::new(Box::new(Box::new(Box::new(Box::new(Box::new(n)))))); Box::new(b) }
#[no_mangle] pub extern \"C\" fn tcg_lib_entry(n: i64) -> i64 { let b = make(n); let k = b.get(); drop(b); k + 1 }
";

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn compile_staticlib_objects(dir: &Path, dylib: &Path, src: &str) -> Output {
    let src_path = dir.join("lib.rs");
    std::fs::write(&src_path, src).expect("write staticlib source");
    toolchain_support::rustc_command()
        .args(["--crate-type", "staticlib"])
        .arg(backend_arg(dylib))
        .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
        .args([
            "--target",
            TARGET,
            "-Cpanic=abort",
            "-Copt-level=0",
            "--emit=obj",
        ])
        .arg("-o")
        .arg(dir.join("lib"))
        .arg(&src_path)
        .output()
        .expect("spawn trustc for the staticlib")
}

/// `(defined, undefined)` external symbols of one object, from `nm`.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn object_symbols(object: &Path) -> (Vec<String>, Vec<String>) {
    let listing = Command::new("nm").arg(object).output().expect("nm");
    let mut defined = Vec::new();
    let mut undefined = Vec::new();
    for line in String::from_utf8_lossy(&listing.stdout).lines() {
        let fields: Vec<&str> = line.split_whitespace().collect();
        match fields.as_slice() {
            ["U", name] => undefined.push((*name).to_owned()),
            [_, kind, name] if kind.chars().all(|c| c.is_ascii_uppercase()) => {
                defined.push((*name).to_owned())
            }
            _ => {}
        }
    }
    (defined, undefined)
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn staticlib_dyn_box_chain_glue_aarch64() {
    if skip("staticlib_dyn_box_chain_glue_aarch64") {
        return;
    }
    // The object closure and the C driver need the host's `nm` and `cc`.
    darwin_native_prerequisites::require("staticlib_dyn_box_chain_glue_aarch64", &["nm", "cc"]);
    let dylib = backend_artifact_support::current_test_backend();

    // 1. The deep chain: six levels of rustc box glue, each freeing its box
    //    (seven allocations with the outer `Box<dyn Get>`).
    let deep = workdir("slib_deep");
    let deep_line = link_and_run_staticlib(&deep, &dylib, STATICLIB_DEEP);
    assert_eq!(
        deep_line, "r=8 allocs=7 deallocs=7 live=0",
        "the six-box chain's drop must free the outer box and every level, nothing twice"
    );
    let _ = std::fs::remove_dir_all(&deep);

    // 2. The two-level chain: the glue lowers, links into a C driver and frees
    //    exactly what was allocated.
    let dir = workdir("slib_chain");
    let line = link_and_run_staticlib(&dir, &dylib, STATICLIB_CHAIN);
    assert_eq!(
        line, "r=42 allocs=3 deallocs=3 live=0",
        "the staticlib's `Box<dyn Get>` drop must free the outer box, both inner boxes, \
         nothing twice (a trap-stubbed glue dies with SIGTRAP, signal 5)"
    );
    let _ = std::fs::remove_dir_all(&dir);
    eprintln!("DYN_HEAP_GLUE_STATICLIB deep_chain: {deep_line} box_chain: {line}");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// Compile `src` as a bridge staticlib's objects in `dir`, link the object
/// closure of `tcg_lib_entry` into a C driver that stands in for libstd's
/// allocator, run it, and return its one output line.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn link_and_run_staticlib(dir: &Path, dylib: &Path, src: &str) -> String {
    let output = compile_staticlib_objects(dir, dylib, src);
    assert!(
        output.status.success(),
        "bridge failed to compile the staticlib: <<<{}>>>",
        String::from_utf8_lossy(&output.stderr)
    );
    let objects: Vec<PathBuf> = std::fs::read_dir(dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    let symbols: Vec<(PathBuf, Vec<String>, Vec<String>)> = objects
        .iter()
        .map(|o| {
            let (d, u) = object_symbols(o);
            (o.clone(), d, u)
        })
        .collect();
    // The object closure of the entry point, by DEFINED symbol.
    let mut selected: Vec<usize> = Vec::new();
    let mut queue: Vec<usize> = symbols
        .iter()
        .position(|(_, d, _)| d.iter().any(|s| s == "_tcg_lib_entry"))
        .into_iter()
        .collect();
    assert!(!queue.is_empty(), "no object defines `tcg_lib_entry`");
    while let Some(index) = queue.pop() {
        if selected.contains(&index) {
            continue;
        }
        selected.push(index);
        for wanted in &symbols[index].2 {
            if let Some(provider) = symbols.iter().position(|(_, d, _)| d.contains(wanted)) {
                if !selected.contains(&provider) {
                    queue.push(provider);
                }
            }
        }
    }
    let selected_objects: Vec<PathBuf> = selected.iter().map(|&i| symbols[i].0.clone()).collect();
    let undefined: Vec<&String> = selected.iter().flat_map(|&i| symbols[i].2.iter()).collect();
    let rdl = |suffix: &str| -> String {
        undefined
            .iter()
            .find(|s| s.ends_with(suffix))
            .map(|s| (*s).clone())
            .unwrap_or_else(|| format!("_unused{suffix}"))
    };
    // The driver stands in for libstd's allocator objects: the `__rdl_*`
    // entry points the shim forwards to, and `__rust_alloc_error_handler`,
    // which every checked allocation's null branch calls (libstd defines it in
    // a real link, beside the `__rdl_*` entries). It is never reached here (no
    // allocation fails); it aborts if it were.
    let driver = format!(
        "#include <stdio.h>\n#include <stdlib.h>\n\
         extern long tcg_lib_entry(long x);\n\
         static long allocs = 0, deallocs = 0, live = 0;\n\
         void *h_alloc(unsigned long s, unsigned long a) __asm__(\"{}\");\n\
         void *h_alloc(unsigned long s, unsigned long a) {{ (void)a; allocs++; live += s; return malloc(s); }}\n\
         void h_dealloc(void *p, unsigned long s, unsigned long a) __asm__(\"{}\");\n\
         void h_dealloc(void *p, unsigned long s, unsigned long a) {{ (void)a; deallocs++; live -= s; free(p); }}\n\
         void *h_realloc(void *p, unsigned long o, unsigned long a, unsigned long n) __asm__(\"{}\");\n\
         void *h_realloc(void *p, unsigned long o, unsigned long a, unsigned long n) {{ (void)a; live += n - o; return realloc(p, n); }}\n\
         void *h_zeroed(unsigned long s, unsigned long a) __asm__(\"{}\");\n\
         void *h_zeroed(unsigned long s, unsigned long a) {{ (void)a; allocs++; live += s; return calloc(1, s); }}\n\
         void h_oom(unsigned long s, unsigned long a) __asm__(\"{}\");\n\
         void h_oom(unsigned long s, unsigned long a) {{ (void)s; (void)a; abort(); }}\n\
         int main(void) {{ long r = tcg_lib_entry(41);\n\
         printf(\"r=%ld allocs=%ld deallocs=%ld live=%ld\\n\", r, allocs, deallocs, live); return 0; }}\n",
        rdl("_rdl_alloc"),
        rdl("_rdl_dealloc"),
        rdl("_rdl_realloc"),
        rdl("_rdl_alloc_zeroed"),
        rdl("_rust_alloc_error_handler"),
    );
    let driver_path = dir.join("driver.c");
    std::fs::write(&driver_path, driver).expect("write driver");
    let bin = dir.join("prog");
    let link = Command::new("cc")
        .arg("-o")
        .arg(&bin)
        .arg(&driver_path)
        .args(&selected_objects)
        .arg(toolchain_support::write_abort_stubs(dir, &selected_objects))
        .output()
        .expect("cc link");
    assert!(
        link.status.success(),
        "link failed: <<<{}>>>",
        String::from_utf8_lossy(&link.stderr)
    );
    let (exit, stdout) = run(&bin);
    assert_eq!(exit, Exit::Code(0), "the staticlib driver failed: {stdout}");
    stdout
}
