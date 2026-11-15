#![cfg(all(target_arch = "x86_64", target_os = "linux"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: three x86-64 Linux capabilities the Trust/Clean slices
// needed, each compiled by the bridge and RUN at -O0..-O3 and compared with
// rustc's LLVM backend at the same level on stdout bytes, stderr bytes (thread
// ids normalized) and exit status.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// 1. `print!` std fallback (`print_falls_back_to_std`). A `_print`/`_eprint`
//    call whose `fmt::Arguments` the interception does not synthesize (any
//    trait other than `Display`, flags, width, precision, positional or
//    dynamic arguments, a value read through a field of a local) is lowered
//    as the real std call: its `Arguments` chain is not seeded dead, and
//    std's `core::fmt` formats it. Before, such a call refused as
//    `[TCG-FMT-DECLINED]`, `[TCG-FMT-ARGPLACE]` or "unsupported placeholder".
// 2. `Box<T>` whose payload has drop glue, under `panic=abort` on x86-64
//    Linux (`box_payload_drop::abort_payload_lane`): rustc's `drop_glue::<T>`
//    on the box pointer, then the free. Under `panic=unwind` the box's nested
//    cleanup is still Darwin-qualified only, so the refusal stays (pinned).
// 3. A whole tagless aggregate stored into an element of a SIZED array behind
//    a reference (`(*r)[i] = S { .. }`, `lower_deref_aggregate_memory_store`).
//    A slice element (`&mut [S]`) keeps its previous route (pinned: match or
//    named refusal, never a wrong value).
//
// EVIDENCE BOUNDARY: a differential test on fixed inputs, proofs-off lane
// (`-Ztrust-verify=off`, `no-proof-certs`); not proof evidence.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = host_target_support::X86_64_TARGET;
const OPT_LEVELS: [&str; 4] = ["0", "1", "2", "3"];

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_slicecap_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

#[derive(Debug, PartialEq, Eq)]
struct RunResult {
    stdout: String,
    stderr: String,
    code: Option<i32>,
    signal: Option<i32>,
}

fn normalize_thread_ids(text: &str) -> String {
    // `thread 'main' (12345) panicked` -> `thread 'main' (TID) panicked`.
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(pos) = rest.find("' (") {
        let (head, tail) = rest.split_at(pos + 3);
        out.push_str(head);
        let digits = tail.chars().take_while(|c| c.is_ascii_digit()).count();
        if digits > 0 && tail[digits..].starts_with(')') {
            out.push_str("TID");
            rest = &tail[digits..];
        } else {
            rest = tail;
        }
    }
    out.push_str(rest);
    out
}

fn run_bin(bin: &Path) -> RunResult {
    use std::os::unix::process::ExitStatusExt;
    let out = Command::new(bin).output().expect("run binary");
    RunResult {
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: normalize_thread_ids(&String::from_utf8_lossy(&out.stderr)),
        code: out.status.code(),
        signal: out.status.signal(),
    }
}

enum Outcome {
    Ran(RunResult),
    Refused(String),
}

fn compile(
    dir: &Path,
    dylib: Option<&Path>,
    stem: &str,
    src: &str,
    opt: &str,
    panic: &str,
) -> Outcome {
    let src_path = dir.join(format!("{stem}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let arm = if dylib.is_some() { "cg" } else { "llvm" };
    let bin = dir.join(format!("{stem}_{arm}_O{opt}_{panic}"));
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "--target", TARGET])
        .arg(format!("-Cpanic={panic}"))
        .arg(format!("-Copt-level={opt}"))
        .args(["-Coverflow-checks=off", "-Ccodegen-units=1", "-Awarnings"]);
    if let Some(dylib) = dylib {
        let mut backend = std::ffi::OsString::from("-Zcodegen-backend=");
        backend.push(dylib);
        cmd.arg(backend)
            .arg("-Ztrust-ir-cg-args=no-proof-certs")
            .arg("-Ztrust-ir-cg-args=refine-solver=0");
    }
    let output = cmd
        .arg("-o")
        .arg(&bin)
        .arg(&src_path)
        .output()
        .expect("spawn rustc");
    if !output.status.success() {
        return Outcome::Refused(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Outcome::Ran(run_bin(&bin))
}

fn llvm(dir: &Path, stem: &str, src: &str, opt: &str, panic: &str) -> RunResult {
    match compile(dir, None, stem, src, opt, panic) {
        Outcome::Ran(result) => result,
        Outcome::Refused(stderr) => panic!("LLVM failed to compile `{stem}`: {stderr}"),
    }
}

/// Every case must compile under the bridge and equal LLVM at every level.
fn require_match(dir: &Path, dylib: &Path, cases: &[(&str, &str)]) {
    for (stem, src) in cases {
        for opt in OPT_LEVELS {
            let want = llvm(dir, stem, src, opt, "abort");
            match compile(dir, Some(dylib), stem, src, opt, "abort") {
                Outcome::Ran(got) => {
                    assert_eq!(
                        got, want,
                        "`{stem}` at -O{opt}: bridge output differs from LLVM"
                    )
                }
                Outcome::Refused(stderr) => {
                    panic!("`{stem}` refused at -O{opt}, expected to compile: {stderr}")
                }
            }
        }
    }
}

fn skip() -> bool {
    if !toolchain_support::target_std_available(TARGET) {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return true;
    }
    false
}

#[test]
fn print_shapes_outside_the_synthesis_run_through_std_and_match_llvm() {
    if skip() {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("print");
    let cases: &[(&str, &str)] = &[
        (
            "hex_alt_zero",
            r#"use std::hint::black_box as bb;
fn main() {
    let v = bb(0xABu32); let n = bb(-42i32);
    println!("[{:#010X}] [{:#x}] [{:x}] [{:X}] [{:08x}] [{:#06x}]", v, v, n, n, v, bb(0u8));
    println!("{:#x} {:x} {} {}", bb(u128::MAX), bb(-1i128), bb(i128::MIN), bb(u64::MAX));
    println!("{:o} {:b} {:#b} {:e}", v, v, bb(5u8), bb(1234.5f64));
}"#,
        ),
        (
            "width_align_sign",
            r#"use std::hint::black_box as bb;
fn main() {
    let n = bb(-42i32); let v = bb(171u32); let w = bb(7usize);
    println!("[{:5}] [{:<5}] [{:^5}] [{:>5}] [{:*^7}] [{:+}] [{:+05}] [{:05}]", n, n, n, n, n, v, n, n);
    println!("[{:w$}] [{:>1$}] [{:.3}] [{:.*}] [{:10.3}]", v, w, n, 2, bb(1.5f64), bb(2.25f64));
    println!("[{:5}] [{:<5}] [{:.1}] [{:>4}] [{:^6}] [{:é>5}]", bb("ab"), bb("é"), bb("xyz"), bb('c'), bb(false), v);
    println!("{0} {1} {0} {name}", v, n, name = bb("nm"));
    eprintln!("err {:?} {:>3}", bb(Some(1u8)), bb(2u8));
}"#,
        ),
        (
            "debug_derive",
            r#"use std::hint::black_box as bb;
#[derive(Debug, Clone, Copy)] struct TyId(u32);
#[derive(Debug, Clone, Copy)] enum Shape { SliceLen { elem: TyId }, StrLen, VTable { trait_id: u32 } }
#[derive(Debug)] struct Unit;
#[derive(Debug)] struct Zst<T>(std::marker::PhantomData<T>);
#[derive(Debug)] struct Gen<T: std::fmt::Debug> { v: T, w: Option<T> }
#[derive(Debug)] #[repr(align(8))] struct Al { a: u8, b: u64 }
#[derive(Debug)] struct Nest { inner: Gen<i16>, al: Al, t: (u8, char, bool) }
fn main() {
    let a = bb(Shape::SliceLen { elem: TyId(7) }); let b = bb(Shape::StrLen); let c = bb(Shape::VTable { trait_id: 9 });
    println!("{:?} {:?} {:?}", a, b, c);
    println!("{:#?}", a);
    println!("{:?} {:?}", Unit, Zst::<u64>(std::marker::PhantomData));
    let n = Nest { inner: Gen { v: bb(5i16), w: Some(bb(6)) }, al: Al { a: bb(1), b: bb(u64::MAX) }, t: (bb(2), bb('é'), bb(true)) };
    println!("{:?}", n);
    let r: Option<&u32> = bb(Some(&42)); let z = bb(std::num::NonZeroU32::new(3));
    println!("{:?} {:?} {:?}", r, z, bb(None::<std::num::NonZeroU8>));
    println!("{:?} {:?} {:?} {:x?}", bb("a\"b\n"), bb('\''), bb([1u8, 2, 3]), bb(255u8));
}"#,
        ),
        (
            "field_of_local",
            r#"use std::hint::black_box as bb;
struct DecOut { tag: u32, a: u64, inner: (u8, i16), n: Nest }
struct Nest { x: u64, y: bool }
fn fill(o: &mut DecOut, k: u32) { o.tag = k * 3; o.a = (k as u64) << 40; o.inner = (k as u8, -(k as i16)); o.n = Nest { x: k as u64 + 1, y: k % 2 == 0 }; }
fn main() {
    let mut o = DecOut { tag: 0, a: 0, inner: (0, 0), n: Nest { x: 0, y: false } };
    fill(&mut o, bb(5));
    println!("{}", o.tag); println!("lo={:#x} len={}", o.a, o.inner.0);
    println!("{} {} {}", o.inner.1, o.n.x, o.n.y);
    for i in 0..bb(3u32) { let mut q = DecOut { tag: i, a: 0, inner: (0, 0), n: Nest { x: 0, y: true } }; if i == 1 { q.tag = 77; } println!("{} {}", q.tag, q.n.y); }
}"#,
        ),
        // The synthesized subset is unchanged and still compiles.
        (
            "plain_display",
            r#"fn main() { let x = std::hint::black_box(-7i64); println!("x={} {} {}", x, std::hint::black_box("s"), std::hint::black_box('c')); }"#,
        ),
    ];
    require_match(&dir, &dylib, cases);
    let _ = std::fs::remove_dir_all(&dir);
}

const BOX_DROP_ORDER: &str = r#"use std::hint::black_box as bb;
static mut LOG: [u32; 64] = [0; 64]; static mut N: usize = 0;
fn log(v: u32) { unsafe { LOG[N] = v; N += 1; } }
struct G(u32); impl Drop for G { fn drop(&mut self) { log(self.0); } }
struct Z; impl Drop for Z { fn drop(&mut self) { log(999); } }
enum L { Nil, Cons(G, Box<L>) }
struct Pair { a: G, b: Box<G>, c: (G, Box<Z>) }
#[repr(align(16))] struct Al { g: G, x: u64 }
struct Gen<T> { v: T, g: G }
fn main() {
    { let mut l = L::Nil; for i in 0..bb(5u32) { l = L::Cons(G(i), Box::new(l)); } let _ = bb(&l); }
    { let p = Box::new(Pair { a: G(10), b: Box::new(G(11)), c: (G(12), Box::new(Z)) }); let _ = bb(&p); }
    { let a = Box::new(Al { g: G(20), x: bb(7) }); let _ = bb(&a); }
    { let z = Box::new(Z); let _ = bb(&z); let o: Option<Box<G>> = bb(Some(Box::new(G(30)))); drop(o); }
    { let g = Box::new(Gen { v: Box::new(G(40)), g: G(41) }); let _ = bb(&g); let gg = Box::new(Gen { v: (), g: G(42) }); let _ = bb(&gg); }
    { let n: Option<Box<Box<G>>> = bb(Some(Box::new(Box::new(G(50))))); let _ = bb(&n); }
    let n = unsafe { N }; for i in 0..n { print!("{} ", unsafe { LOG[i] }); } println!();
}"#;

#[test]
fn box_payload_drop_glue_matches_llvm_under_abort() {
    if skip() {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("boxdrop");
    let cases: &[(&str, &str)] = &[
        ("drop_order", BOX_DROP_ORDER),
        (
            "recursive_tree",
            r#"use std::hint::black_box as bb;
static mut DROPS: u64 = 0;
struct C(u64); impl Drop for C { fn drop(&mut self) { unsafe { DROPS = DROPS.wrapping_mul(31).wrapping_add(self.0); } } }
enum T { Leaf(C), Node(Box<T>, Box<T>) }
fn mk(d: u32, s: u64) -> T { if d == 0 { T::Leaf(C(s)) } else { T::Node(Box::new(mk(d - 1, s * 2)), Box::new(mk(d - 1, s * 2 + 1))) } }
fn main() { for r in 0..bb(30u32) { let t = Box::new(mk(10, r as u64)); bb(&t); } println!("{}", unsafe { DROPS }); }"#,
        ),
    ];
    require_match(&dir, &dylib, cases);
    let _ = std::fs::remove_dir_all(&dir);
}

/// `panic=unwind` keeps the Darwin-only nested cleanup: the payload glue lane
/// is not admitted, and the drop refuses by name (never a leak or a skipped
/// destructor). Pins `abort_payload_lane`'s `panic_is_abort` condition.
#[test]
fn box_payload_drop_glue_still_refuses_under_unwind() {
    if skip() {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("boxdrop_unwind");
    for opt in OPT_LEVELS {
        match compile(
            &dir,
            Some(&dylib),
            "drop_order",
            BOX_DROP_ORDER,
            opt,
            "unwind",
        ) {
            Outcome::Refused(stderr) => assert!(
                stderr.contains("recursive drop glue not lowered"),
                "-O{opt}: expected the named Box payload-drop refusal, got: {stderr}"
            ),
            Outcome::Ran(got) => {
                let want = llvm(&dir, "drop_order", BOX_DROP_ORDER, opt, "unwind");
                panic!(
                    "-O{opt}: compiled under unwind (outside the qualified lane): {got:?} vs {want:?}"
                )
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

const ELEMENT_STORE_PRELUDE: &str = r#"use std::hint::black_box as bb;
#[derive(Clone, Copy)] struct LR { start: u32, end: u32 }
#[derive(Clone, Copy)] struct Mixed { a: u8, b: u64, c: i16 }
#[derive(Clone, Copy)] #[repr(align(16))] struct Al { x: u32 }
#[derive(Clone, Copy)] struct Nest { lr: LR, t: (u8, u32), arr: [u16; 3] }
#[derive(Clone, Copy)] struct G<T> { v: T, w: T }
struct Holder { pad: u8, ranges: [LR; 3] }
fn pr(v: u64) { println!("{}", v); }
"#;

fn element_case(body: &str) -> String {
    format!("{ELEMENT_STORE_PRELUDE}{body}")
}

#[test]
fn whole_aggregate_store_into_referenced_array_element_matches_llvm() {
    if skip() {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("elemstore");
    let bodies = [
        (
            "unflatten",
            r#"fn unflatten(flat: &[u32; 8], out: &mut [LR; 4]) { let mut i = 0; while i < 4 { out[i] = LR { start: flat[2 * i], end: flat[2 * i + 1] }; i += 1; } }
fn main() { let flat = bb([1, 2, 3, 4, 5, 6, 7, 8]); let mut o = [LR { start: 0, end: 0 }; 4]; unflatten(&flat, &mut o); let mut s = 0u64; for i in 0..4 { s = s * 100 + o[i].start as u64 * 10 + o[i].end as u64; } pr(s); }"#,
        ),
        (
            "mixed_padding",
            r#"fn mixed(out: &mut [Mixed; 3], k: u64) { for i in 0..3 { out[i] = Mixed { a: i as u8, b: k << i, c: -(i as i16) }; } out[2] = out[0]; }
fn main() { let mut m = [Mixed { a: 9, b: 9, c: 9 }; 3]; mixed(&mut m, bb(3)); let mut s = 0u64; for i in 0..3 { s = s * 1000 + m[i].a as u64 * 100 + m[i].b * 10 + (m[i].c + 5) as u64; } pr(s); }"#,
        ),
        (
            "nested",
            r#"fn nest(out: &mut [Nest; 2], s: u32) { for i in 0..2 { out[i] = Nest { lr: LR { start: s, end: s + i as u32 }, t: (i as u8, s * 3), arr: [1, 2, i as u16] }; } }
fn main() { let mut n = [Nest { lr: LR { start: 0, end: 0 }, t: (0, 0), arr: [0; 3] }; 2]; nest(&mut n, bb(10)); let mut s = 0u64; for i in 0..2 { s = s * 7 + n[i].lr.start as u64 + n[i].lr.end as u64 * 3 + n[i].t.0 as u64 * 5 + n[i].t.1 as u64 + n[i].arr[0] as u64 + n[i].arr[2] as u64 * 11; } pr(s); }"#,
        ),
        (
            "generic",
            r#"fn gen<T: Copy>(out: &mut [G<T>; 2], a: T, b: T) { out[0] = G { v: a, w: b }; out[1] = G { v: b, w: a }; }
fn main() { let mut g = [G { v: 0u16, w: 0 }; 2]; gen(&mut g, bb(4u16), bb(9)); let mut g2 = [G { v: 0i64, w: 0 }; 2]; gen(&mut g2, bb(-4i64), bb(9)); pr(g[0].v as u64 * 1000 + g[0].w as u64 * 100 + g[1].v as u64 * 10 + g[1].w as u64); pr((g2[0].v + 100) as u64 * 1000 + (g2[1].w + 100) as u64); }"#,
        ),
        (
            "field_array",
            r#"fn field(h: &mut Holder, s: u32) { for i in 0..3 { h.ranges[i] = LR { start: s + i as u32, end: s }; } h.ranges[bb(1)] = LR { start: 99, end: 98 }; }
fn main() { let mut h = Holder { pad: 1, ranges: [LR { start: 0, end: 0 }; 3] }; field(&mut h, bb(20)); let mut s = h.pad as u64; for i in 0..3 { s = s * 10000 + h.ranges[i].start as u64 * 100 + h.ranges[i].end as u64; } pr(s); }"#,
        ),
        (
            "raw_pointer",
            r#"fn raw(p: *mut [LR; 2], k: usize) { unsafe { (*p)[k] = LR { start: 5, end: 6 }; (*p)[0] = (*p)[1]; } }
fn main() { let mut rr = [LR { start: 0, end: 0 }; 2]; raw(&mut rr, bb(1)); pr(rr[0].start as u64 * 1000 + rr[0].end as u64 * 100 + rr[1].start as u64 * 10 + rr[1].end as u64); }"#,
        ),
        (
            "out_of_bounds_panics",
            r#"fn oob(out: &mut [LR; 2], k: usize) { out[k] = LR { start: 1, end: 2 }; }
fn main() { let mut rr = [LR { start: 0, end: 0 }; 2]; oob(&mut rr, bb(1)); pr(rr[1].end as u64); oob(&mut rr, bb(2)); pr(7); }"#,
        ),
    ];
    let cases: Vec<(String, String)> = bodies
        .iter()
        .map(|(stem, body)| (stem.to_string(), element_case(body)))
        .collect();
    let refs: Vec<(&str, &str)> = cases
        .iter()
        .map(|(a, b)| (a.as_str(), b.as_str()))
        .collect();
    require_match(&dir, &dylib, &refs);
    let _ = std::fs::remove_dir_all(&dir);
}

/// Shapes the element-store admission does NOT take: an element of a SLICE
/// (`&mut [S]`, a fat base) and a single-field over-aligned
/// newtype element (at -O0/-O1 an older scalar-array path claims it and
/// refuses a runtime index by name; -O2/-O3 match). Each must keep its previous
/// route: compile and match, or refuse by name; never a wrong value.
#[test]
fn element_stores_outside_the_admission_match_or_refuse() {
    if skip() {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("elemstore_out");
    let cases = [
        (
            "slice_element",
            element_case(
                r#"fn sl(out: &mut [LR], s: u32) { for i in 0..out.len() { out[i] = LR { start: s + i as u32, end: s }; } }
fn main() { let mut o = [LR { start: 0, end: 0 }; 3]; sl(&mut o, bb(4)); pr(o[0].start as u64 * 100 + o[2].start as u64 * 10 + o[2].end as u64); }"#,
            ),
        ),
        (
            "overaligned_newtype",
            element_case(
                r#"fn al(out: &mut [Al; 3]) { for i in 0..3 { out[i] = Al { x: 7 * i as u32 + 1 }; } }
fn main() { let mut a = [Al { x: 0 }; 3]; al(&mut a); pr(a[0].x as u64 * 10000 + a[1].x as u64 * 100 + a[2].x as u64); }"#,
            ),
        ),
    ];
    for (stem, src) in &cases {
        for opt in OPT_LEVELS {
            let want = llvm(&dir, stem, src, opt, "abort");
            match compile(&dir, Some(&dylib), stem, src, opt, "abort") {
                Outcome::Ran(got) => assert_eq!(got, want, "`{stem}` at -O{opt}: WRONG output"),
                Outcome::Refused(stderr) => assert!(
                    stderr.contains("failing closed") || stderr.contains("unsupported"),
                    "`{stem}` at -O{opt}: refusal is not a named fail-closed: {stderr}"
                ),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Multi-variant enum elements of a referenced array (`out[k] = Some(v)`,
/// `out[k] = e` for `Option<u32>` and a three-variant enum). The element-store
/// admission is tagless-field-wise only; the enum lane copy was measured on
/// field chains alone. Pinned as measured on 2026-11-15: at -O0/-O1 the
/// non-inlined `en` refuses by name (`[TCG-MIR-UNSUPPORTED]` naming `en`); at
/// -O2/-O3 (`en` inlined into `main`) the program matches LLVM. Admitting the
/// O0/O1 shape is a new capability that needs its own differential and
/// decision-record entry, and must update this pin; it can never produce a
/// wrong value here.
#[test]
fn enum_element_stores_keep_their_measured_route() {
    if skip() {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("elemstore_enum");
    let cases = [
        (
            "enum_element",
            element_case(
                r#"fn en(out: &mut [Option<u32>; 3], k: usize, v: u32) { out[k] = Some(v); out[0] = None; }
fn main() { let mut o = [Some(1u32); 3]; en(&mut o, bb(2), bb(9)); pr(o[0].unwrap_or(5) as u64 * 100 + o[1].unwrap_or(5) as u64 * 10 + o[2].unwrap_or(5) as u64); }"#,
            ),
        ),
        (
            "enum_use",
            element_case(
                r#"fn en(out: &mut [Option<u32>; 3], k: usize, e: Option<u32>) { out[k] = e; }
fn main() { let mut o = [Some(1u32); 3]; en(&mut o, bb(2), bb(Some(9))); en(&mut o, bb(0), bb(None)); pr(o[0].unwrap_or(5) as u64 * 100 + o[1].unwrap_or(5) as u64 * 10 + o[2].unwrap_or(5) as u64); }"#,
            ),
        ),
        (
            "enum_custom_use",
            element_case(
                r#"#[derive(Clone, Copy)] enum E { A(u32), B(u16, u8), C }
fn v(e: E) -> u64 { match e { E::A(x) => x as u64, E::B(a, b) => a as u64 * 3 + b as u64, E::C => 7 } }
fn en(out: &mut [E; 3], k: usize, e: E) { out[k] = e; }
fn main() { let mut o = [E::C; 3]; en(&mut o, bb(2), bb(E::A(9))); en(&mut o, bb(1), bb(E::B(4, 5))); pr(v(o[0]) * 10000 + v(o[1]) * 100 + v(o[2])); }"#,
            ),
        ),
    ];
    for (stem, src) in &cases {
        for opt in OPT_LEVELS {
            let want = llvm(&dir, stem, src, opt, "abort");
            let inlined = matches!(opt, "2" | "3");
            match compile(&dir, Some(&dylib), stem, src, opt, "abort") {
                Outcome::Ran(got) => {
                    assert!(
                        inlined,
                        "`{stem}` at -O{opt}: compiled, but the non-inlined enum element store is pinned as refused"
                    );
                    assert_eq!(got, want, "`{stem}` at -O{opt}: WRONG output");
                }
                Outcome::Refused(stderr) => {
                    assert!(
                        !inlined,
                        "`{stem}` at -O{opt}: refused, expected to match LLVM: {stderr}"
                    );
                    assert!(
                        stderr.contains("[TCG-MIR-UNSUPPORTED]") && stderr.contains("2en"),
                        "`{stem}` at -O{opt}: expected the named refusal of `en`: {stderr}"
                    );
                }
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}
