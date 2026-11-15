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

// A String built by `format!`, `write!` or an integer's `to_string()` has
// std's capacity, and the allocator sees std's calls.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The bridge synthesizes these Strings instead of running `core::fmt`. It
// sized each one to a static worst case up front (every integer placeholder
// at its widest, plus one byte), so the bytes were right but the capacity was
// not. Measured on trust-cg main 555184eab (2026-10-09, against LLVM, both
// panic strategies): at every level `format!("{}", 5)` had capacity 12, not
// 8, `format!("")` allocated 1 byte instead of none, and `(-7i32).to_string()`
// had 12, not 11; at -O0/-O1 a `write!` into `String::new()` had 12, not 8 (at
// -O2/-O3 `write!` already ran std's own path). A program that reads
// `capacity()`, or counts allocator calls, saw a different value.
//
// std's rules, which the bridge now follows:
// * `format!` starts at `Arguments::estimated_capacity()` (a template with no
//   placeholder is `str::to_owned`: its length), and every `fmt::Write` call
//   then grows the String by the amortized rule. A negative integer's `'-'` is
//   its own `write_char`, a separate growth step before its digits.
// * `write!` starts from the String it is given and grows the same way.
// * A signed `to_string()` is `String::with_capacity(SIZE)` (`SIZE + 1` when
//   negative), SIZE being the digit count of the type's MAX. An unsigned one
//   is exactly its digits.
//
// Every write now reserves exactly its own bytes, so a store past them would
// be a heap overflow. `exact_fit_writes` writes into Strings whose capacity
// is exactly the bytes written, under an allocator that pads every block with
// canary bytes and counts any that change. It fires on a mutant that stores
// `bool`'s old fifth byte unconditionally (3 violations at -O0/-O1, 1 at
// -O2/-O3); the canary pointer goes through `black_box` because LLVM may
// otherwise drop canary stores past a `__rust_alloc` block's declared size.
// `allocator_calls` pins std's exact alloc/realloc/dealloc sequence.
//
// PROOF GATE: compiled with `no-proof-certs`; an execution differential, not a
// certification claim.

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;

const TARGET: &str = "aarch64-apple-darwin";
const OPTS: [u32; 4] = [0, 1, 2, 3];
const PANICS: [&str; 2] = ["abort", "unwind"];

struct Program {
    name: &'static str,
    src: &'static str,
    /// The LLVM oracle's stdout (every program exits 0), so a broken oracle
    /// cannot pass.
    stdout: &'static str,
}

const PROGRAMS: &[Program] = &[
    Program {
        name: "format_capacities",
        src: r##"use std::hint::black_box as bb;
fn ck(s: &String) -> u64 { let mut h = 0u64; for &c in s.as_bytes() { h = h.wrapping_mul(31).wrapping_add(c as u64); } h.wrapping_add(s.len() as u64) }
fn main() {
    let v = [
        format!("{}", bb(5)),
        format!("x={}", bb(123456789012i64)),
        format!("{}{}", bb(-5), bb(7)),
        format!("a fairly long literal piece here: {} and {}", bb(1u8), bb("tail")),
        format!("{}", bb("a runtime string that is longer than sixteen")),
        format!("{} {} {}", bb(1), bb(22), bb(333)),
        format!("{}", bb(-1234567890i64)),
        format!("v{}", bb(true)),
        format!("{}", bb('é')),
        format!("plain literal only"),
        format!(""),
        format!("{}{}", bb(false), bb('😀')),
        format!("{}", bb(i8::MIN)),
        format!("{}:{}", bb(u16::MAX), bb(i16::MIN)),
        format!("{}", bb(u64::MAX)),
        format!("[{}]", bb(i128::MIN)),
        format!("{}", bb(u128::MAX)),
        format!("{} and {}", "lit", "eral"),
        format!("prefix that is long enough {}", bb(0u8)),
        format!("{}", bb('a')),
        format!("{}{}{}{}{}{}{}{}{}", bb(1), bb(2), bb(3), bb(4), bb(5), bb(6), bb(7), bb(8), bb(9)),
        format!("ab{}", bb(-9i8)),
        format!("{}-{}", bb(0u32), bb(0i32)),
        format!("{}", bb(-7i32)),
    ];
    let mut h = 0u64;
    for s in v.iter() { h = h.wrapping_mul(1000003).wrapping_add(ck(s)); }
    for s in v.iter() { print!("{} ", s.capacity()); }
    println!();
    println!("{}", h);
}
"##,
        stdout: "8 14 8 78 44 8 16 8 8 18 0 16 8 16 20 82 39 12 54 8 16 4 8 8 \n14741762277812429773\n",
    },
    Program {
        name: "write_growth",
        src: r##"use std::fmt::Write;
use std::hint::black_box as bb;
fn main() {
    let mut s = String::new();
    write!(s, "{}", bb(5)).unwrap(); let c1 = s.capacity();
    write!(s, "abc{}def", bb(-12345)).unwrap(); let c2 = s.capacity();
    write!(s, "{}{}{}", bb(true), bb('x'), bb("yz")).unwrap(); let c3 = s.capacity();
    let mut t = String::with_capacity(3);
    write!(t, "hello {}", bb(1)).unwrap(); let c4 = t.capacity();
    let mut u = String::with_capacity(100);
    write!(u, "{}", bb(123)).unwrap(); let c5 = u.capacity();
    let mut w = String::new();
    write!(w, "a literal only write").unwrap(); let c6 = w.capacity();
    let mut x = String::new();
    for i in 0..10 { write!(x, "{},", bb(i * 1001)).unwrap(); }
    let c7 = x.capacity();
    println!("{} {} {} {} {} {} {}", c1, c2, c3, c4, c5, c6, c7);
    println!("{} {} {} {} {}", s.len(), t.len(), u.len(), w.len(), x.len());
}
"##,
        stdout: "8 16 32 8 100 20 64\n20 7 3 20 47\n",
    },
    Program {
        name: "integer_to_string",
        src: r##"use std::hint::black_box as bb;
fn main() {
    let v = [
        bb(0i32).to_string(), bb(7i32).to_string(), bb(-7i32).to_string(), bb(i32::MIN).to_string(), bb(i32::MAX).to_string(),
        bb(0u32).to_string(), bb(7u32).to_string(), bb(u32::MAX).to_string(),
        bb(-1i8).to_string(), bb(100u8).to_string(), bb(-300i16).to_string(), bb(65535u16).to_string(),
        bb(i64::MIN).to_string(), bb(12345678901u64).to_string(), bb(-5isize).to_string(), bb(42usize).to_string(),
    ];
    for s in v.iter() { print!("{} ", s.capacity()); }
    println!();
    let mut h = 0u64;
    for s in v.iter() { for &c in s.as_bytes() { h = h.wrapping_mul(31).wrapping_add(c as u64); } h = h.wrapping_add(s.len() as u64); }
    println!("{}", h);
}
"##,
        stdout: "10 10 11 11 10 1 1 10 4 3 6 5 20 11 20 2 \n192699330686867094\n",
    },
    Program {
        name: "allocator_calls",
        src: r##"use std::alloc::{GlobalAlloc, Layout, System};
use std::fmt::Write;
use std::hint::black_box as bb;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
static ON: AtomicBool = AtomicBool::new(false);
static N: AtomicUsize = AtomicUsize::new(0);
static mut LK: [u8; 256] = [0; 256];
static mut LA: [usize; 256] = [0; 256];
static mut LB: [usize; 256] = [0; 256];
fn rec(k: u8, a: usize, b: usize) {
    if ON.load(Ordering::Relaxed) {
        let i = N.fetch_add(1, Ordering::Relaxed);
        if i < 256 { unsafe { LK[i] = k; LA[i] = a; LB[i] = b; } }
    }
}
struct L;
unsafe impl GlobalAlloc for L {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 { rec(1, l.size(), l.align()); unsafe { System.alloc(l) } }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) { rec(2, l.size(), l.align()); unsafe { System.dealloc(p, l) } }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 { rec(3, l.size(), n); unsafe { System.realloc(p, l, n) } }
}
#[global_allocator]
static G: L = L;
fn main() {
    ON.store(true, Ordering::Relaxed);
    let a = format!("{}", bb(-1234567890i64));
    let b = format!("x={} y={} z={}", bb(1), bb(-22), bb(333333333));
    let mut s = String::new();
    write!(s, "{}{}", bb(true), bb('é')).unwrap();
    write!(s, "{}", bb(u64::MAX)).unwrap();
    let t = bb(-42i32).to_string();
    let u = bb(42u32).to_string();
    drop(a); drop(b); drop(s); drop(t); drop(u);
    ON.store(false, Ordering::Relaxed);
    let n = N.load(Ordering::Relaxed).min(256);
    let mut h = 0u64;
    for i in 0..n { let (k, x, y) = unsafe { (LK[i], LA[i], LB[i]) }; h = h.wrapping_mul(1000003).wrapping_add((k as u64) << 40 ^ (x as u64) << 20 ^ y as u64); }
    println!("{} {}", n, h);
    for i in 0..n { let (k, x, y) = unsafe { (LK[i], LA[i], LB[i]) }; println!("{} {} {}", k, x, y); }
}
"##,
        stdout: "13 14855237004448030190\n1 8 1\n3 8 16\n1 16 1\n3 16 32\n1 8 1\n3 8 26\n1 11 1\n1 2 1\n2 16 1\n2 32 1\n2 26 1\n2 11 1\n2 2 1\n",
    },
    Program {
        name: "exact_fit_writes",
        src: r##"use std::alloc::{GlobalAlloc, Layout, System};
use std::fmt::Write;
use std::hint::black_box as bb;
use std::sync::atomic::{AtomicUsize, Ordering};
static VIOL: AtomicUsize = AtomicUsize::new(0);
const PAD: usize = 16;
unsafe fn arm(p: *mut u8, size: usize) { let q = bb(p); let mut i = 0; while i < PAD { unsafe { *q.add(size + i) = 0xA5; } i += 1; } }
unsafe fn check(p: *mut u8, size: usize) { let q = bb(p); let mut i = 0; while i < PAD { if unsafe { *q.add(size + i) } != 0xA5 { VIOL.fetch_add(1, Ordering::Relaxed); } i += 1; } }
struct G;
unsafe impl GlobalAlloc for G {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc(Layout::from_size_align_unchecked(l.size() + PAD, l.align())) };
        if !p.is_null() { unsafe { arm(p, l.size()); } }
        p
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        unsafe { check(p, l.size()); System.dealloc(p, Layout::from_size_align_unchecked(l.size() + PAD, l.align())) }
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        unsafe { check(p, l.size()); }
        let q = unsafe { System.realloc(p, Layout::from_size_align_unchecked(l.size() + PAD, l.align()), n + PAD) };
        if !q.is_null() { unsafe { arm(q, n); } }
        q
    }
}
#[global_allocator]
static GA: G = G;
fn main() {
    let mut caps = 0u64;
    // Each String is created with exactly the bytes its write needs, so a
    // store past them lands in the canary.
    { let mut s = String::with_capacity(bb(4)); write!(s, "{}", bb(true)).unwrap(); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64); }
    { let mut s = String::with_capacity(bb(5)); write!(s, "{}", bb(false)).unwrap(); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64); }
    for c in [bb('a'), bb('é'), bb('€'), bb('😀')] {
        let mut s = String::with_capacity(c.len_utf8()); write!(s, "{}", c).unwrap(); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64);
    }
    for v in [bb(0i64), bb(7), bb(-7), bb(i64::MIN), bb(i64::MAX), bb(-1000000000)] {
        let n = format!("{}", v).len();
        let mut s = String::with_capacity(bb(n)); write!(s, "{}", v).unwrap(); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64);
    }
    for v in [bb(0u64), bb(u64::MAX), bb(10000000000000000000u64)] {
        let n = format!("{}", v).len();
        let mut s = String::with_capacity(bb(n)); write!(s, "{}", v).unwrap(); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64);
    }
    for v in [bb(i128::MIN), bb(-1i128), bb(i128::MAX)] {
        let n = format!("{}", v).len();
        let mut s = String::with_capacity(bb(n)); write!(s, "{}", v).unwrap(); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64);
    }
    { let mut s = String::with_capacity(bb(9)); write!(s, "{}{}{}", bb(-3i8), bb('€'), bb(true)).unwrap(); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64); }
    { let mut s = String::with_capacity(bb(0)); write!(s, "{}", bb(u16::MAX)).unwrap(); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64); }
    for v in [bb(-5i32), bb(i32::MIN), bb(9i32)] { let s = v.to_string(); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64); }
    for v in [bb(0u8), bb(255u8)] { let s = v.to_string(); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64); }
    { let s = bb(4294967295u32).to_string(); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64); }
    // format! fills std's estimated capacity (twice the literal bytes) exactly.
    { let s = format!("abcd{}", bb(true)); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64); }
    { let s = format!("abcde{}", bb(false)); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64); }
    { let s = format!("abcd{}", bb('😀')); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64); }
    { let s = format!("abc{}", bb('€')); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64); }
    { let s = format!("abcd{}", bb(-123i32)); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64); }
    { let s = format!("abcdefghij{}", bb(-123456789i64)); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64); }
    { let s = format!("abcdefghijklmnopqrst{}", bb(i128::MIN)); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64); }
    { let s = format!("abcdefghij{}", bb(u64::MAX)); caps = caps.wrapping_mul(31).wrapping_add(s.capacity() as u64); }
    println!("{} {}", caps, VIOL.load(Ordering::Relaxed));
}
"##,
        stdout: "14428314755315956922 0\n",
    },
];

#[derive(Debug, PartialEq, Eq)]
struct Ending {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
    stderr: String,
}

fn workdir() -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_format_capacity_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `program` with LLVM (`backend == None`) or the bridge and run it.
fn compile_and_run(
    dir: &Path,
    program: &Program,
    opt: u32,
    panic: &str,
    backend: Option<(&Path, &str)>,
) -> Result<Ending, String> {
    let side = if backend.is_some() { "tcg" } else { "llvm" };
    let stem = format!("{}_O{opt}_{panic}_{side}", program.name);
    let src = dir.join(format!("{stem}.rs"));
    std::fs::write(&src, program.src).expect("write source");
    let exe = dir.join(&stem);
    let mut cmd = toolchain_support::rustc_command_with_edition("2021");
    cmd.args([
        "--target",
        TARGET,
        "--crate-type",
        "bin",
        "-Ccodegen-units=1",
    ])
    .arg(format!("-Cpanic={panic}"))
    .arg(format!("-Copt-level={opt}"));
    if let Some((dylib, knobs)) = backend {
        let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
        arg.push(dylib);
        cmd.arg(arg).arg(knobs);
    }
    cmd.arg("-o").arg(&exe).arg(&src);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    let run = Command::new(&exe).output().expect("run the program");
    Ok(Ending {
        code: run.status.code(),
        signal: run.status.signal(),
        stdout: String::from_utf8_lossy(&run.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&run.stderr).into_owned(),
    })
}

/// One cell: the LLVM oracle must be the pinned run, and the bridge must
/// compile and match it exactly.
fn judge_cell(
    dir: &Path,
    program: &Program,
    opt: u32,
    panic: &str,
    backend: &Path,
    knobs: &str,
) -> Result<(), String> {
    let cell = format!("{} -O{opt} -Cpanic={panic}", program.name);
    let oracle = compile_and_run(dir, program, opt, panic, None)
        .map_err(|stderr| format!("{cell}: LLVM failed to compile: {stderr}"))?;
    if (oracle.code, oracle.signal, oracle.stdout.as_str()) != (Some(0), None, program.stdout) {
        return Err(format!(
            "{cell}: the LLVM oracle is not the pinned run: {oracle:?}"
        ));
    }
    match compile_and_run(dir, program, opt, panic, Some((backend, knobs))) {
        Ok(bridge) if bridge == oracle => Ok(()),
        Ok(bridge) => Err(format!(
            "{cell}: compiled and DIVERGES -- LLVM {oracle:?}, trust-cg {bridge:?}"
        )),
        Err(stderr) => Err(format!("{cell}: refused: <<<{stderr}>>>")),
    }
}

#[test]
fn format_write_and_to_string_strings_have_stds_capacity_aarch64() {
    darwin_native::require("format_capacity_aarch64", &[]);
    let backend = backend_artifact_support::current_test_backend();
    // Built once on the test's own thread, so its knob trace lands in this
    // test's captured output.
    let knobs = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    let dir = workdir();
    let cells: Vec<(&Program, u32, &str)> = PROGRAMS
        .iter()
        .flat_map(|p| {
            OPTS.iter()
                .flat_map(move |&o| PANICS.iter().map(move |&k| (p, o, k)))
        })
        .collect();
    let next = Mutex::new(0usize);
    let failures: Mutex<Vec<(usize, String)>> = Mutex::new(Vec::new());
    std::thread::scope(|scope| {
        for _ in 0..4 {
            scope.spawn(|| {
                loop {
                    let index = {
                        let mut next = next.lock().unwrap();
                        let index = *next;
                        *next += 1;
                        index
                    };
                    let Some(&(program, opt, panic)) = cells.get(index) else {
                        break;
                    };
                    if let Err(why) = judge_cell(&dir, program, opt, panic, &backend, &knobs) {
                        failures.lock().unwrap().push((index, why));
                    }
                }
            });
        }
    });
    let _ = std::fs::remove_dir_all(&dir);
    let mut failures = failures.into_inner().unwrap();
    failures.sort();
    assert!(
        failures.is_empty(),
        "{} cell(s) failed:\n  {}",
        failures.len(),
        failures
            .into_iter()
            .map(|(_, why)| why)
            .collect::<Vec<_>>()
            .join("\n  ")
    );
    eprintln!(
        "FORMAT_CAPACITY programs={} cells={} matched={} opts=0,1,2,3 strategies=abort,unwind",
        PROGRAMS.len(),
        cells.len(),
        cells.len()
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
