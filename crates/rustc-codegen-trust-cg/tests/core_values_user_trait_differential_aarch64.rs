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

// Core values a bridge model or binding produces for user and std types: a call
// result written into a FIELD of a memory-backed local, the `None` byte of
// `Vec<float>::partial_cmp`, and `Vec == array/slice` operands.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THREE FAMILIES, one test function each:
//
//   * FIELD RESULTS. rustc's builtin tuple and closure `Clone` shims write each
//     field with a call whose destination is a projection of the memory-backed
//     return place, `(_0.i: T) = <T as Clone>::clone(..)`. The bridge bound that
//     result only as an SSA projection, so `_0`'s slot was never written and the
//     returned tuple or closure held uninitialized stack. The custom-MIR rows
//     reach the same binding without a shim: a direct call, the `ctpop`
//     intrinsic and `u64::wrapping_mul` writing fields of a borrowed tuple.
//   * PARTIAL_CMP NONE. `Vec<f32/f64>::partial_cmp` wrote the helper's
//     unordered result 2 as the whole `Option<Ordering>`; rustc's `None` is the
//     niche byte its layout names (0xFE with the pinned compiler), so it read
//     back as `Some(<invalid 2>)`. The byte is now taken from `layout_of`.
//   * VEC EQ RHS. `<Vec<T> as PartialEq<[U; N]>>`, `PartialEq<&[U]>`,
//     `PartialEq<[U]>`, `PartialEq<&[U; N]>` and `PartialEq<&mut [U]>` reached
//     the `Vec == Vec` intercept, which read the array or slice operand as a
//     `{cap, ptr, len}` header. Only a `Vec<T>` operand is intercepted now; the
//     others compile std's own body.
//
// Every guest is free of undefined behavior (the one `unsafe` block reads the
// initialized byte of an `Option<Ordering>`) and has the same LLVM result at
// -O0..-O3; the oracle's exit code is pinned. Each cell is the guest built by
// LLVM and by the bridge (`no-proof-certs`: an execution differential, not a
// certification claim) with the same flags, run, and compared on stdout, exit
// code and killing signal. A `Match` cell must compile and match; a `Refuse`
// cell must fail closed with the named code and message fragment.
//
// MEASURED against the bridge of origin/main 33eefbf58 (Trust pack 9192, SDK
// 26.5): 88 of the 160 cells failed, exactly those at the levels each row's
// comment marks `bug` (a wrong value, SIGSEGV or a wrong drop log, or the
// refusal that row names); every other cell matched, or refused as it does now.

use std::os::unix::process::ExitStatusExt;
use std::path::Path;
use std::process::Command;
use std::sync::Mutex;

const TARGET: &str = "aarch64-apple-darwin";
const PANIC_ABORT: &str = "abort";
const PANIC_UNWIND: &str = "unwind";

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// The bridge compiles the cell and its run matches LLVM's.
    Match,
    /// The bridge refuses with this `[TCG-...]` code and message fragment.
    Refuse(&'static str, &'static str),
}

use Expect::Match;

const ALL_MATCH: [Expect; 4] = [Match, Match, Match, Match];
/// Darwin `panic=unwind`: a call with a cleanup edge whose result is stored
/// after the call keeps its existing refusal (no normal continuation there).
const UNWIND_CALL_RESULT_REFUSAL: Expect = Expect::Refuse(
    "TCG-MIR-UNSUPPORTED",
    "TerminatorKind::Call with cleanup unwind and a non-trivial result",
);
/// The `Vec ==` intercept models integer and float elements only.
const BOOL_ELEMENT_EQ_REFUSAL: Expect = Expect::Refuse(
    "TCG-MIR-UNSUPPORTED",
    "Vec `==` over a non-integer/non-float element bool is not modeled",
);

struct Case {
    name: &'static str,
    src: &'static str,
    /// LLVM's exit code, identical at -O0..-O3.
    oracle_exit: i32,
    /// Expected bridge outcome at -O0..-O3 under `-Cpanic=abort`.
    abort: [Expect; 4],
    /// Expected bridge outcome at -O0..-O3 under `-Cpanic=unwind`, if run.
    unwind: Option<[Expect; 4]>,
}

#[derive(Debug, PartialEq, Eq)]
struct Ending {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
}

fn compile(
    dir: &Path,
    case: &Case,
    panic: &str,
    opt: usize,
    backend: Option<&Path>,
) -> Result<std::path::PathBuf, String> {
    let src = dir.join(format!("{}.rs", case.name));
    std::fs::write(&src, case.src).expect("write guest");
    let exe = dir.join(format!(
        "{}-{panic}-O{opt}-{}",
        case.name,
        if backend.is_some() { "bridge" } else { "llvm" }
    ));
    let mut cmd = toolchain_support::rustc_command_with_edition("2021");
    cmd.args([
        "--target",
        TARGET,
        "--crate-type",
        "bin",
        "-Ccodegen-units=1",
        "-Coverflow-checks=off",
    ])
    .arg(format!("-Cpanic={panic}"))
    .arg(format!("-Copt-level={opt}"));
    if let Some(backend) = backend {
        let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
        arg.push(backend);
        cmd.arg(arg)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.arg("-o").arg(&exe).arg(&src);
    let output = cmd.output().expect("spawn the compiler");
    if output.status.success() {
        Ok(exe)
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

fn run(exe: &Path) -> Ending {
    let output = Command::new(exe).output().expect("run guest");
    Ending {
        code: output.status.code(),
        signal: output.status.signal(),
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
    }
}

/// The first `[TCG-...]` code in a fail-closed refusal; `None` for a crash.
fn refusal_code(stderr: &str) -> Option<&str> {
    if stderr.contains("internal compiler error") || stderr.contains("panicked at") {
        return None;
    }
    let start = stderr.find("[TCG-")?;
    let end = stderr[start..].find(']')? + start + 1;
    Some(&stderr[start + 1..end - 1])
}

#[derive(Default)]
struct Tally {
    cells: usize,
    matched: usize,
    refused: usize,
    failures: Vec<String>,
}

/// One cell: the LLVM oracle (exit code pinned), then the bridge under `expect`.
fn cell(
    dir: &Path,
    backend: &Path,
    case: &Case,
    panic: &str,
    opt: usize,
    expect: Expect,
) -> Result<bool, String> {
    let label = format!("{} panic={panic} O{opt}", case.name);
    let llvm_exe = compile(dir, case, panic, opt, None)
        .map_err(|e| format!("{label}: the LLVM oracle failed to compile: <<<{e}>>>"))?;
    let oracle = run(&llvm_exe);
    if oracle.code != Some(case.oracle_exit) || oracle.signal.is_some() {
        return Err(format!(
            "{label}: the LLVM oracle ended {oracle:?}, not exit {}",
            case.oracle_exit
        ));
    }
    match (compile(dir, case, panic, opt, Some(backend)), expect) {
        (Ok(exe), Expect::Match) => {
            let bridge = run(&exe);
            if bridge == oracle {
                Ok(true)
            } else {
                Err(format!(
                    "{label}: DIVERGES — LLVM {oracle:?}, trust-cg {bridge:?}"
                ))
            }
        }
        (Ok(exe), Expect::Refuse(code, _)) => Err(format!(
            "{label}: compiled (ran {:?}) where [{code}] was expected",
            run(&exe)
        )),
        (Err(stderr), Expect::Refuse(code, fragment)) => {
            if refusal_code(&stderr) == Some(code) && stderr.contains(fragment) {
                Ok(false)
            } else {
                Err(format!(
                    "{label}: refused without [{code}] and `{fragment}`: <<<{stderr}>>>"
                ))
            }
        }
        (Err(stderr), Expect::Match) => Err(format!(
            "{label}: refused ({:?}) a cell that must compile and match: <<<{stderr}>>>",
            refusal_code(&stderr)
        )),
    }
}

/// Run every cell of `cases` on a small worker pool and return the tally.
fn run_family(family: &str, cases: &[Case]) -> Tally {
    darwin_native::require(family, &[]);
    let backend = backend_artifact_support::current_test_backend();
    let dir = std::env::temp_dir().join(format!("tcg_core_values_{family}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    let mut jobs = Vec::new();
    for case in cases {
        for (opt, expect) in case.abort.iter().enumerate() {
            jobs.push((case, PANIC_ABORT, opt, *expect));
        }
        if let Some(unwind) = &case.unwind {
            for (opt, expect) in unwind.iter().enumerate() {
                jobs.push((case, PANIC_UNWIND, opt, *expect));
            }
        }
    }
    let queue = Mutex::new(jobs);
    let tally = Mutex::new(Tally::default());
    std::thread::scope(|scope| {
        for _ in 0..4 {
            scope.spawn(|| {
                loop {
                    let Some((case, panic, opt, expect)) = queue.lock().unwrap().pop() else {
                        break;
                    };
                    let outcome = cell(&dir, &backend, case, panic, opt, expect);
                    let mut tally = tally.lock().unwrap();
                    tally.cells += 1;
                    match outcome {
                        Ok(true) => tally.matched += 1,
                        Ok(false) => tally.refused += 1,
                        Err(failure) => tally.failures.push(failure),
                    }
                }
            });
        }
    });
    let _ = std::fs::remove_dir_all(&dir);
    let mut tally = tally.into_inner().unwrap();
    tally.failures.sort();
    tally
}

fn assert_family(family: &str, marker: &str, cases: &[Case]) {
    let tally = run_family(family, cases);
    assert!(
        tally.failures.is_empty(),
        "{} of {} {family} cell(s) failed:\n  {}",
        tally.failures.len(),
        tally.cells,
        tally.failures.join("\n  ")
    );
    eprintln!(
        "{marker} cases={} cells={} matched={} refused={}",
        cases.len(),
        tally.cells,
        tally.matched,
        tally.refused
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

// ---------------------------------------------------------------------------
// The cases. "bug" names the levels (and strategies) where origin/main 33eefbf58
// diverged from LLVM; every other cell matched there, or refused as listed.
// ---------------------------------------------------------------------------

const FIELD_RESULT_CASES: &[Case] = &[
    // `(D, D).clone()`, derived `Clone`. bug -O0/-O1 (exit 1); the unwind
    // shim's cleanup-edge call is refused at every level, before and after.
    Case {
        name: "tuple_derived_clone",
        src: r#"#[derive(Clone)]
struct D { a: u32 }
fn main() {
    let t = (D { a: std::hint::black_box(10) }, D { a: 20 });
    let t2 = t.clone();
    std::process::exit((t2.0.a + t2.1.a) as i32);
}
"#,
        oracle_exit: 30,
        abort: ALL_MATCH,
        unwind: Some([UNWIND_CALL_RESULT_REFUSAL; 4]),
    },
    // `(Box<u32>, u8)` cloned in a non-inlined generic: std-only `Clone`s.
    // bug -O0..-O3 (exit 9, 9, SIGSEGV, 115); unwind lowers the Box drop glue.
    Case {
        name: "tuple_box_generic_clone",
        src: r#"#[inline(never)]
fn dup<T: Clone>(t: &T) -> T { t.clone() }
fn main() {
    let t = (Box::new(std::hint::black_box(41u32)), 2u8);
    let t2 = dup(&t);
    std::process::exit((*t2.0 + t2.1 as u32 * 3) as i32);
}
"#,
        oracle_exit: 47,
        abort: ALL_MATCH,
        unwind: Some(ALL_MATCH),
    },
    // `(S, W, S).clone()`, hand-written `Clone`s. bug -O0..-O3.
    Case {
        name: "tuple_user_clone",
        src: r#"use std::sync::atomic::{AtomicU64, Ordering::SeqCst};
static LOG: AtomicU64 = AtomicU64::new(0);
fn ev(x: u64) { LOG.store(LOG.load(SeqCst).wrapping_mul(31).wrapping_add(x), SeqCst); }
struct S { a: u32 }
impl Clone for S { fn clone(&self) -> S { ev(self.a as u64); S { a: self.a + 100 } } }
struct W(u64);
impl Clone for W { fn clone(&self) -> W { ev(500 + self.0); W(self.0 * 2) } }
fn main() {
    let t = (S { a: std::hint::black_box(1) }, W(2), S { a: 3 });
    let t2 = t.clone();
    let x0 = t2.0.a as u64; let x1 = t2.1 .0; let x2 = t2.2.a as u64;
    let log = LOG.load(SeqCst);
    println!("{x0} {x1} {x2} log={log}");
    std::process::exit(((x0 + x1 * 10 + x2 * 100) % 251) as i32);
}
"#,
        oracle_exit: 150,
        abort: ALL_MATCH,
        unwind: None,
    },
    // A `move` closure capturing a user-`Clone` value and a `u8`, cloned.
    // bug -O0/-O1 under both strategies (r2=3 for 1053).
    Case {
        name: "closure_clone_shim",
        src: r#"use std::sync::atomic::{AtomicU64, Ordering::SeqCst};
static CNT: AtomicU64 = AtomicU64::new(0);
struct S { a: u32 }
impl S { fn get(&self) -> u32 { self.a } }
impl Clone for S { fn clone(&self) -> S { CNT.fetch_add(1, SeqCst); S { a: self.a + 100 } } }
fn main() {
    let s = S { a: std::hint::black_box(5) };
    let k = std::hint::black_box(3u8);
    let c = move || s.get() as u64 * 10 + k as u64;
    let c2 = c.clone();
    let r1 = c(); let r2 = c2();
    let cnt = CNT.load(SeqCst);
    println!("r1={r1} r2={r2} cnt={cnt}");
    std::process::exit(((r1 + r2 * 3 + cnt) % 251) as i32);
}
"#,
        oracle_exit: 201,
        abort: ALL_MATCH,
        unwind: Some(ALL_MATCH),
    },
    // `(W(u64), W(u64)).clone()`. bug -O0/-O1.
    Case {
        name: "tuple_u64_newtypes",
        src: r#"use std::sync::atomic::{AtomicU64, Ordering::SeqCst};
static CNT: AtomicU64 = AtomicU64::new(0);
struct W(u64);
impl Clone for W { fn clone(&self) -> W { CNT.fetch_add(1, SeqCst); W(self.0 * 2 + 1) } }
fn main() {
    let t = (W(std::hint::black_box(10)), W(20));
    let t2 = t.clone();
    let x0 = t2.0 .0; let x1 = t2.1 .0;
    let cnt = CNT.load(SeqCst);
    println!("{x0} {x1} cnt={cnt}");
    std::process::exit(((x0 + x1 * 3 + cnt) % 251) as i32);
}
"#,
        oracle_exit: 146,
        abort: ALL_MATCH,
        unwind: None,
    },
    // `(S, u8)` cloned through a non-inlined generic. bug -O0..-O3 under both
    // strategies.
    Case {
        name: "tuple_generic_clone",
        src: r#"use std::sync::atomic::{AtomicU64, Ordering::SeqCst};
static CNT: AtomicU64 = AtomicU64::new(0);
struct S { a: u32 }
impl Clone for S { fn clone(&self) -> S { CNT.fetch_add(1, SeqCst); S { a: self.a + 100 } } }
#[inline(never)]
fn dup<T: Clone>(t: &T) -> T { t.clone() }
fn main() {
    let t = (S { a: std::hint::black_box(1) }, 8u8);
    let t2 = dup(&t);
    let x0 = t2.0.a as u64; let x1 = t2.1 as u64;
    let cnt = CNT.load(SeqCst);
    println!("{x0} {x1} cnt={cnt}");
    std::process::exit(((x0 + x1 * 3 + cnt) % 251) as i32);
}
"#,
        oracle_exit: 126,
        abort: ALL_MATCH,
        unwind: Some(ALL_MATCH),
    },
    // `(Box<u32>, u32).clone()`. bug -O0/-O1 (a garbage `*t2.0`).
    Case {
        name: "tuple_box_clone",
        src: r#"fn main() {
    let t = (Box::new(std::hint::black_box(10u32)), 5u32);
    let t2 = t.clone();
    let x0 = *t2.0 as u64; let x1 = t2.1 as u64;
    let same = std::ptr::eq(&*t.0, &*t2.0) as u64;
    println!("{x0} {x1} same={same}");
    std::process::exit(((x0 + x1 * 3 + same * 7) % 251) as i32);
}
"#,
        oracle_exit: 25,
        abort: ALL_MATCH,
        unwind: None,
    },
    // `(S,).clone()`. bug -O0/-O1.
    Case {
        name: "one_tuple_clone",
        src: r#"use std::sync::atomic::{AtomicU64, Ordering::SeqCst};
static CNT: AtomicU64 = AtomicU64::new(0);
struct S { a: u32 }
impl Clone for S { fn clone(&self) -> S { CNT.fetch_add(1, SeqCst); S { a: self.a + 100 } } }
fn main() {
    let t = (S { a: std::hint::black_box(1) },);
    let t2 = t.clone();
    let x0 = t2.0.a as u64;
    let cnt = CNT.load(SeqCst);
    println!("{x0} cnt={cnt}");
    std::process::exit(((x0 + cnt) % 251) as i32);
}
"#,
        oracle_exit: 102,
        abort: ALL_MATCH,
        unwind: None,
    },
    // `(S, S, S).clone()` passed by value. bug -O0..-O3.
    Case {
        name: "tuple_clone_by_value",
        src: r#"use std::sync::atomic::{AtomicU64, Ordering::SeqCst};
static CNT: AtomicU64 = AtomicU64::new(0);
struct S { a: u32 }
impl Clone for S { fn clone(&self) -> S { CNT.fetch_add(1, SeqCst); S { a: self.a * 3 } } }
#[inline(never)]
fn total(t: (S, S, S)) -> u64 { t.0.a as u64 + t.1.a as u64 * 10 + t.2.a as u64 * 100 }
fn main() {
    let t = (S { a: std::hint::black_box(1) }, S { a: 2 }, S { a: 3 });
    let r = total(t.clone());
    let cnt = CNT.load(SeqCst);
    println!("r={r} cnt={cnt}");
    std::process::exit(((r + cnt) % 251) as i32);
}
"#,
        oracle_exit: 213,
        abort: ALL_MATCH,
        unwind: None,
    },
    // `Option<(S, u8)>::clone()` reaches the tuple shim. bug -O0/-O1 under
    // both strategies.
    Case {
        name: "option_tuple_clone",
        src: r#"use std::sync::atomic::{AtomicU64, Ordering::SeqCst};
static CNT: AtomicU64 = AtomicU64::new(0);
struct S { a: u32 }
impl Clone for S { fn clone(&self) -> S { CNT.fetch_add(1, SeqCst); S { a: self.a + 100 } } }
fn main() {
    let o = Some((S { a: std::hint::black_box(1) }, 8u8));
    let o2 = o.clone();
    let (x0, x1) = match &o2 { Some((s, b)) => (s.a as u64, *b as u64), None => (0, 0) };
    let cnt = CNT.load(SeqCst);
    println!("{x0} {x1} cnt={cnt}");
    std::process::exit(((x0 + x1 * 3 + cnt) % 251) as i32);
}
"#,
        oracle_exit: 126,
        abort: ALL_MATCH,
        unwind: Some(ALL_MATCH),
    },
    // A derived `Clone` whose field is a tuple. bug -O0/-O1 under both
    // strategies.
    Case {
        name: "derive_with_tuple_field",
        src: r#"#[derive(Clone)]
struct D { a: u32 }
#[derive(Clone)]
struct H { t: (D, u32), z: u8 }
fn main() {
    let h = H { t: (D { a: std::hint::black_box(10) }, 20), z: 3 };
    let h2 = h.clone();
    let x0 = h2.t.0.a as u64; let x1 = h2.t.1 as u64; let x2 = h2.z as u64;
    println!("{x0} {x1} {x2}");
    std::process::exit(((x0 + x1 * 3 + x2 * 7) % 251) as i32);
}
"#,
        oracle_exit: 91,
        abort: ALL_MATCH,
        unwind: Some(ALL_MATCH),
    },
    // `(S, S).clone()` with `Drop` on `S`: the drops ran on garbage fields.
    // bug -O0..-O3 under both strategies.
    Case {
        name: "tuple_clone_drop_log",
        src: r#"use std::sync::atomic::{AtomicU64, Ordering::SeqCst};
static LOG: AtomicU64 = AtomicU64::new(0);
fn ev(x: u64) { LOG.store(LOG.load(SeqCst).wrapping_mul(31).wrapping_add(x), SeqCst); }
struct S { a: u32 }
impl Clone for S { fn clone(&self) -> S { ev(100 + self.a as u64); S { a: self.a + 10 } } }
impl Drop for S { fn drop(&mut self) { ev(200 + self.a as u64); } }
fn main() {
    {
        let t = (S { a: std::hint::black_box(1) }, S { a: 2 });
        let t2 = t.clone();
        ev(t2.0.a as u64 + t2.1.a as u64 * 1000);
    }
    let log = LOG.load(SeqCst);
    println!("log={log}");
    std::process::exit((log % 251) as i32);
}
"#,
        oracle_exit: 76,
        abort: ALL_MATCH,
        unwind: Some(ALL_MATCH),
    },
    // A closure capturing two user-`Clone` values, cloned in a generic.
    // bug -O0..-O3.
    Case {
        name: "closure_two_captures",
        src: r#"use std::sync::atomic::{AtomicU64, Ordering::SeqCst};
static LOG: AtomicU64 = AtomicU64::new(0);
fn ev(x: u64) { LOG.store(LOG.load(SeqCst).wrapping_mul(31).wrapping_add(x), SeqCst); }
struct S { a: u32 }
impl S { fn get(&self) -> u32 { self.a } }
impl Clone for S { fn clone(&self) -> S { ev(self.a as u64); S { a: self.a + 100 } } }
struct W(u64);
impl W { fn get(&self) -> u64 { self.0 } }
impl Clone for W { fn clone(&self) -> W { ev(500 + self.0); W(self.0 * 3) } }
#[inline(never)]
fn twice<F: Fn() -> u64 + Clone>(f: &F) -> u64 { let g = f.clone(); g() * 1000 + f() }
fn main() {
    let s = S { a: std::hint::black_box(5) };
    let w = W(std::hint::black_box(7));
    let k = std::hint::black_box(11u64);
    let c = move || s.get() as u64 * 10 + w.get() + k;
    let r = twice(&c);
    let log = LOG.load(SeqCst);
    println!("r={r} log={log}");
    std::process::exit(((r + log) % 251) as i32);
}
"#,
        oracle_exit: 167,
        abort: ALL_MATCH,
        unwind: None,
    },
    // Custom MIR, no shim: `Call(temp.0 = mk(x))` into a borrowed tuple.
    // bug -O0..-O3 under both strategies.
    Case {
        name: "custom_mir_call_into_field",
        src: r#"#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
use core::intrinsics::mir::*;
#[inline(never)]
fn mk(x: u32) -> u32 { x * 3 + 1 }
#[inline(never)]
fn read(r: &(u32, u32)) -> u32 { r.0 * 10 + r.1 }
#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
fn probe(x: u32) -> u32 {
    mir! {
        let temp: (u32, u32);
        let r: &(u32, u32);
        {
            temp.1 = 2;
            Call(temp.0 = mk(x), ReturnTo(bb1), UnwindUnreachable())
        }
        bb1 = {
            r = &temp;
            Call(RET = read(r), ReturnTo(bb2), UnwindUnreachable())
        }
        bb2 = {
            Return()
        }
    }
}
fn main() {
    let v = probe(std::hint::black_box(4));
    println!("{v}");
    std::process::exit((v % 251) as i32);
}
"#,
        oracle_exit: 132,
        abort: ALL_MATCH,
        unwind: Some(ALL_MATCH),
    },
    // Custom MIR: `ctpop` and `u64::wrapping_mul` results into fields of a
    // borrowed tuple. bug -O0..-O3.
    Case {
        name: "custom_mir_intrinsic_into_field",
        src: r#"#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
use core::intrinsics::mir::*;
#[inline(never)]
fn read(r: &(u32, u64, u32)) -> u64 { r.0 as u64 * 1000 + r.1 * 10 + r.2 as u64 }
#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
fn probe(x: u32, y: u64) -> u64 {
    mir! {
        let temp: (u32, u64, u32);
        let r: &(u32, u64, u32);
        {
            temp.2 = 7;
            Call(temp.0 = core::intrinsics::ctpop::<u32>(x), ReturnTo(bb1), UnwindUnreachable())
        }
        bb1 = {
            Call(temp.1 = u64::wrapping_mul(y, 3), ReturnTo(bb2), UnwindUnreachable())
        }
        bb2 = {
            r = &temp;
            Call(RET = read(r), ReturnTo(bb3), UnwindUnreachable())
        }
        bb3 = {
            Return()
        }
    }
}
fn main() {
    let v = probe(std::hint::black_box(0b1011), std::hint::black_box(5));
    println!("{v}");
    std::process::exit((v % 251) as i32);
}
"#,
        oracle_exit: 145,
        abort: ALL_MATCH,
        unwind: None,
    },
    // CONTROL: a tuple of primitives (`u8`..`u64`, `i8`, `i64`, `bool`,
    // `char`) cloned directly and through a generic. Matched before.
    Case {
        name: "control_primitive_tuple",
        src: r#"#[inline(never)]
fn dup<T: Clone>(t: &T) -> T { t.clone() }
fn main() {
    let t = (std::hint::black_box(3u8), 400u16, 70000u32, 1u64 << 40, -5i8, -9i64, true, 'z');
    let t2 = t.clone();
    let t3 = dup(&t);
    let s = |t: &(u8, u16, u32, u64, i8, i64, bool, char)| {
        t.0 as u64 + t.1 as u64 + t.2 as u64 + (t.3 >> 30) + (t.4 as i64 + t.5 + 100) as u64 + t.6 as u64 + t.7 as u64
    };
    println!("{} {}", s(&t2), s(&t3));
    std::process::exit(((s(&t2) + s(&t3) * 3) % 251) as i32);
}
"#,
        oracle_exit: 153,
        abort: ALL_MATCH,
        unwind: None,
    },
];

const PARTIAL_CMP_CASES: &[Case] = &[
    // `Vec<f64>::partial_cmp` over NaN, signed-zero and prefix cases.
    // bug -O0/-O1 (the NaN case decoded as `Some`).
    Case {
        name: "vec_f64_partial_cmp_cases",
        src: r#"fn code(o: Option<std::cmp::Ordering>) -> i32 {
    match o { None => 9, Some(std::cmp::Ordering::Less) => 1, Some(std::cmp::Ordering::Equal) => 2, Some(std::cmp::Ordering::Greater) => 3 }
}
#[inline(never)]
fn pc(a: &Vec<f64>, b: &Vec<f64>) -> i32 { code(a.partial_cmp(b)) }
fn main() {
    let n = std::hint::black_box(f64::NAN);
    let a: Vec<f64> = vec![1.0, n];
    let b: Vec<f64> = vec![2.0, n];
    let c: Vec<f64> = vec![n, 1.0];
    let e: Vec<f64> = vec![0.0, 1.0];
    let f: Vec<f64> = vec![-0.0];
    let g: Vec<f64> = vec![1.0, 2.0];
    let h: Vec<f64> = vec![1.0, 2.0, n];
    let r1 = pc(&a, &b); // Some(Less)
    let r2 = pc(&c, &c); // None
    let r3 = pc(&e, &f); // Some(Greater): 0.0 == -0.0, then longer
    let r4 = pc(&g, &h); // Some(Less): prefix, shorter
    let r5 = pc(&b, &a); // Some(Greater)
    println!("{} {} {} {} {}", r1, r2, r3, r4, r5); // 1 9 3 1 3
    std::process::exit(r1 + r2 * 2 + r3 * 4 + r4 * 8 + r5 * 16);
}
"#,
        oracle_exit: 87,
        abort: ALL_MATCH,
        unwind: None,
    },
    // `is_none()`, a full `match` and an `as i32` arm on the unordered
    // result. bug -O0/-O1.
    Case {
        name: "vec_f64_partial_cmp_none_decode",
        src: r#"use std::cmp::Ordering;
fn code(o: Option<Ordering>) -> i32 {
    match o { None => 9, Some(Ordering::Less) => 1, Some(Ordering::Equal) => 2, Some(Ordering::Greater) => 3 }
}
fn main() {
    let n = std::hint::black_box(f64::NAN);
    let c: Vec<f64> = vec![n, 1.0];
    let d: Vec<f64> = vec![n, 1.0];
    let o = c.partial_cmp(&d);
    let r1 = o.is_none() as i32;              // 1
    let r2 = code(o);                         // 9
    let r4 = code(n.partial_cmp(&1.0));       // 9
    let r5 = match c.partial_cmp(&d) { None => 9, Some(x) => x as i32 + 5 };
    println!("{} {} {} {}", r1, r2, r4, r5); // 1 9 9 9
    std::process::exit(r1 + r2 * 2 + r4 * 8 + r5 * 1);
}
"#,
        oracle_exit: 100,
        abort: ALL_MATCH,
        unwind: None,
    },
    // The minimal `is_none()` exit. bug -O0/-O1.
    Case {
        name: "vec_f64_partial_cmp_is_none",
        src: r#"fn main() {
    let n = std::hint::black_box(f64::NAN);
    let c: Vec<f64> = vec![n, 1.0];
    let d: Vec<f64> = vec![n, 1.0];
    let o = c.partial_cmp(&d);
    std::process::exit(if o.is_none() { 1 } else { 0 });
}
"#,
        oracle_exit: 1,
        abort: ALL_MATCH,
        unwind: None,
    },
    // The stored byte itself (-2), read through a pointer cast. bug -O0/-O1
    // (byte 2).
    Case {
        name: "vec_f64_partial_cmp_raw_byte",
        src: r#"use std::cmp::Ordering;
fn main() {
    let n = std::hint::black_box(f64::NAN);
    let c: Vec<f64> = vec![n, 1.0];
    let d: Vec<f64> = vec![n, 1.0];
    let o: Option<Ordering> = c.partial_cmp(&d);
    let p: Option<Ordering> = n.partial_cmp(&1.0);
    let ob = unsafe { *(&o as *const Option<Ordering> as *const i8) };
    let pb = unsafe { *(&p as *const Option<Ordering> as *const i8) };
    let a = o.is_none() as i32; let b = p.is_none() as i32;
    println!("ob={} pb={} o_none={} p_none={}", ob, pb, a, b);
    std::process::exit(a * 2 + b);
}
"#,
        oracle_exit: 3,
        abort: ALL_MATCH,
        unwind: None,
    },
    // `Vec<f32>`: `unwrap_or(Equal) as i32` read 2. bug -O0/-O1.
    Case {
        name: "vec_f32_partial_cmp",
        src: r#"use std::cmp::Ordering;
#[inline(never)]
fn pc32(a: &Vec<f32>, b: &Vec<f32>) -> Option<Ordering> { a.partial_cmp(b) }
fn main() {
    let n = std::hint::black_box(f32::NAN);
    let a: Vec<f32> = vec![1.0, n];
    let b: Vec<f32> = vec![1.0, 2.0];
    let o = pc32(&a, &b);                       // lane 1 unordered -> None
    let p = a.partial_cmp(&b);                  // same, inline in main
    let q = vec![1.0f32].partial_cmp(&vec![1.0f32, n]); // prefix -> Some(Less)
    let r1 = o.is_none() as i32;
    let r2 = (p == None) as i32;
    let r3 = o.unwrap_or(Ordering::Equal) as i32;
    let r4 = (q == Some(Ordering::Less)) as i32;
    println!("{} {} {} {}", r1, r2, r3, r4); // 1 1 0 1
    std::process::exit(r1 + r2 * 2 + r4 * 4 + (r3 + 1) * 8);
}
"#,
        oracle_exit: 15,
        abort: ALL_MATCH,
        unwind: None,
    },
    // An address-taken (memory-backed) `Option<Ordering>` destination.
    // bug -O0/-O1.
    Case {
        name: "vec_f64_partial_cmp_memory_destination",
        src: r#"use std::cmp::Ordering;
#[inline(never)]
fn show(o: &Option<Ordering>) -> i32 { match o { None => 9, Some(x) => *x as i32 + 5 } }
fn main() {
    let n = std::hint::black_box(f64::NAN);
    let a: Vec<f64> = vec![1.0, n];
    let b: Vec<f64> = vec![1.0, 2.0];
    let o = a.partial_cmp(&b);
    let r1 = show(&o);
    let p = b.partial_cmp(&a);
    let r2 = show(&p);
    let c: Vec<f64> = vec![0.5];
    let q = c.partial_cmp(&b);
    let r3 = show(&q);
    println!("{} {} {}", r1, r2, r3); // 9 9 4
    std::process::exit(r1 + r2 * 2 + r3 * 4);
}
"#,
        oracle_exit: 43,
        abort: ALL_MATCH,
        unwind: None,
    },
    // CONTROL: `u8`/`i32`/`u64`/`i64` (always `Some`) and NaN-free `f64`.
    // Matched before.
    Case {
        name: "control_integer_partial_cmp",
        src: r#"use std::cmp::Ordering;
fn code(o: Option<Ordering>) -> i32 {
    match o { None => 9, Some(Ordering::Less) => 1, Some(Ordering::Equal) => 2, Some(Ordering::Greater) => 3 }
}
#[inline(never)]
fn pu8(a: &Vec<u8>, b: &Vec<u8>) -> i32 { code(a.partial_cmp(b)) }
#[inline(never)]
fn pi32(a: &Vec<i32>, b: &Vec<i32>) -> i32 { code(a.partial_cmp(b)) }
#[inline(never)]
fn pu64(a: &Vec<u64>, b: &Vec<u64>) -> i32 { code(a.partial_cmp(b)) }
#[inline(never)]
fn pi64(a: &Vec<i64>, b: &Vec<i64>) -> i32 { code(a.partial_cmp(b)) }
#[inline(never)]
fn pf64(a: &Vec<f64>, b: &Vec<f64>) -> i32 { code(a.partial_cmp(b)) }
fn main() {
    let x = std::hint::black_box(200u8);
    let r1 = pu8(&vec![1, x], &vec![1, 3]);          // Greater (unsigned)
    let r2 = pi32(&vec![-5, 2], &vec![-5, 2]);       // Equal
    let r3 = pi32(&vec![-5], &vec![3]);              // Less (signed)
    let r4 = pu64(&vec![u64::MAX], &vec![1]);        // Greater
    let r5 = pi64(&vec![1, 2], &vec![1, 2, 3]);      // Less (prefix)
    let r6 = pf64(&vec![1.5, -0.0], &vec![1.5, 0.0]); // Equal
    let r7 = pf64(&vec![2.0], &vec![1.0, 9.0]);      // Greater
    println!("{} {} {} {} {} {} {}", r1, r2, r3, r4, r5, r6, r7);
    std::process::exit(r1 + r2 * 2 + r3 * 3 + r4 * 5 + r5 * 7 + r6 * 11 + r7 * 13);
}
"#,
        oracle_exit: 93,
        abort: ALL_MATCH,
        unwind: None,
    },
];

const VEC_EQ_CASES: &[Case] = &[
    // `Vec<i32> == [i32; 3]`. bug -O0/-O1 (false).
    Case {
        name: "vec_eq_array",
        src: r#"fn main() {
    let mut v: Vec<i32> = Vec::new();
    for x in [1, 2, 3] { v.push(x); }
    let arr = std::hint::black_box([1, 2, 3]);
    let r1 = v == arr;          // true
    println!("r1={}", r1);
    std::process::exit(r1 as i32);
}
"#,
        oracle_exit: 1,
        abort: ALL_MATCH,
        unwind: None,
    },
    // `Vec<i32> == &[i32]`. bug -O0/-O1 (false).
    Case {
        name: "vec_eq_slice_ref",
        src: r#"fn main() {
    let mut v: Vec<i32> = Vec::new();
    for x in [1, 2, 3] { v.push(x); }
    let arr = std::hint::black_box([1, 2, 3]);
    let s: &[i32] = &arr;
    let r3 = v == s;            // true
    println!("r3={}", r3);
    std::process::exit(r3 as i32);
}
"#,
        oracle_exit: 1,
        abort: ALL_MATCH,
        unwind: None,
    },
    // `!=` against arrays and a byte-string array. bug -O0; -O1 was refused
    // (a promoted-constant operand).
    Case {
        name: "vec_ne_array",
        src: r#"fn main() {
    let mut v: Vec<i32> = Vec::new();
    for x in [1, 2, 3] { v.push(x); }
    let arr2 = std::hint::black_box([1, 2, 3]);
    let r = v != arr2;          // false
    let mut w: Vec<u8> = Vec::new();
    for x in [7u8, 8] { w.push(x); }
    let r2 = w == [7u8, 8];     // true
    let r3 = w == *b"\x07\x08"; // true
    println!("ne={} r2={} r3={}", r, r2, r3);
    std::process::exit(r as i32 + 2 * r2 as i32 + 4 * r3 as i32);
}
"#,
        oracle_exit: 6,
        abort: ALL_MATCH,
        unwind: None,
    },
    // Array, slice-reference and `!=` forms together. bug -O0/-O1.
    Case {
        name: "vec_eq_cross_type",
        src: r#"fn main() {
    let mut v: Vec<i32> = Vec::new();
    for x in [1, 2, 3] { v.push(x); }
    let arr = std::hint::black_box([1, 2, 3]);
    let arr2 = std::hint::black_box([1, 2, 4]);
    let s: &[i32] = &arr;
    let r1 = v == arr;          // true
    let r2 = v == arr2;         // false
    let r3 = v == s;            // true
    let r4 = v[..] == arr[..];  // true
    let r5 = v != arr2;         // true
    let r = r1 as i32 + 2 * r2 as i32 + 4 * r3 as i32 + 8 * r4 as i32 + 16 * r5 as i32;
    println!("r={}", r); // 29
    std::process::exit(r);
}
"#,
        oracle_exit: 29,
        abort: ALL_MATCH,
        unwind: None,
    },
    // An empty `Vec<i64>` against `[5, 0, 0]`: the array's words read as a
    // header said equal. bug -O0/-O1.
    Case {
        name: "empty_vec_eq_array",
        src: r#"fn main() {
    let v: Vec<i64> = Vec::new();
    let arr = std::hint::black_box([5i64, 0, 0]);
    let r = v == arr; // false
    println!("r={}", r);
    std::process::exit(r as i32);
}
"#,
        oracle_exit: 0,
        abort: ALL_MATCH,
        unwind: None,
    },
    // `== &[u8; 3]`, `== &mut [u8]`, `== [u8]`: refused -O0/-O1 before
    // ([TCG-SSA-071] on the misread operand).
    Case {
        name: "vec_eq_ref_array_and_mut_slice",
        src: r#"fn main() {
    let mut v: Vec<u8> = Vec::new();
    for x in [7u8, 8, 9] { v.push(x); }
    let arr = std::hint::black_box([7u8, 8, 9]);
    let r1 = v == &arr;                 // true
    let mut arr2 = std::hint::black_box([7u8, 8, 0]);
    let r2 = v == &mut arr2[..];        // false
    let r3 = v == arr[..];              // true
    let r4 = v != &arr;                 // false
    let r = r1 as i32 + 2 * r2 as i32 + 4 * r3 as i32 + 8 * r4 as i32;
    println!("r={}", r); // 5
    std::process::exit(r);
}
"#,
        oracle_exit: 5,
        abort: ALL_MATCH,
        unwind: None,
    },
    // CONTROL: `[T] == Vec`, `&[T] == Vec`, `&mut [T] == Vec` never reach
    // the intercept (the self is not a `Vec`). Matched before.
    Case {
        name: "control_vec_on_the_right",
        src: r#"fn main() {
    let mut v: Vec<i32> = Vec::new();
    for x in [1, 2, 3] { v.push(x); }
    let arr = std::hint::black_box([1, 2, 3]);
    let s: &[i32] = &arr;
    let r1 = arr[..] == v;  // true
    let r2 = s == v;        // true
    let mut arr2 = std::hint::black_box([1, 2, 4]);
    let m: &mut [i32] = &mut arr2;
    let r3 = m == v;        // false
    let r4 = s != v;        // false
    let r = r1 as i32 + 2 * r2 as i32 + 4 * r3 as i32 + 8 * r4 as i32;
    println!("r={}", r); // 3
    std::process::exit(r);
}
"#,
        oracle_exit: 3,
        abort: ALL_MATCH,
        unwind: None,
    },
    // CONTROL: `Vec == Vec` and `!=` for `u8`..`u64`, `i8`..`i64`, `f32`,
    // `f64` (NaN, signed zero) keep the intercept. Matched before.
    Case {
        name: "control_vec_eq_vec",
        src: r#"fn main() {
    let k = std::hint::black_box(3u8);
    let mut r = 0u64;
    let mut bit = 1u64;
    macro_rules! case {
        ($t:ty, $a:expr, $b:expr) => {{
            let a: Vec<$t> = $a; let b: Vec<$t> = $b;
            if a == b { r |= bit; } bit <<= 1;
            if a != b { r |= bit; } bit <<= 1;
        }};
    }
    case!(u8, vec![1, k], vec![1, 3]);
    case!(u16, vec![1, k as u16], vec![1, 4]);
    case!(u32, vec![k as u32; 3], vec![3, 3, 3]);
    case!(u64, vec![k as u64], vec![3, 0]);
    case!(i8, vec![-1, k as i8], vec![-1, 3]);
    case!(i16, vec![-(k as i16)], vec![3]);
    case!(i32, vec![-7, k as i32], vec![-7, 3]);
    case!(i64, vec![k as i64], vec![3]);
    case!(f32, vec![k as f32, -0.0], vec![3.0, 0.0]);
    case!(f64, vec![f64::NAN, k as f64], vec![f64::NAN, 3.0]);
    println!("r={}", r);
    std::process::exit((r % 251) as i32);
}
"#,
        oracle_exit: 70,
        abort: ALL_MATCH,
        unwind: None,
    },
    // BOUNDARY: `bool`/`char` elements are not modeled by the intercept and
    // refuse at -O0/-O1 (before and after); -O2/-O3 inline std's body.
    Case {
        name: "boundary_vec_eq_bool_char",
        src: r#"fn main() {
    let k = std::hint::black_box(3u8);
    let a: Vec<bool> = vec![true, k == 3];
    let b: Vec<bool> = vec![true, true];
    let c: Vec<char> = vec!['a', (b'a' + k) as char];
    let d: Vec<char> = vec!['a', 'd'];
    let r = (a == b) as i32 + 2 * (c == d) as i32 + 4 * (c != d) as i32;
    println!("r={r}");
    std::process::exit(r);
}
"#,
        oracle_exit: 3,
        abort: [
            BOOL_ELEMENT_EQ_REFUSAL,
            BOOL_ELEMENT_EQ_REFUSAL,
            Match,
            Match,
        ],
        unwind: None,
    },
];

#[test]
fn call_results_into_memory_backed_fields_reach_the_slot() {
    assert_family(
        "field_results",
        "CORE_VALUES_FIELD_RESULTS",
        FIELD_RESULT_CASES,
    );
}

#[test]
fn vec_float_partial_cmp_writes_the_layout_none_byte() {
    assert_family("partial_cmp", "CORE_VALUES_PARTIAL_CMP", PARTIAL_CMP_CASES);
}

#[test]
fn vec_eq_intercepts_only_a_vec_operand() {
    assert_family("vec_eq", "CORE_VALUES_VEC_EQ", VEC_EQ_CASES);
}
