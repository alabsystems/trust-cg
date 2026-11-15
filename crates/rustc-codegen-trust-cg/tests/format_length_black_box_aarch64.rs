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

// A length printed through `format!`/`println!`/`eprintln!`/`write!` renders
// like LLVM, and `std::hint::black_box` of a `Vec` is the identity it is
// everywhere else.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// LENGTHS. `classify_decoded_arguments` refused every INTEGER placeholder whose
// value depended on a `len` call or a `PtrMetadata` ([TCG-FMT-LEN]), on the
// claim that no such placeholder rendered correctly. The miscompile it was
// added for (2026-07-06, x86-64: `format!("{}#{}", a, a.len())` printed
// `measure#4096`) came from `str::len` being a real -O0 call that took the
// `&str` pair by value, whose by-value-aggregate retype poisoned the caller's
// slot. Two days later that retype was scoped to a call-site temp and
// `str::len` was intercepted; the gate stayed and refused `v.len()`,
// `s.len()`, slice and `&str` lengths, even a length cast or added to.
// MEASURED (2026-10-03, aarch64-apple-darwin): with the gate disabled, 123
// length programs (this file's, m131's reproducers and more) matched LLVM in
// stdout, stderr and exit status in every cell that compiled at -O0..-O3 under
// panic=abort and panic=unwind; none diverged.
//
// FALSIFIED (2026-10-03, the targo-built backend): with the gate restored, the
// length test fails (52 of its 56 cells refused by [TCG-FMT-LEN]; the other
// four are -O2/-O3 cells whose length is an inlined field read the gate never
// saw); with the `black_box` early return removed, the black_box test fails
// (its 12 Vec cells at -O0/-O1 refused by the Vec claim).
//
// BLACK_BOX. `lower_vec_call` recognizes a `Vec` method by the SHAPE of its
// first argument or destination, so the genuine `core::hint::black_box::<Vec<T>>`
// (a real call at -O0/-O1) was claimed and refused as "`Vec::<u32>::black_box`
// is not an intercepted Vec method"; `black_box(&v)` and `black_box(&mut v)`
// likewise. It now reaches the ordinary call path, as `black_box` of a `Box`,
// a `String` or a user `fn id(v: Vec<T>) -> Vec<T>` always did. The
// `Vec<Vec<_>>` and `BTreeMap` rows are refused for reasons owned elsewhere
// (the nested collection image; a map moved through any call, and the map
// interceptors' own black_box claim at -O0/-O1, which `[TCG-MAP-CALLEE]` makes
// by callee identity before the arm-by-name fallback can: `black_box` is a std
// callee taking a modeled map that is not one of the map's inherent methods,
// OD-173); they must refuse by those names or match, never compile and
// diverge, and never name the Vec claim.
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
/// A refusal that names the `Vec` interceptor's claim on `black_box`.
const VEC_BLACK_BOX_CLAIM: &str = "black_box is not an intercepted Vec method";

#[derive(Clone, Copy)]
enum Expect {
    /// Every cell compiles and matches LLVM.
    Match,
    /// Each cell matches LLVM, or is refused with every needle of one of the
    /// alternatives in its diagnostics.
    MatchOrRefuse(&'static [&'static [&'static str]]),
}

struct Program {
    name: &'static str,
    src: &'static str,
    /// The LLVM oracle's stdout and exit code, so a broken oracle cannot pass.
    stdout: &'static str,
    code: i32,
    expect: Expect,
}

const LENGTHS: &[Program] = &[
    Program {
        name: "vec_push_and_truncate",
        src: r#"use std::hint::black_box as bb;
fn main() {
    let mut w = Vec::new();
    for i in 0..5u64 {
        w.push(i);
    }
    let m = w.len() as u64 + 1;
    println!("{}", m);
    w.truncate(bb(2));
    println!("{}", w.len());
}
"#,
        stdout: "6\n2\n",
        code: 0,
        expect: Expect::Match,
    },
    Program {
        name: "vec_pop_and_clear",
        src: r#"fn main() {
    let mut w = vec![1u64, 2, 3];
    w.push(4);
    let _ = w.pop();
    let _ = w.pop();
    println!("{}", w.len());
    w.clear();
    println!("{} {}", w.len(), w.is_empty());
}
"#,
        stdout: "2\n0 true\n",
        code: 0,
        expect: Expect::Match,
    },
    Program {
        name: "vec_extend_and_arithmetic",
        src: r#"fn main() {
    let v = vec![1u32, 2, 3];
    let mut x = vec![1u32];
    x.extend_from_slice(&[4, 5, 6]);
    println!("{}", x.len());
    println!("{} {}", v.len() * 3 - 1, v.len() / 2 + v.len() % 3);
    eprintln!("{}", v.len());
}
"#,
        stdout: "4\n8 1\n",
        code: 0,
        expect: Expect::Match,
    },
    Program {
        name: "vec_casts_retain_branch_loop",
        src: r#"use std::hint::black_box as bb;
fn main() {
    let v = vec![1u32, 2, 3];
    let big = vec![0u8; bb(300usize)];
    println!("{} {} {} {} {}", big.len() as u8, big.len() as i32, big.len() as i64, big.len() as u16, big.len() as i8);
    let mut y = vec![1u32, 2, 3, 4, 5, 6];
    y.retain(|e| e % 2 == 0);
    println!("{}", y.len());
    let k = if bb(true) { v.len() } else { y.len() };
    println!("{k}");
    let mut t = 0u32;
    for i in 0..v.len() {
        t += v[i];
    }
    println!("{} {}", t, v.len());
}
"#,
        stdout: "44 300 300 300 44\n3\n3\n6 3\n",
        code: 0,
        expect: Expect::Match,
    },
    Program {
        name: "string_and_str_lengths",
        src: r#"use std::hint::black_box as bb;
fn main() {
    let s = String::from("hello");
    let n = s.len();
    println!("{n}");
    let n2 = bb(String::from("hi")).len();
    println!("{n2}");
    let mut t = String::from("ab");
    t.push_str("xyz");
    println!("{}", t.len());
    let a: &str = bb("measure");
    println!("{}#{}", a, a.len());
    let k: usize = a.len();
    println!("{}#{}", k, a);
    println!("{}#{}", a, a.len() + bb(0usize));
    let r = s.as_str();
    println!("{}", r.len());
    let lit = "literal";
    println!("{}", lit.len());
    let br: &str = if bb(true) { "trust" } else { "cg" };
    println!("{}", br.len());
    let sub = &s[1..];
    println!("{}", sub.len());
    let h: &str = bb("hello!");
    println!("{} {}", h.bytes().len(), h.as_bytes().len());
    let o = String::from(bb("dynamic"));
    println!("{}", o.len());
}
"#,
        stdout: "5\n2\n5\nmeasure#7\n7#measure\nmeasure#7\n5\n7\n5\n4\n6 6\n7\n",
        code: 0,
        expect: Expect::Match,
    },
    Program {
        name: "slice_lengths",
        src: r#"use std::hint::black_box as bb;
#[inline(never)]
fn slice_len(s: &[u32]) {
    println!("{}", s.len())
}
#[inline(never)]
fn str_len(s: &str) {
    println!("{}", s.len())
}
fn main() {
    let v = vec![1u32, 2, 3, 4, 5];
    slice_len(&v);
    slice_len(&[9u32, 8]);
    slice_len(&v[1..]);
    str_len(bb("abcde"));
    str_len(bb(""));
    let arr = [1u8; 7];
    let sl: &[u8] = &arr;
    println!("{}", sl.len());
    let t: &[u8] = bb(&arr[..]);
    println!("{}", t.len());
    let s = &v[1..4];
    println!("{}", s.len());
    let s2 = &v[bb(2)..];
    println!("{}", s2.len());
    let (l, r) = v.split_at(bb(2));
    println!("{} {}", l.len(), r.len());
    let mut d = std::collections::VecDeque::new();
    d.push_back(1u32);
    d.push_back(2);
    println!("{}", d.len());
}
"#,
        stdout: "5\n2\n4\n5\n0\n7\n7\n3\n3\n2 3\n2\n",
        code: 0,
        expect: Expect::Match,
    },
    // m131's x86-64 reproducers, here on the native host: the formatted
    // `String` is written out and its byte hash is the exit code.
    Program {
        name: "format_into_string",
        src: r#"use std::fmt::Write as _;
use std::hint::black_box as bb;
use std::io::Write as _;
#[inline(never)]
fn hash(s: &str) -> i32 {
    let mut h = 0i32;
    for b in s.as_bytes() {
        h = h.wrapping_mul(31).wrapping_add(*b as i32);
    }
    h & 0x7f
}
#[inline(never)]
fn go(a: &str) -> String {
    format!("<{}>", a.len())
}
fn main() {
    let a: &str = bb("measure");
    let s1 = format!("{}#{}", a, a.len());
    let n: usize = a.len();
    let s2 = format!("{}#{}", n, a);
    let s3 = format!("{}#{}", a, a.len() + bb(0usize));
    let b: &str = bb("hello");
    let s4 = format!("L={}", b.len());
    let s5 = go(bb("measure"));
    let o = String::from(bb("dynamic"));
    let s6 = format!("[{}]", o.len());
    let mut s7 = String::new();
    write!(s7, "n={} m={}", o.len(), bb("ab").len()).unwrap();
    let mut out = std::io::stdout();
    out.write_all(s1.as_bytes()).unwrap();
    out.write_all(s2.as_bytes()).unwrap();
    out.write_all(s3.as_bytes()).unwrap();
    out.write_all(s4.as_bytes()).unwrap();
    out.write_all(s5.as_bytes()).unwrap();
    out.write_all(s6.as_bytes()).unwrap();
    out.write_all(s7.as_bytes()).unwrap();
    let code = hash(&s1) ^ hash(&s2) ^ hash(&s3) ^ hash(&s4) ^ hash(&s5) ^ hash(&s6) ^ hash(&s7);
    std::process::exit(code);
}
"#,
        stdout: "measure#77#measuremeasure#7L=5<7>[7]n=7 m=2",
        code: 94,
        expect: Expect::Match,
    },
    // The review of this change: with [TCG-FMT-LEN] removed, a printed length
    // of a `ChunksExact` cursor read the bridge's private iterator layout at
    // -O2/-O3 (a heap address for `remainder().len()`, `3` printed forever for
    // the loop). The stride iterators now hold std's state (OD-169); these must
    // match at every level.
    Program {
        name: "chunks_exact_remainder_len",
        src: r#"use std::hint::black_box as bb;
fn main() {
    let v = vec![0u8; bb(11usize)];
    let c = v.chunks_exact(4);
    println!("{}", c.remainder().len());
}
"#,
        stdout: "3\n",
        code: 0,
        expect: Expect::Match,
    },
    Program {
        name: "chunks_exact_loop_len",
        src: r#"use std::hint::black_box as bb;
fn main() {
    let v = vec![1u8; bb(11usize)];
    let mut n = 0;
    for c in v.chunks_exact(4) {
        n += c.len();
        println!("{}", c.len());
    }
    println!("{}", n);
}
"#,
        stdout: "4\n4\n8\n",
        code: 0,
        expect: Expect::Match,
    },
];

const BLACK_BOXES: &[Program] = &[
    Program {
        name: "black_box_vec_by_value",
        src: r#"use std::hint::black_box as bb;
fn main() {
    let v = bb(vec![1u32, 2, 3]);
    let (a, b, c) = (v[0], v[1], v[2]);
    println!("{a} {b} {c}");
    let w = vec![4u32, 5, 6];
    let x = bb(w.clone());
    let (d, e, f) = (x[0], x[2], w[1]);
    println!("{d} {e} {f}");
    let mut p = bb(vec![1u32]);
    p.push(2);
    p.push(3);
    let (g, h) = (p[1], p[2]);
    println!("{g} {h} {}", p.len());
    let q = bb(bb(vec![7i64, -2]));
    let (i, j) = (q[0], q[1]);
    println!("{i} {j}");
    let r = core::hint::black_box(vec![200u8, 1]);
    let (k, l) = (r[0], r[1]);
    println!("{k} {l}");
    let s: u32 = bb(vec![1u32, 2, 3]).iter().sum();
    println!("{s}");
}
"#,
        stdout: "1 2 3\n4 6 5\n2 3 3\n7 -2\n200 1\n6\n",
        code: 0,
        expect: Expect::Match,
    },
    Program {
        name: "black_box_vec_references",
        src: r#"use std::hint::black_box as bb;
fn main() {
    let v = vec![1u32, 2, 3];
    let r = bb(&v);
    let x = r[1];
    println!("{x}");
    let mut m = vec![1u32, 2, 3];
    bb(&mut m).push(4);
    let (a, b) = (m[3], m[0]);
    println!("{a} {b} {}", m.len());
}
"#,
        stdout: "2\n4 1 4\n",
        code: 0,
        expect: Expect::Match,
    },
    Program {
        name: "black_box_vec_ownership",
        src: r#"use std::hint::black_box as bb;
#[inline(never)]
fn make(n: u32) -> Vec<u32> {
    let mut v = Vec::new();
    for i in 0..n {
        v.push(i);
    }
    bb(v)
}
#[inline(never)]
fn take(v: Vec<u32>) -> u32 {
    let v = bb(v);
    v[0] + v[1]
}
fn main() {
    let v = make(4);
    let x = v[3];
    println!("{x}");
    let y = take(vec![3u32, 4]);
    println!("{y}");
    let mut w = vec![0u32];
    for i in 1..4u32 {
        w = bb(w);
        w.push(i);
    }
    let (a, n) = (w[3], w.len());
    println!("{a} {n}");
}
"#,
        stdout: "3\n7\n3 4\n",
        code: 0,
        expect: Expect::Match,
    },
    // Already the identity before this fix: a `String`, a `Box`, an `Rc`, a
    // `VecDeque`, and a user fn that only shares the name.
    Program {
        name: "black_box_other_owners",
        src: r#"use std::hint::black_box as bb;
mod user {
    #[inline(never)]
    pub fn black_box(v: Vec<u32>) -> Vec<u32> {
        let mut v = v;
        v.push(9);
        v
    }
}
fn main() {
    let s = bb(String::from("hi"));
    let b = s.as_bytes();
    let (x, y) = (b[0], b[1]);
    println!("{x} {y} {}", s.len());
    let bx = bb(Box::new(5u64));
    let z = *bx + 1;
    println!("{z}");
    let rc = bb(std::rc::Rc::new(5u32));
    let r = *rc;
    println!("{r}");
    let mut d = std::collections::VecDeque::new();
    d.push_back(7u32);
    let d = bb(d);
    let e = d[0];
    println!("{e}");
    let u = user::black_box(vec![1u32]);
    let (a, c) = (u[0], u[1]);
    println!("{a} {c}");
}
"#,
        stdout: "104 105 2\n6\n5\n7\n1 9\n",
        code: 0,
        expect: Expect::Match,
    },
    Program {
        name: "black_box_vec_of_vec",
        src: r#"use std::hint::black_box as bb;
fn main() {
    let v = bb(vec![vec![1u32, 2], vec![3u32]]);
    let (a, b) = (v[0][1], v[1][0]);
    println!("{a} {b}");
}
"#,
        stdout: "2 3\n",
        code: 0,
        expect: Expect::MatchOrRefuse(&[
            &["[TCG-COLLECTION-IMAGE]"],
            &["memory-backed aggregate assignment Rvalue::Cast"],
        ]),
    },
    Program {
        name: "black_box_btreemap",
        src: r#"use std::hint::black_box as bb;
fn main() {
    let mut m = std::collections::BTreeMap::new();
    m.insert(1u64, 10u64);
    m.insert(2, 20);
    let r = bb(&m);
    let x = r.get(&2).copied().unwrap_or(0);
    println!("{x}");
    let m = bb(m);
    let y = m.get(&1).copied().unwrap_or(0);
    println!("{y}");
}
"#,
        stdout: "20\n10\n",
        code: 0,
        expect: Expect::MatchOrRefuse(&[
            &["BTreeMap local", "assigned from a non-aggregate rvalue"],
            &["BTreeMap::<u64, u64>::black_box is not an intercepted BTreeMap method"],
            &[
                "[TCG-MAP-CALLEE]",
                "`std::hint::black_box` takes a BTreeMap",
            ],
        ]),
    },
];

#[derive(Debug, PartialEq, Eq)]
struct Ending {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
    stderr: String,
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "tcg_format_length_black_box_{stem}_{}",
        std::process::id()
    ));
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

/// Every (program, opt, panic) cell, judged against its LLVM oracle. Returns
/// `(matched, refused, failures)`.
fn judge(programs: &[Program], stem: &str) -> (usize, usize, Vec<String>) {
    let backend = backend_artifact_support::current_test_backend();
    // Built once on the test's own thread, so its knob trace lands in this
    // test's captured output.
    let knobs = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    let dir = workdir(stem);
    let cells: Vec<(&Program, u32, &str)> = programs
        .iter()
        .flat_map(|p| {
            OPTS.iter()
                .flat_map(move |&o| PANICS.iter().map(move |&k| (p, o, k)))
        })
        .collect();
    let next = Mutex::new(0usize);
    let results: Mutex<Vec<(usize, Result<(), String>, bool)>> = Mutex::new(Vec::new());
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
                    let verdict = judge_cell(&dir, program, opt, panic, &backend, &knobs);
                    results.lock().unwrap().push((index, verdict.0, verdict.1));
                }
            });
        }
    });
    let _ = std::fs::remove_dir_all(&dir);
    let mut results = results.into_inner().unwrap();
    results.sort_by_key(|(index, ..)| *index);
    let (mut matched, mut refused, mut failures) = (0, 0, Vec::new());
    for (_, verdict, was_refused) in results {
        match verdict {
            Ok(()) if was_refused => refused += 1,
            Ok(()) => matched += 1,
            Err(failure) => failures.push(failure),
        }
    }
    (matched, refused, failures)
}

/// One cell: `(Ok(()), refused?)` or `(Err(why), _)`.
fn judge_cell(
    dir: &Path,
    program: &Program,
    opt: u32,
    panic: &str,
    backend: &Path,
    knobs: &str,
) -> (Result<(), String>, bool) {
    let cell = format!("{} -O{opt} -Cpanic={panic}", program.name);
    let oracle = match compile_and_run(dir, program, opt, panic, None) {
        Ok(oracle) => oracle,
        Err(stderr) => {
            return (
                Err(format!("{cell}: LLVM failed to compile: {stderr}")),
                false,
            );
        }
    };
    let expected = (Some(program.code), None, program.stdout);
    if (oracle.code, oracle.signal, oracle.stdout.as_str()) != expected {
        return (
            Err(format!(
                "{cell}: the LLVM oracle is not the pinned run: {oracle:?}"
            )),
            false,
        );
    }
    match (
        compile_and_run(dir, program, opt, panic, Some((backend, knobs))),
        program.expect,
    ) {
        (Ok(bridge), _) if bridge == oracle => (Ok(()), false),
        (Ok(bridge), _) => (
            Err(format!(
                "{cell}: compiled and DIVERGES -- LLVM {oracle:?}, trust-cg {bridge:?}"
            )),
            false,
        ),
        (Err(stderr), _) if stderr.contains(VEC_BLACK_BOX_CLAIM) => (
            Err(format!(
                "{cell}: the Vec interceptor claimed std's black_box: <<<{stderr}>>>"
            )),
            true,
        ),
        (Err(stderr), Expect::Match) => (Err(format!("{cell}: refused: <<<{stderr}>>>")), true),
        (Err(stderr), Expect::MatchOrRefuse(alternatives)) => {
            if alternatives
                .iter()
                .any(|needles| needles.iter().all(|needle| stderr.contains(needle)))
            {
                (Ok(()), true)
            } else {
                (
                    Err(format!(
                        "{cell}: refused, but not for a named reason {alternatives:?}: \
                         <<<{stderr}>>>"
                    )),
                    true,
                )
            }
        }
    }
}

#[test]
fn length_placeholders_render_like_llvm_aarch64() {
    darwin_native::require("format_length_black_box_aarch64", &[]);
    let (matched, refused, failures) = judge(LENGTHS, "len");
    assert!(
        failures.is_empty(),
        "{} length cell(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    assert_eq!(refused, 0);
    eprintln!(
        "FORMAT_LENGTH programs={} cells={matched} matched={matched} opts=0,1,2,3 \
         strategies=abort,unwind",
        LENGTHS.len()
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn std_black_box_of_a_collection_matches_llvm_aarch64() {
    darwin_native::require("format_length_black_box_aarch64", &[]);
    let (matched, refused, failures) = judge(BLACK_BOXES, "bb");
    assert!(
        failures.is_empty(),
        "{} black_box cell(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    let must_match = BLACK_BOXES
        .iter()
        .filter(|p| matches!(p.expect, Expect::Match))
        .count()
        * OPTS.len()
        * PANICS.len();
    // The must-match rows are fixed; how many of the others match or refuse by
    // name moves with lanes that own those refusals, so it is reported apart.
    eprintln!(
        "STD_BLACK_BOX programs={} cells={} must_match={must_match} opts=0,1,2,3 \
         strategies=abort,unwind",
        BLACK_BOXES.len(),
        matched + refused
    );
    eprintln!(
        "STD_BLACK_BOX_OTHERS matched={} refused_by_name={refused}",
        matched - must_match
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
