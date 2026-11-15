#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: the five slice stride iterators (`Windows`, `Chunks`,
// `ChunksExact`, `RChunks`, `RChunksExact`) are represented in RUSTC'S OWN
// LAYOUT, so a value is the same bytes whoever builds it and whoever reads it.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE CLAIM. The bridge's intercepted constructor writes std's own state
// (`Windows { v, size }`, `Chunks`/`RChunks { v, chunk_size }`,
// `ChunksExact`/`RChunksExact { v, rem, chunk_size }`, with `ChunksExact::v`
// truncated to whole chunks and `rem` the `len % n` tail or head) at the offsets
// rustc's layout gives those fields (`StrideIterLayout`, certified per instance
// by `slice_stride_iter_layout`), and its intercepted `next` and `remainder`
// read and update exactly those fields with std's transitions. Every OTHER
// producer and consumer — std's inlined constructor and methods at `-O2`/`-O3`
// or under `-Zinline-mir=yes`, std's real `count`/`len`/`nth`/`last`/
// `next_back`/`fold`/`Zip` bodies, an LLVM-compiled caller that builds or
// receives the iterator, a reified `Iterator::next` — therefore sees the same
// bytes.
//
// THE DEFECT THIS REPLACES (K1). Until 2026-10-02 the bridge kept a private
// cursor `{ ptr@0, end@8, n@16 }` (+ `{ rem_data@24, rem_len@32 }`). At `-O2`/
// `-O3` the `chunks_exact` CALL survives inlining while `count`/`next` are
// inlined into the caller as field projections, so std read the cursor's `end`
// POINTER as `v`'s length: `chunks_exact(256).count()` over 1000 bytes returned
// about 18.7 million, then SIGABRT, and the row loop died with SIGBUS
// (`benchmarks/oracles/hunt` K1/K1s). The interim fix refused those bodies
// (`[TCG-STRIDE-ITER-INLINE]`, `[TCG-STRIDE-ITER-METHOD]`); both are now
// withdrawn under the certificate, and every row below must MATCH.
//
// THE GATE, per configuration (element type x opt level x `-Zinline-mir` x
// build mode). Each configuration builds ONE library holding every shape for
// that element type, plus a driver:
//   * split: the library by the bridge, the driver by LLVM (the census-lane
//     shape that found K1, and the LLVM-built-iterator / returned-to-LLVM
//     crossings);
//   * whole: the library and the driver in one crate, every function by the
//     bridge. This driver reads no `argv` (the bridge refuses a `String`
//     argument image for reasons unrelated to stride iterators): it runs every
//     non-panicking case in one process and ends with one zero-stride case
//     (one kind per element type, all five kinds across the six types).
// The LLVM oracle builds the same sources with no backend. Every case must
// produce exactly the oracle's stdout and exit status (a signal included: the
// `zero_*` cases build an iterator with a zero stride, which std must abort
// on). A refusal, a different output, a signal, a timeout or an ICE fails.
// The oracle is asserted on every case first, so a row cannot pass vacuously.
//
// SHAPES, for each of the five kinds: a `for` loop; a `while let` over `next`;
// `next_back` to exhaustion; alternating `next`/`next_back`; `nth(0/1/2/5)`
// then `next`; `count`; `len` then `size_hint` after a `next`; `last`; `fold`;
// `map(len).sum()`; `rev()`; `enumerate().skip(1).take(4)`; `zip` with another
// stride iterator (`chunks_exact(n + 1)`); a fn pointer to `Iterator::next`; an
// iterator built by the LLVM driver and passed in by value (`consume`) or by
// `&mut` (`step`); and one built by the library and returned to the LLVM
// driver (`make`). Plus `remainder()` before, during and after iteration for
// the two `*_exact` kinds. Inputs: lengths 0 (empty), 1, 7, 100, 1000; strides
// 1..=len+1 for len <= 7 (so every window size), else 1, 3, 10, 256 (not
// dividing 1000), len, len + 1. Elements: u8, u16, u32, u64, f64 and the
// two-field `(u8, u32)` (which the bridge does not intercept: std's bodies run
// throughout; its terminals, `zip` and adapters take std's real bodies as a
// stride iterator in std's representation, `slice_stride_iter_state_is_std`).
//
// HOST-NATIVE: no `--target` is passed. The bridge side passes `no-proof-certs`
// for the reason `fat_thin_cast_differential.rs` gives: with certificates on,
// AArch64 objects stop at `[TCG-PROOF-465]` after lowering and would pin
// nothing. Evidence boundary: native differential runs on this host, not a
// proof.

use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output, Stdio};
use std::time::{Duration, Instant};

/// One case in its own process (split mode, the K1 rows).
const RUN_TIMEOUT: Duration = Duration::from_secs(30);
/// The whole-program driver runs every case in one process, so a hang is judged
/// against a longer bound.
const WHOLE_RUN_TIMEOUT: Duration = Duration::from_secs(300);

/// `(method, type)` for the five modeled stride iterators.
const KINDS: [(&str, &str); 5] = [
    ("windows", "Windows"),
    ("chunks", "Chunks"),
    ("chunks_exact", "ChunksExact"),
    ("rchunks", "RChunks"),
    ("rchunks_exact", "RChunksExact"),
];

/// Every per-kind shape (`<kind>_<shape>` is both the library function and the
/// driver's case name).
const SHAPES: [&str; 17] = [
    "for",
    "next",
    "next_back",
    "mixed",
    "nth",
    "count",
    "len",
    "last",
    "fold",
    "sum",
    "rev",
    "enum",
    "zip",
    "fnptr",
    "consume",
    "make",
    "step",
];

struct Elem {
    name: &'static str,
    ty: &'static str,
    /// `fn h(x: E) -> u64` body.
    hash: &'static str,
    /// The `i`-th element of the input buffer.
    init: &'static str,
}

const ELEMS: [Elem; 6] = [
    Elem {
        name: "u8",
        ty: "u8",
        hash: "x as u64",
        init: "(i % 251) as u8",
    },
    Elem {
        name: "u16",
        ty: "u16",
        hash: "x as u64",
        init: "(i * 7 % 65521) as u16",
    },
    Elem {
        name: "u32",
        ty: "u32",
        hash: "x as u64",
        init: "(i as u64 * 2654435761 % 4294967291) as u32",
    },
    Elem {
        name: "u64",
        ty: "u64",
        hash: "x",
        init: "(i as u64).wrapping_mul(0x9E3779B97F4A7C15)",
    },
    Elem {
        name: "f64",
        ty: "f64",
        hash: "x.to_bits()",
        init: "(i as f64) * 1.5 - 3.25",
    },
    Elem {
        name: "pair",
        ty: "(u8, u32)",
        hash: "(x.0 as u64) << 32 | x.1 as u64",
        init: "((i % 256) as u8, (i * 31) as u32)",
    },
];

#[derive(Clone, Copy, Debug, PartialEq)]
enum Mode {
    /// The library by the bridge, the driver by LLVM.
    Split,
    /// One crate, every function by the bridge.
    Whole,
}

fn lib_source(elem: &Elem) -> String {
    let mut s = format!(
        "pub type E = {ty};\n\
         #[inline(never)] pub fn h(x: E) -> u64 {{ {hash} }}\n\
         #[inline(never)] pub fn hs(c: &[E]) -> u64 {{\n\
         \x20   let mut s = c.len() as u64 * 1000003;\n\
         \x20   if let Some(&x) = c.first() {{ s = s.wrapping_mul(31).wrapping_add(h(x)); }}\n\
         \x20   if let Some(&x) = c.last() {{ s = s.wrapping_mul(37).wrapping_add(h(x)); }}\n\
         \x20   s\n\
         }}\n",
        ty = elem.ty,
        hash = elem.hash,
    );
    for (k, t) in KINDS {
        s.push_str(&format!(
            r#"
#[inline(never)] pub fn {k}_for(v: &[E], n: usize) -> u64 {{
    let mut s = 0u64;
    for c in v.{k}(n) {{ s = s.wrapping_mul(1000003).wrapping_add(hs(c)); }}
    s
}}
#[inline(never)] pub fn {k}_next(v: &[E], n: usize) -> u64 {{
    let mut it = v.{k}(n);
    let mut s = 0u64;
    while let Some(c) = it.next() {{ s = s.wrapping_mul(1000003).wrapping_add(hs(c)); }}
    s ^ (it.next().is_none() as u64)
}}
#[inline(never)] pub fn {k}_next_back(v: &[E], n: usize) -> u64 {{
    let mut it = v.{k}(n);
    let mut s = 0u64;
    while let Some(c) = it.next_back() {{ s = s.wrapping_mul(1000003).wrapping_add(hs(c)); }}
    s
}}
#[inline(never)] pub fn {k}_mixed(v: &[E], n: usize) -> u64 {{
    let mut it = v.{k}(n);
    let mut s = 0u64;
    loop {{
        match it.next() {{ Some(c) => s = s.wrapping_mul(7).wrapping_add(hs(c)), None => break }}
        match it.next_back() {{ Some(c) => s = s.wrapping_mul(11).wrapping_add(hs(c)), None => break }}
    }}
    s
}}
#[inline(never)] pub fn {k}_nth(v: &[E], n: usize) -> u64 {{
    let mut s = 0u64;
    for k in [0usize, 1, 2, 5] {{
        let mut it = v.{k}(n);
        s = s.wrapping_mul(31).wrapping_add(it.nth(k).map_or(99, hs));
        s = s.wrapping_mul(31).wrapping_add(it.next().map_or(77, hs));
    }}
    s
}}
#[inline(never)] pub fn {k}_count(v: &[E], n: usize) -> u64 {{
    v.{k}(n).count() as u64
}}
#[inline(never)] pub fn {k}_len(v: &[E], n: usize) -> u64 {{
    let mut it = v.{k}(n);
    let a = it.len() as u64;
    it.next();
    let (lo, hi) = it.size_hint();
    a * 1000 + lo as u64 * 10 + hi.map_or(7, |x| x as u64)
}}
#[inline(never)] pub fn {k}_last(v: &[E], n: usize) -> u64 {{
    v.{k}(n).last().map_or(5, hs)
}}
#[inline(never)] pub fn {k}_fold(v: &[E], n: usize) -> u64 {{
    v.{k}(n).fold(1u64, |a, c| a.wrapping_mul(13).wrapping_add(hs(c)))
}}
#[inline(never)] pub fn {k}_sum(v: &[E], n: usize) -> u64 {{
    v.{k}(n).map(|c| c.len() as u64).sum::<u64>()
}}
#[inline(never)] pub fn {k}_rev(v: &[E], n: usize) -> u64 {{
    let mut s = 0u64;
    for c in v.{k}(n).rev() {{ s = s.wrapping_mul(1000003).wrapping_add(hs(c)); }}
    s
}}
#[inline(never)] pub fn {k}_enum(v: &[E], n: usize) -> u64 {{
    let mut s = 0u64;
    for (i, c) in v.{k}(n).enumerate().skip(1).take(4) {{
        s = s.wrapping_mul(1000003).wrapping_add(hs(c) ^ i as u64);
    }}
    s
}}
#[inline(never)] pub fn {k}_zip(v: &[E], n: usize) -> u64 {{
    let mut s = 0u64;
    for (a, b) in v.{k}(n).zip(v.chunks_exact(n + 1)) {{
        s = s.wrapping_mul(1000003).wrapping_add(hs(a) ^ hs(b));
    }}
    s
}}
#[inline(never)] pub fn {k}_fnptr<'a>(v: &'a [E], n: usize) -> u64 {{
    let f: fn(&mut core::slice::{t}<'a, E>) -> Option<&'a [E]> = Iterator::next;
    let f = core::hint::black_box(f);
    let mut it = v.{k}(n);
    let mut s = 0u64;
    while let Some(c) = f(&mut it) {{ s = s.wrapping_mul(1000003).wrapping_add(hs(c)); }}
    s
}}
#[inline(never)] pub fn {k}_consume(it: core::slice::{t}<'_, E>) -> u64 {{
    let mut s = 0u64;
    for c in it {{ s = s.wrapping_mul(1000003).wrapping_add(hs(c)); }}
    s
}}
#[inline(never)] pub fn {k}_make(v: &[E], n: usize) -> core::slice::{t}<'_, E> {{
    v.{k}(n)
}}
#[inline(never)] pub fn {k}_step(it: &mut core::slice::{t}<'_, E>) -> u64 {{
    it.next().map_or(3, hs)
}}
"#
        ));
    }
    for k in ["chunks_exact", "rchunks_exact"] {
        s.push_str(&format!(
            r#"
#[inline(never)] pub fn {k}_remainder(v: &[E], n: usize) -> u64 {{
    let mut it = v.{k}(n);
    let a = hs(it.remainder());
    it.next();
    let b = hs(it.remainder());
    while it.next().is_some() {{}}
    a.wrapping_mul(31).wrapping_add(b).wrapping_mul(31).wrapping_add(hs(it.remainder()))
}}
"#
        ));
    }
    s
}

/// Every driver case: `<kind>_<shape>`, the two `remainder` cases, and one
/// `zero_<kind>` (a zero stride) per kind.
fn cases() -> Vec<String> {
    let mut out = Vec::new();
    for (k, _) in KINDS {
        for shape in SHAPES {
            out.push(format!("{k}_{shape}"));
        }
    }
    out.push("chunks_exact_remainder".to_owned());
    out.push("rchunks_exact_remainder".to_owned());
    for (k, _) in KINDS {
        out.push(format!("zero_{k}"));
    }
    out
}

/// The driver expression that computes case `case`'s `u64` for input `v`/`n`.
fn case_call(case: &str) -> String {
    if let Some(k) = case.strip_prefix("zero_") {
        // A zero stride: std panics in the constructor, which must abort.
        format!("klib::{k}_for(black_box(v), black_box(0))")
    } else if let Some(k) = case.strip_suffix("_consume") {
        format!("klib::{case}(black_box(v).{k}(black_box(n)))")
    } else if case.ends_with("_make") {
        format!(
            "{{ let mut s = 0u64; for x in klib::{case}(black_box(v), black_box(n)) \
             {{ s = s.wrapping_mul(1000003).wrapping_add(klib::hs(x)); }} s }}"
        )
    } else if let Some(k) = case.strip_suffix("_step") {
        format!(
            "{{ let mut it = black_box(v).{k}(black_box(n)); \
             let a = klib::{case}(&mut it); let b = klib::{case}(&mut it); \
             let mut s = a.wrapping_mul(31).wrapping_add(b); \
             for x in it {{ s = s.wrapping_mul(1000003).wrapping_add(klib::hs(x)); }} s }}"
        )
    } else {
        format!("klib::{case}(black_box(v), black_box(n))")
    }
}

/// The input buffer and the stride table shared by both drivers. Fixed arrays,
/// no collected `Vec`: the whole-program driver is compiled by the bridge too.
fn driver_prelude(elem: &Elem) -> String {
    format!(
        r#"use std::hint::black_box;
fn sizes(len: usize) -> &'static [usize] {{
    match len {{
        0 => &[1],
        1 => &[1, 2],
        7 => &[1, 2, 3, 4, 5, 6, 7, 8],
        100 => &[1, 3, 10, 256, 100, 101],
        _ => &[1, 3, 10, 256, 1000, 1001],
    }}
}}
fn input() -> [klib::E; 1000] {{
    let mut all: [klib::E; 1000] = [Default::default(); 1000];
    let mut i = 0usize;
    while i < 1000 {{
        all[i] = {init};
        i += 1;
    }}
    all
}}
"#,
        init = elem.init,
    )
}

/// The split-mode driver (compiled by LLVM): the case is `argv[1]`, run in its
/// own process, one `len= n= r=` line per input row.
fn split_main_source(elem: &Elem) -> String {
    let mut arms = String::new();
    for case in cases() {
        arms.push_str(&format!(
            "                \"{case}\" => {},\n",
            case_call(&case)
        ));
    }
    format!(
        r#"{prelude}fn main() {{
    let args: Vec<String> = std::env::args().collect();
    let which = args.get(1).map(String::as_str).unwrap_or("");
    let all = input();
    for &len in &[0usize, 1, 7, 100, 1000] {{
        for &n in sizes(len) {{
            let v: &[klib::E] = &all[..len];
            let r: u64 = match which {{
{arms}                _ => std::process::exit(2),
            }};
            println!("len={{}} n={{}} r={{}}", len, n, r);
        }}
    }}
}}
"#,
        prelude = driver_prelude(elem),
    )
}

/// The zero-stride case the whole-program driver ends with (one kind per element
/// type, so the matrix covers all five).
fn whole_zero_case(elem: &Elem) -> String {
    let index = ELEMS.iter().position(|e| e.name == elem.name).unwrap_or(0);
    format!("zero_{}", KINDS[index % KINDS.len()].0)
}

/// The whole-program driver (compiled by the bridge with the library). It reads
/// no `argv`: a `String` argument image is refused by the bridge
/// (`[TCG-COLLECTION-IMAGE]`, unrelated to stride iterators), so every
/// non-panicking case runs in sequence, each row printed as `c=<case index>
/// len= n= r=`, and the program ends with one zero-stride case, which must abort
/// exactly as LLVM's build does after the same output.
fn whole_main_source(elem: &Elem) -> String {
    let mut blocks = String::new();
    for (index, case) in cases().iter().enumerate() {
        if case.starts_with("zero_") {
            continue;
        }
        blocks.push_str(&format!(
            "    for &len in &[0usize, 1, 7, 100, 1000] {{\n\
             \x20       for &n in sizes(len) {{\n\
             \x20           let v: &[klib::E] = &all[..len];\n\
             \x20           let r: u64 = {call};\n\
             \x20           emit({index}, len, n, r);\n\
             \x20       }}\n\
             \x20   }}\n",
            call = case_call(case),
        ));
    }
    format!(
        "{prelude}fn main() {{\n\
         \x20   let all = input();\n\
         {blocks}\
         \x20   let v: &[klib::E] = &all[..7];\n\
         \x20   let n = 1usize;\n\
         \x20   let _ = n;\n\
         \x20   let r: u64 = {zero};\n\
         \x20   emit(u64::MAX, 0, 0, r);\n\
         }}\n\
         // Every row is printed by one non-inlined function, so no `println!`\n\
         // argument is derived from a slice length in the caller after MIR\n\
         // inlining (the bridge refuses that `format!` shape, `[TCG-FMT-LEN]`).\n\
         #[inline(never)]\n\
         fn emit(c: u64, len: usize, n: usize, r: u64) {{\n\
         \x20   println!(\"c={{}} len={{}} n={{}} r={{}}\", c, len, n, r);\n\
         }}\n",
        prelude = driver_prelude(elem),
        zero = case_call(&whole_zero_case(elem)),
    )
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_stride_layout_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn compiler(opt: &str, inline_mir: bool, backend: Option<&Path>) -> Command {
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["-Cpanic=abort", "-Ccodegen-units=1"]);
    cmd.arg(format!("-Copt-level={opt}"));
    cmd.arg(if inline_mir {
        "-Zinline-mir=yes"
    } else {
        "-Zinline-mir=no"
    });
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd
}

fn checked(mut cmd: Command) -> Result<(), String> {
    let output = cmd.output().expect("spawn the compiler");
    if output.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

/// Build one configuration's program; `backend` is `None` for the LLVM oracle.
/// `Err` carries the compiler's stderr.
fn build(
    dir: &Path,
    elem: &Elem,
    opt: &str,
    inline_mir: bool,
    mode: Mode,
    backend: Option<&Path>,
) -> Result<PathBuf, String> {
    std::fs::create_dir_all(dir).expect("create build dir");
    let lib = lib_source(elem);
    let main = match mode {
        Mode::Split => split_main_source(elem),
        Mode::Whole => whole_main_source(elem),
    };
    let bin = dir.join("prog");
    match mode {
        Mode::Split => {
            let src = dir.join("klib.rs");
            std::fs::write(&src, lib).expect("write library source");
            let rlib = dir.join("libklib.rlib");
            let mut cmd = compiler(opt, inline_mir, backend);
            cmd.args(["--crate-type", "rlib", "--crate-name", "klib"]);
            cmd.arg("-o").arg(&rlib).arg(&src);
            checked(cmd)?;
            let main_src = dir.join("kmain.rs");
            std::fs::write(&main_src, main).expect("write driver source");
            let mut cmd = compiler(opt, inline_mir, None);
            cmd.args(["--crate-type", "bin", "--crate-name", "kmain"]);
            let mut extern_arg = std::ffi::OsString::from("klib=");
            extern_arg.push(&rlib);
            cmd.arg("--extern").arg(extern_arg);
            cmd.arg("-o").arg(&bin).arg(&main_src);
            checked(cmd)
                .unwrap_or_else(|e| panic!("the LLVM-compiled driver did not build: <<<{e}>>>"));
        }
        Mode::Whole => {
            let src = dir.join("whole.rs");
            std::fs::write(
                &src,
                format!("#[allow(dead_code)]\nmod klib {{\n{lib}\n}}\n{main}"),
            )
            .expect("write program source");
            let mut cmd = compiler(opt, inline_mir, backend);
            cmd.args(["--crate-type", "bin", "--crate-name", "whole"]);
            cmd.arg("-o").arg(&bin).arg(&src);
            checked(cmd)?;
        }
    }
    Ok(bin)
}

/// Run `bin` with the case name as its argument (none when `case` is empty).
/// stdout and stderr are drained on their own threads while the child runs: the
/// whole-program driver prints tens of kilobytes, more than a pipe buffers, and a
/// child blocked on a full pipe would otherwise look like a hang.
fn run_with_timeout(bin: &Path, case: &str, timeout: Duration) -> Option<Output> {
    use std::io::Read;
    let mut cmd = Command::new(bin);
    if !case.is_empty() {
        cmd.arg(case);
    }
    let mut child = cmd
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn the compiled program");
    let drain = |pipe: Option<Box<dyn Read + Send>>| {
        std::thread::spawn(move || {
            let mut bytes = Vec::new();
            if let Some(mut pipe) = pipe {
                let _ = pipe.read_to_end(&mut bytes);
            }
            bytes
        })
    };
    let stdout = drain(
        child
            .stdout
            .take()
            .map(|p| Box::new(p) as Box<dyn Read + Send>),
    );
    let stderr = drain(
        child
            .stderr
            .take()
            .map(|p| Box::new(p) as Box<dyn Read + Send>),
    );
    let start = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().expect("poll the compiled program") {
            break Some(status);
        }
        if start.elapsed() >= timeout {
            child.kill().expect("kill the timed-out program");
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(Duration::from_millis(5));
    };
    let stdout = stdout.join().expect("stdout reader");
    let stderr = stderr.join().expect("stderr reader");
    status.map(|status| Output {
        status,
        stdout,
        stderr,
    })
}

/// `(exit code, signal)`: a panic under `panic=abort` is a signal, not a code.
fn status_key(status: ExitStatus) -> (Option<i32>, Option<i32>) {
    use std::os::unix::process::ExitStatusExt;
    (status.code(), status.signal())
}

/// Every `[TCG-...]` code in `stderr`.
fn refusal_codes(stderr: &str) -> Vec<String> {
    let mut codes = Vec::new();
    let mut rest = stderr;
    while let Some(start) = rest.find("[TCG-") {
        let tail = &rest[start + 1..];
        let Some(end) = tail.find(']') else {
            break;
        };
        codes.push(tail[..end].to_owned());
        rest = &tail[end..];
    }
    codes.sort();
    codes.dedup();
    codes
}

/// Run one configuration; returns the failures (empty when every case matched).
fn check_config(dylib: &Path, elem: &Elem, opt: &str, inline_mir: bool, mode: Mode) -> Vec<String> {
    let label = format!(
        "{}@O{opt}/inline-mir={}/{mode:?}",
        elem.name,
        if inline_mir { "yes" } else { "no" }
    );
    let dir = workdir(&format!(
        "{}_O{opt}_{}_{mode:?}",
        elem.name,
        if inline_mir { "inl" } else { "noinl" }
    ));
    let oracle = build(&dir.join("llvm"), elem, opt, inline_mir, mode, None)
        .unwrap_or_else(|e| panic!("{label}: the LLVM oracle did not build: <<<{e}>>>"));
    let bridge = match build(
        &dir.join("bridge"),
        elem,
        opt,
        inline_mir,
        mode,
        Some(dylib),
    ) {
        Ok(bin) => bin,
        Err(stderr) => {
            assert!(
                !stderr.contains("internal compiler error") && !stderr.contains("panicked at"),
                "{label}: the bridge crashed instead of compiling: <<<{stderr}>>>"
            );
            return vec![format!(
                "{label}: REFUSED (codes {:?}); every shape must compile: <<<{}>>>",
                refusal_codes(&stderr),
                &stderr[..stderr.len().min(6000)]
            )];
        }
    };
    let mut failures = Vec::new();
    if mode == Mode::Whole {
        let expected = run_with_timeout(&oracle, "", WHOLE_RUN_TIMEOUT)
            .unwrap_or_else(|| panic!("{label}: the LLVM oracle did not finish"));
        let expected_stdout = String::from_utf8_lossy(&expected.stdout).into_owned();
        assert!(
            !expected.status.success()
                && expected_stdout.lines().count() >= 20 * (cases().len() - KINDS.len()),
            "{label}: the LLVM oracle must print every case's rows and then abort on its \
             zero stride; status {:?}, {} lines",
            expected.status,
            expected_stdout.lines().count()
        );
        match run_with_timeout(&bridge, "", WHOLE_RUN_TIMEOUT) {
            None => failures.push(format!(
                "{label}: HANG (did not finish in {WHOLE_RUN_TIMEOUT:?})"
            )),
            Some(got) => {
                let got_stdout = String::from_utf8_lossy(&got.stdout).into_owned();
                if (status_key(got.status), got_stdout.as_str())
                    != (status_key(expected.status), expected_stdout.as_str())
                {
                    let all_cases = cases();
                    let first_diff = got_stdout
                        .lines()
                        .zip(expected_stdout.lines())
                        .find(|(g, e)| g != e)
                        .map(|(g, e)| format!("bridge `{g}` vs LLVM `{e}`"))
                        .unwrap_or_else(|| {
                            format!(
                                "{} vs {} lines",
                                got_stdout.lines().count(),
                                expected_stdout.lines().count()
                            )
                        });
                    failures.push(format!(
                        "{label}: bridge {:?} vs LLVM {:?}; first difference: {first_diff} \
                         (case `c=<i>` is cases()[i]: {:?}); stderr <<<{}>>>",
                        status_key(got.status),
                        status_key(expected.status),
                        all_cases,
                        String::from_utf8_lossy(&got.stderr)
                    ));
                }
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
        return failures;
    }
    for case in cases() {
        let expected = run_with_timeout(&oracle, &case, RUN_TIMEOUT)
            .unwrap_or_else(|| panic!("{label} {case}: the LLVM oracle did not finish"));
        let expected_stdout = String::from_utf8_lossy(&expected.stdout).into_owned();
        if case.starts_with("zero_") {
            assert!(
                !expected.status.success(),
                "{label} {case}: std must abort on a zero stride: {:?}",
                expected.status
            );
        } else {
            assert!(
                expected.status.success() && expected_stdout.lines().count() >= 20,
                "{label} {case}: the LLVM oracle must print every input row and exit 0; \
                 status {:?}, stdout <<<{expected_stdout}>>>",
                expected.status
            );
        }
        let Some(got) = run_with_timeout(&bridge, &case, RUN_TIMEOUT) else {
            failures.push(format!(
                "{label} {case}: HANG (did not finish in {RUN_TIMEOUT:?})"
            ));
            continue;
        };
        let got_stdout = String::from_utf8_lossy(&got.stdout).into_owned();
        if (status_key(got.status), got_stdout.as_str())
            != (status_key(expected.status), expected_stdout.as_str())
        {
            failures.push(format!(
                "{label} {case}: bridge {:?} <<<{}>>> vs LLVM {:?} <<<{}>>>; stderr <<<{}>>>",
                status_key(got.status),
                &got_stdout[..got_stdout.len().min(400)],
                status_key(expected.status),
                &expected_stdout[..expected_stdout.len().min(400)],
                String::from_utf8_lossy(&got.stderr)
            ));
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    failures
}

/// The full matrix for one element type: O0-O3 x `-Zinline-mir=no/yes` x split
/// and whole-program.
fn check_elem(name: &str) {
    if toolchain_support::skip_without_backend_knobs(&format!("stride_layout_{name}")) {
        return;
    }
    let elem = ELEMS
        .iter()
        .find(|e| e.name == name)
        .expect("a known element type");
    let dylib = backend_artifact_support::current_test_backend();
    let mut failures = Vec::new();
    let mut configs = 0;
    for mode in [Mode::Split, Mode::Whole] {
        for opt in ["0", "1", "2", "3"] {
            for inline_mir in [false, true] {
                configs += 1;
                failures.extend(check_config(&dylib, elem, opt, inline_mir, mode));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{name}: {} of {configs} configurations x {} cases failed. A stride iterator's \
         state was read under another layout, or a shape is refused; do not relax this \
         assertion — fix the layout or the lowering:\n{}",
        failures.len(),
        cases().len(),
        failures.join("\n")
    );
    eprintln!(
        "stride layout {name}: {configs} configurations x {} cases MATCHED LLVM",
        cases().len()
    );
}

#[test]
fn stride_layout_matches_llvm_u8() {
    check_elem("u8");
}

#[test]
fn stride_layout_matches_llvm_u16() {
    check_elem("u16");
}

#[test]
fn stride_layout_matches_llvm_u32() {
    check_elem("u32");
}

#[test]
fn stride_layout_matches_llvm_u64() {
    check_elem("u64");
}

#[test]
fn stride_layout_matches_llvm_f64() {
    check_elem("f64");
}

#[test]
fn stride_layout_matches_llvm_u8_u32_pair() {
    check_elem("pair");
}

/// K1 and K1s (`benchmarks/oracles/hunt`, `p0_chunks_exact[_kernel]`) verbatim:
/// `chunks_exact(w).count()` and a row-sum kernel over `chunks_exact(w)`, widths
/// dividing and not dividing 1000. Before the layout migration: O2/O3 returned
/// ~18.7 million rows then SIGABRT (`nrows`) and SIGBUS (`kernel`); with the
/// interim refusal, REFUSED. Now: MATCH at O0-O3, `-Zinline-mir=no/yes`, split and
/// whole-program.
#[test]
fn k1_chunks_exact_rows_match_llvm() {
    if toolchain_support::skip_without_backend_knobs("k1_chunks_exact_rows_match_llvm") {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let lib = "#[inline(never)]\n\
        pub fn kernel(img: &[u8], w: usize) -> u64 {\n\
        \x20   let mut s = 0u64;\n\
        \x20   for row in img.chunks_exact(w) {\n\
        \x20       let r: u64 = row.iter().map(|&p| p as u64).sum();\n\
        \x20       s = s.wrapping_mul(31).wrapping_add(r);\n\
        \x20   }\n\
        \x20   s\n\
        }\n\
        #[inline(never)]\n\
        pub fn nrows(img: &[u8], w: usize) -> usize {\n\
        \x20   img.chunks_exact(w).count()\n\
        }\n";
    // No `argv`: the whole-program build compiles this driver with the bridge,
    // which refuses a `String` argument image for reasons unrelated to K1.
    let main = "use std::hint::black_box;\n\
        fn main() {\n\
        \x20   let img: Vec<u8> = (0..1000u32).map(|i| (i % 7) as u8).collect();\n\
        \x20   for &w in &[256usize, 100, 999, 250, 1, 1000, 1001, 7] {\n\
        \x20       show_rows(w, klib::nrows(black_box(&img), black_box(w)));\n\
        \x20   }\n\
        \x20   for &w in &[256usize, 100, 999, 250, 1, 1000, 1001, 7] {\n\
        \x20       show_kernel(w, klib::kernel(black_box(&img), black_box(w)));\n\
        \x20   }\n\
        }\n\
        #[inline(never)]\n\
        fn show_rows(w: usize, n: usize) { println!(\"w={} nrows={}\", w, n); }\n\
        #[inline(never)]\n\
        fn show_kernel(w: usize, k: u64) { println!(\"w={} kernel={}\", w, k); }\n";
    let mut failures = Vec::new();
    let configs = [Mode::Split, Mode::Whole].into_iter().flat_map(|mode| {
        ["0", "1", "2", "3"]
            .into_iter()
            .flat_map(move |opt| [false, true].map(|inline_mir| (mode, opt, inline_mir)))
    });
    for (mode, opt, inline_mir) in configs {
        {
            let label = format!("K1@O{opt}/inline-mir={inline_mir}/{mode:?}");
            let dir = workdir(&format!("k1_O{opt}_{inline_mir}_{mode:?}"));
            let build_k1 = |sub: &str, backend: Option<&Path>| -> Result<PathBuf, String> {
                let d = dir.join(sub);
                std::fs::create_dir_all(&d).expect("create build dir");
                let bin = d.join("prog");
                match mode {
                    Mode::Split => {
                        let src = d.join("klib.rs");
                        std::fs::write(&src, lib).expect("write library");
                        let rlib = d.join("libklib.rlib");
                        let mut cmd = compiler(opt, inline_mir, backend);
                        cmd.args(["--crate-type", "rlib", "--crate-name", "klib"]);
                        cmd.arg("-o").arg(&rlib).arg(&src);
                        checked(cmd)?;
                        let main_src = d.join("kmain.rs");
                        std::fs::write(&main_src, main).expect("write driver");
                        let mut cmd = compiler("3", inline_mir, None);
                        cmd.args(["--crate-type", "bin", "--crate-name", "kmain"]);
                        let mut extern_arg = std::ffi::OsString::from("klib=");
                        extern_arg.push(&rlib);
                        cmd.arg("--extern").arg(extern_arg);
                        cmd.arg("-o").arg(&bin).arg(&main_src);
                        checked(cmd).expect("the LLVM driver builds");
                    }
                    Mode::Whole => {
                        let src = d.join("whole.rs");
                        std::fs::write(&src, format!("mod klib {{\n{lib}\n}}\n{main}"))
                            .expect("write program");
                        let mut cmd = compiler(opt, inline_mir, backend);
                        cmd.args(["--crate-type", "bin", "--crate-name", "whole"]);
                        cmd.arg("-o").arg(&bin).arg(&src);
                        checked(cmd)?;
                    }
                }
                Ok(bin)
            };
            let oracle = build_k1("llvm", None)
                .unwrap_or_else(|e| panic!("{label}: the LLVM oracle did not build: <<<{e}>>>"));
            let bridge = match build_k1("bridge", Some(&dylib)) {
                Ok(bin) => bin,
                Err(stderr) => {
                    failures.push(format!(
                        "{label}: REFUSED (codes {:?}): <<<{stderr}>>>",
                        refusal_codes(&stderr)
                    ));
                    continue;
                }
            };
            let expected = run_with_timeout(&oracle, "", RUN_TIMEOUT).expect("the oracle finishes");
            let expected_stdout = String::from_utf8_lossy(&expected.stdout).into_owned();
            assert!(
                expected.status.success()
                    && expected_stdout.starts_with("w=256 nrows=3\n")
                    && expected_stdout.contains("\nw=256 kernel=756949\n"),
                "{label}: the oracle must count 3 full 256-byte rows and sum them: \
                 <<<{expected_stdout}>>>"
            );
            match run_with_timeout(&bridge, "", RUN_TIMEOUT) {
                None => failures.push(format!("{label}: HANG")),
                Some(got) => {
                    let got_stdout = String::from_utf8_lossy(&got.stdout).into_owned();
                    if (status_key(got.status), got_stdout.as_str())
                        != (status_key(expected.status), expected_stdout.as_str())
                    {
                        failures.push(format!(
                            "{label}: bridge {:?} <<<{got_stdout}>>> vs LLVM {:?} \
                             <<<{expected_stdout}>>>",
                            status_key(got.status),
                            status_key(expected.status)
                        ));
                    }
                }
            }
            let _ = std::fs::remove_dir_all(&dir);
        }
    }
    assert!(
        failures.is_empty(),
        "K1 rows failed:\n{}",
        failures.join("\n")
    );
    eprintln!("K1 rows: 16 configurations (nrows + kernel) MATCHED LLVM");
}

#[test]
fn every_kind_and_shape_is_a_case() {
    let cases = cases();
    assert_eq!(cases.len(), KINDS.len() * SHAPES.len() + 2 + KINDS.len());
    for elem in &ELEMS {
        let lib = lib_source(elem);
        let main = split_main_source(elem);
        let whole = whole_main_source(elem);
        for case in &cases {
            assert!(
                main.contains(&format!("\"{case}\" =>")),
                "driver arm for {case}"
            );
            if !case.starts_with("zero_") {
                assert!(
                    lib.contains(&format!("pub fn {case}")),
                    "library function for {case}"
                );
            }
        }
        // The whole-program driver runs every non-panicking case, then one
        // zero-stride case, and reads no `argv`.
        let rows = whole.matches("emit(").count() - 2;
        assert_eq!(rows, cases.len() - KINDS.len(), "{}", elem.name);
        assert!(!whole.contains("std::env::args"));
        assert!(whole.contains(&case_call(&whole_zero_case(elem))));
    }
    // Across the six element types the whole-program zero-stride case covers
    // every kind.
    let mut zero_kinds: Vec<String> = ELEMS.iter().map(whole_zero_case).collect();
    zero_kinds.sort();
    zero_kinds.dedup();
    assert_eq!(zero_kinds.len(), KINDS.len());
    assert_eq!(
        refusal_codes(
            "error: [TCG-MIR-UNSUPPORTED] x [TCG-STRIDE-ITER-INLINE] y [TCG-MIR-UNSUPPORTED]"
        ),
        vec![
            "TCG-MIR-UNSUPPORTED".to_owned(),
            "TCG-STRIDE-ITER-INLINE".to_owned()
        ]
    );
}
