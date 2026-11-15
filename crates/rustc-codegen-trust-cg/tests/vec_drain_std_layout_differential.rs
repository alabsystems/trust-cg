#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a `vec::Drain` crosses between bridge-compiled and
// LLVM-compiled code in both directions and must mean the same thing on
// either side.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE DEFECT. The bridge intercepts `Vec::drain`, `<Drain as Iterator>::next`,
// the identity `into_iter` and `<Drain as Drop>::drop` for a no-drop element.
// It used to model the Drain with its own four words `{ ptr@0, end@8,
// vecslot@16, newlen@24 }` and its own semantics: the constructor never
// shortened the Vec (std sets `len = start` before returning), never wrote
// std's `tail_len@32`, and stored the post-drop length where std keeps
// `tail_start`; the drop wrote that word into the Vec's length and moved no
// tail; the identity copied four words of five. Nothing tied a Drain to the
// side that built it, so
//   * a Drain LLVM code built and handed to the bridge (a by-value parameter,
//     an `Option` or struct field, the identity `into_iter`) came back with
//     drained elements restored, the kept tail lost, or (identity) a garbage
//     `tail_len`;
//   * a Drain the bridge built and returned (bare, in an `Option`, in a tuple)
//     was dropped by std's real `Drop` over an uninitialized `tail_len`: an
//     out-of-bounds memmove and a length past the capacity;
//   * a Drain the bridge built and leaked (`mem::forget(Some(d))`,
//     `forget((d, 0))`) left the Vec at its old length, exposing drained
//     elements, including one the Drain had already moved out (`dup_tok`
//     returned `Tok(1)` with the Vec still holding `Tok(1)`);
//   * `drop_glue::<Drain<T>>` calls `<Drain as Drop>::drop`, which the
//     `[TCG-OWNING-ITER-METHOD]` guard refused, so a library that drops a Drain
//     itself left that glue undefined, and an LLVM driver that links it from
//     the library under `-Zshare-generics` failed to link at O0;
//   * the Drain predicate admitted any allocator, so the drop of a
//     `Drain<'_, T, A>` whose `Vec<T, A>::drain` was std's own code (a custom
//     `A` is not the modeled Vec) read std's `tail_start` as the new length.
// Measured on origin/main c8b07006b with these rows (aarch64-apple-darwin):
// std_to_bridge O0 link failure, O1 SIGBUS, O2/O3 wrong transcript;
// bridge_to_std O0 link failure, O1-O3 SIGSEGV or SIGBUS (the garbage
// `tail_len` varies by run) (hunt UP2-T1-DRAIN-PRIVATE-LAYOUT-AT-STD-BOUNDARY
// and UP2-T1-DRAIN-DEFERRED-TRUNCATION); custom_allocator O0 link failure,
// O1-O3 wrong transcript (`sink` and `sum_from` restore the drained elements).
//
// THE INVARIANT. The bridge's Drain IS std's: `VecDrainLayout` reads the five
// words' offsets from rustc's layout, the constructor writes std's values and
// shortens the Vec, `next` advances `iter.ptr`, the identity copies all five
// words, and the drop (of a Drain local, or the glue's `<Drain as
// Drop>::drop` call) applies std's transition (move the kept tail back,
// restore the length). Only a Drain over the Global allocator is modeled; any
// other is std's code throughout. Every row below must therefore BUILD and
// MATCH the LLVM oracle at every optimization level; none may be refused.
//
// HARNESS. The hunt's: the library (`klib`) is compiled once by LLVM and once
// by the bridge, each linked into the same LLVM-compiled driver (`kmain`), and
// each driver's exit status and stdout are compared. The LLVM oracle is
// asserted against the row's pinned transcript FIRST, so a row that measures
// something else says so. The binaries run under macOS's `MallocScribble` /
// `MallocGuardEdges` / `MallocErrorAbort` (inert elsewhere) and under a
// deadline, so a hang is a failure. HOST-NATIVE: no `--target` is passed; the
// bridge side passes `no-proof-certs` (these rows judge codegen, not proofs).

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const OPTS: [&str; 4] = ["0", "1", "2", "3"];

struct Row {
    name: &'static str,
    lib: &'static str,
    main: &'static str,
    /// The LLVM oracle's stdout.
    expect: &'static str,
}

const ROWS: &[Row] = &[
    Row {
        name: "std_to_bridge",
        lib: include_str!("support/vec_drain_std_layout/std_to_bridge_lib.rs"),
        main: include_str!("support/vec_drain_std_layout/std_to_bridge_main.rs"),
        expect: "\
sink 1..3 [1, 4, 5]
sink 0..5 []
sink 0..2 [3, 4, 5]
sink 2..2 [1, 2, 3, 4, 5]
sink 3..5 [1, 2, 3]
sink_u8 [10, 40, 50]
sink_u64 [10, 40, 50]
sink_char ['a', 'd', 'e']
sink_pair [(1, 1), (4, 4), (5, 5)]
sink_pt [(1, 10), (4, 40), (5, 50)]
consume s=23 [1, 4, 5]
pass drop [1, 4, 5]
pass collect [2, 3, 4] [1, 5]
pass_move drop [1, 4, 5]
opt_param r=1 [1, 4, 5]
struct_param b=7 [1, 4, 5]
",
    },
    Row {
        name: "bridge_to_std",
        lib: include_str!("support/vec_drain_std_layout/bridge_to_std_lib.rs"),
        main: include_str!("support/vec_drain_std_layout/bridge_to_std_main.rs"),
        expect: "\
make drop [1]
make collect [3, 4, 5] [1, 2]
make partial Some(2) rest=3 [1]
make forget [1, 2, 3, 9]
make empty [1, 2, 3, 4, 5]
make_all drop []
make_u8 [30, 40, 50] [10, 20]
make_u64 [10]
make_char de ['a', 'b', 'c']
make_pair [(1, 1), (2, 2)]
make_pt [(4, 40), (5, 50)] [(1, 10), (2, 20), (3, 30)]
ret_option s=12 [1, 2]
ret_tuple b=3 [1]
leak_len [7, 100]
leak_tuple []
dup_tok taken=Some(1) []
sum_from s=345 [1, 2]
",
    },
    Row {
        name: "custom_allocator",
        lib: include_str!("support/vec_drain_std_layout/custom_alloc_lib.rs"),
        main: include_str!("support/vec_drain_std_layout/custom_alloc_main.rs"),
        expect: "\
make drop [1, 2]
make collect [2, 3, 4, 5] [1]
sink 1..3 [1, 4, 5]
sum_from s=345 [1, 2]
",
    },
];

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_vec_drain_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// The bridge's named refusal tag, if `stderr` is a fail-closed refusal rather
/// than a crash. An ICE, a panic, or a refusal with no `[TCG-...]` tag is not.
fn named_refusal(stderr: &str) -> Option<String> {
    if stderr.contains("internal compiler error") || stderr.contains("panicked at") {
        return None;
    }
    let start = stderr.find("[TCG-")?;
    let end = stderr[start..].find(']')? + start + 1;
    Some(stderr[start..end].to_owned())
}

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Exit(i32, String),
    Signal(i32),
    Hung,
}

/// Run `bin all` under the macOS malloc checks with a deadline.
fn run(bin: &Path) -> Outcome {
    let mut child = Command::new(bin)
        .arg("all")
        .env("MallocScribble", "1")
        .env("MallocGuardEdges", "1")
        .env("MallocErrorAbort", "1")
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn compiled binary");
    let start = Instant::now();
    loop {
        if let Some(status) = child.try_wait().expect("poll compiled binary") {
            let mut stdout = String::new();
            if let Some(mut pipe) = child.stdout.take() {
                use std::io::Read;
                let _ = pipe.read_to_string(&mut stdout);
            }
            if let Some(code) = status.code() {
                return Outcome::Exit(code, stdout);
            }
            #[cfg(unix)]
            {
                use std::os::unix::process::ExitStatusExt;
                if let Some(signal) = status.signal() {
                    return Outcome::Signal(signal);
                }
            }
            return Outcome::Signal(-1);
        }
        if start.elapsed() > Duration::from_secs(30) {
            let _ = child.kill();
            let _ = child.wait();
            return Outcome::Hung;
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}

/// Compile `src` as the `klib` rlib, by the bridge when `backend` is given.
fn compile_lib(
    dir: &Path,
    src: &str,
    backend: Option<&Path>,
    opt: &str,
) -> (std::process::Output, PathBuf) {
    let src_path = dir.join("klib.rs");
    std::fs::write(&src_path, src).expect("write library source");
    let lib = dir.join("libklib.rlib");
    let _ = std::fs::remove_file(&lib);
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "rlib", "--crate-name", "klib"])
        .args(["-Cpanic=abort", "-Ccodegen-units=1"])
        .arg(format!("-Copt-level={opt}"));
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.arg("-o").arg(&lib).arg(&src_path);
    (cmd.output().expect("spawn the compiler"), lib)
}

/// Compile the LLVM driver `src` against `lib`.
fn compile_main(dir: &Path, lib: &Path, src: &str, opt: &str) -> (std::process::Output, PathBuf) {
    let src_path = dir.join("kmain.rs");
    std::fs::write(&src_path, src).expect("write driver source");
    let bin = dir.join("kmain");
    let _ = std::fs::remove_file(&bin);
    let mut extern_arg = std::ffi::OsString::from("klib=");
    extern_arg.push(lib);
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin", "--crate-name", "kmain"])
        .args(["-Cpanic=abort", "-Ccodegen-units=1"])
        .arg(format!("-Copt-level={opt}"))
        .arg("--extern")
        .arg(extern_arg)
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    (cmd.output().expect("spawn the compiler"), bin)
}

/// Build `row` at `opt` with LLVM (`backend == None`) or the bridge and run it.
/// `Err` carries a named refusal or a build failure.
fn build_and_run(
    root: &Path,
    row: &Row,
    backend: Option<&Path>,
    opt: &str,
) -> Result<Outcome, String> {
    let side = if backend.is_some() { "tcg" } else { "llvm" };
    let dir = root.join(format!("{}_o{opt}_{side}", row.name));
    std::fs::create_dir_all(&dir).expect("create cell dir");
    let (out, lib) = compile_lib(&dir, row.lib, backend, opt);
    if !out.status.success() {
        let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
        return Err(match named_refusal(&stderr) {
            Some(tag) => format!(
                "REFUSED ({tag}): <<<{}>>>",
                stderr
                    .lines()
                    .filter(|l| l.contains(" - ") || l.contains("[TCG-"))
                    .take(4)
                    .collect::<Vec<_>>()
                    .join(" | ")
            ),
            None => format!(
                "library build failed WITHOUT a named [TCG-...] refusal: <<<{}>>>",
                stderr.lines().rev().take(8).collect::<Vec<_>>().join(" | ")
            ),
        });
    }
    let (out, bin) = compile_main(&dir, &lib, row.main, opt);
    if !out.status.success() {
        return Err(format!(
            "the LLVM driver did not build against the {side} library: <<<{}>>>",
            String::from_utf8_lossy(&out.stderr)
                .lines()
                .rev()
                .take(8)
                .collect::<Vec<_>>()
                .join(" | ")
        ));
    }
    Ok(run(&bin))
}

#[test]
fn vec_drain_crosses_the_llvm_boundary_with_std_semantics() {
    if toolchain_support::skip_without_backend_knobs(
        "vec_drain_crosses_the_llvm_boundary_with_std_semantics",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let root = workdir("diff");
    let mut failures = Vec::new();
    let mut matched = 0usize;
    for row in ROWS {
        for opt in OPTS {
            let oracle = build_and_run(&root, row, None, opt)
                .unwrap_or_else(|e| panic!("LLVM oracle for `{}` at -O{opt}: {e}", row.name));
            assert_eq!(
                oracle,
                Outcome::Exit(0, row.expect.to_owned()),
                "the LLVM oracle for `{}` at -O{opt} is not the row's transcript; this row \
                 measures something else",
                row.name
            );
            match build_and_run(&root, row, Some(&dylib), opt) {
                Ok(ran) if ran == oracle => matched += 1,
                Ok(ran) => failures.push(format!(
                    "-O{opt} `{}`: the bridge-compiled library DISAGREES with LLVM — a \
                     vec::Drain meant different state on the two sides:\n    trust-cg: \
                     {ran:?}\n    llvm:     {oracle:?}",
                    row.name
                )),
                Err(e) => failures.push(format!(
                    "-O{opt} `{}`: {e} — every row must build and match",
                    row.name
                )),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&root);
    assert!(
        failures.is_empty(),
        "{} vec::Drain boundary cell(s) failed ({matched} matched):\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    assert_eq!(
        matched,
        ROWS.len() * OPTS.len(),
        "every cell must build and match"
    );
    eprintln!(
        "VEC_DRAIN_STD_LAYOUT rows={} cells={matched} matched={matched} opts=0,1,2,3",
        ROWS.len()
    );
}
