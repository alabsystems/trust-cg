#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test (m125): the REASSIGNED / copied slice-`&[T]` / `&str`
// fat-pointer frontend arm. A `let mut r: &[i32] = &[..]; r = &[..]; use(r)`
// (and its `&str` mirror `let mut s = ".."; s = ".."; use(s)`) keeps the mutable
// fat-pointer local OUT of SSA, so rustc emits a real fat-pointer copy statement
// (`_7 = copy _1; PtrMetadata(move _7)`) or, at `-O`, an inlined `str::len`
// transmute (`_5 = copy _1 as &[u8] (Transmute)`) over the reassigned local.
// Compiled for x86_64 via the rustc_codegen_trust_cg bridge, COMPILED, LINKED,
// and RUN, with exit codes checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Before this arm both shapes failed CLOSED: the scalar-borrow path rejected the
// copy (`_7 = copy _1` -> "borrowed reference Use before scalar borrow binding")
// and `lower_memory_slice_assign` rejected a scalar `Use`/`Transmute` source
// ("memory-backed slice assignment Rvalue::{Use,Cast}"). The fix classifies a
// slice/str fat-pointer local joined to an already-memory-backed slice/str local
// by a whole-value `Use`/`Transmute` edge as itself memory-backed (a
// `{ data, len }` slot), so the reassign stores both halves and later uses reload
// them. A SINGLE-assignment slice/str (which rustc SSA-collapses or const-folds)
// keeps its scalar / side-table path and is untouched.
//
// Each case is a strict CONTENT differential: the exit code folds BOTH the
// reassigned length AND a read-back element / byte, so a dropped reassign (reading
// the stale initial value) or a wrong data pointer (reading the wrong literal)
// shows up as a mismatched exit code. Run at `-Copt-level=0` AND `-Copt-level=3`
// (opt parity — the out-of-line O0 copy and the inlined O3 transmute forms alike).

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";

fn pinned_toolchain() -> String {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let toolchain = std::fs::read_to_string(crate_dir.join("rust-toolchain.toml"))
        .expect("failed to read rust-toolchain.toml");
    for line in toolchain.lines() {
        let line = line.trim();
        if let Some(raw_channel) = line.strip_prefix("channel") {
            let Some((_, value)) = raw_channel.split_once('=') else {
                continue;
            };
            return value.trim().trim_matches('"').to_owned();
        }
    }
    panic!("rust-toolchain.toml did not contain a channel");
}

fn ensure_dylib_built() -> PathBuf {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let target_dir = target_dir_support::cargo_target_dir(crate_dir);
    let candidates = [
        target_dir
            .join("release")
            .join("librustc_codegen_trust_cg.dylib"),
        target_dir
            .join("debug")
            .join("librustc_codegen_trust_cg.dylib"),
    ];
    for cand in &candidates {
        if cand.exists() {
            return cand.clone();
        }
    }
    let status = Command::new("cargo")
        .arg(format!("+{}", pinned_toolchain()))
        .args(["build"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run m124 test");
    let built = target_dir
        .join("debug")
        .join("librustc_codegen_trust_cg.dylib");
    assert!(built.exists(), "expected dylib at {built:?} but none produced");
    built
}

fn x86_64_std_available() -> bool {
    let output = Command::new("rustup")
        .args(["target", "list", "--installed", "--toolchain"])
        .arg(pinned_toolchain())
        .output();
    match output {
        Ok(output) => String::from_utf8_lossy(&output.stdout)
            .lines()
            .any(|line| line.trim() == TARGET),
        Err(_) => false,
    }
}

fn host_is_x86_64() -> bool {
    cfg!(target_arch = "x86_64")
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_m124_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

fn try_compile_at(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt_level: &str,
) -> Result<PathBuf, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"]);
    if let Some(dylib) = backend {
        cmd.arg(backend_arg(dylib));
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort", opt_level])
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    if output.status.success() {
        Ok(bin)
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

fn compile_at(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt_level: &str,
) -> PathBuf {
    match try_compile_at(dir, name, src, backend, opt_level) {
        Ok(bin) => bin,
        Err(stderr) => panic!(
            "compile of `{name}` failed ({} backend, {opt_level}). stderr: <<<{stderr}>>>",
            if backend.is_some() { "trust-cg" } else { "llvm" },
        ),
    }
}

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// Every REASSIGNED / copied slice/str fat-pointer shape is compiled by trust-cg
/// AND LLVM, run, and the exit codes must match each other and the expected
/// CONTENT-folded value, at BOTH `-Copt-level=0` and `-Copt-level=3`.
#[test]
fn reassign_slice_ref_runs_and_matches_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("cases");

    // (name, source, expected exit code). All values are in 0..=255.
    let shapes: &[(&str, &str, i32)] = &[
        // 1. `&[i32]` REASSIGN, length read-back: the reassigned `&[4,5,6,7]` gives
        //    len 4 (the stale initial `&[1,2,3]` would be 3).
        (
            "slice_reassign_len",
            "fn main(){ let mut r: &[i32] = &[1,2,3]; r = &[4,5,6,7]; \
             std::process::exit(r.len() as i32) }",
            4,
        ),
        // 2. `&[i32]` REASSIGN, ELEMENT read-back — proves the reassigned DATA pointer
        //    resolves to the new literal: `[4,5,6,7][2] == 6` (stale `[1,2,3][2]==3`).
        (
            "slice_reassign_elem",
            "fn main(){ let mut r: &[i32] = &[1,2,3]; r = &[4,5,6,7]; \
             std::process::exit(r[2]) }",
            6,
        ),
        // 3. `&[i32]` REASSIGN, length AND element folded: `len(4)*10 + r[2](6) == 46`
        //    — a single exit code that pins BOTH fat-pointer halves after reassign.
        (
            "slice_reassign_len_elem",
            "fn main(){ let mut r: &[i32] = &[1,2,3]; r = &[4,5,6,7]; \
             std::process::exit((r.len() as i32)*10 + r[2]) }",
            46,
        ),
        // 4. `&str` REASSIGN, length read-back: `"hello".len() == 5` (stale `"hi"==2`).
        (
            "str_reassign_len",
            "fn main(){ let mut s: &str = \"hi\"; s = \"hello\"; \
             std::process::exit(s.len() as i32) }",
            5,
        ),
        // 5. `&str` REASSIGN, BYTE-CONTENT read-back — proves the reassigned data
        //    pointer resolves to the RIGHT literal: `"world"[1] == 'o' == 111`.
        (
            "str_reassign_byte",
            "fn main(){ let mut s: &str = \"hi\"; s = \"world\"; \
             std::process::exit(s.as_bytes()[1] as i32) }",
            111,
        ),
        // 6. BRANCH-VARYING reassign, NOT taken (`black_box(0) > 100` is false): `r`
        //    keeps `&[1,2,3]`, len 3. The reassign stores into the SAME slot so the
        //    merge reads whichever arm ran — no lost update.
        (
            "slice_reassign_branch_nottaken",
            "fn main(){ let c = std::hint::black_box(0i32) > 100; \
             let mut r: &[i32] = &[1,2,3]; if c { r = &[9,9]; } \
             std::process::exit(r.len() as i32) }",
            3,
        ),
        // 7. BRANCH-VARYING reassign, TAKEN (`black_box(200) > 100` is true): `r`
        //    becomes `&[9,9]`, len 2. Proves the conditional store reaches the merge.
        (
            "slice_reassign_branch_taken",
            "fn main(){ let c = std::hint::black_box(200i32) > 100; \
             let mut r: &[i32] = &[1,2,3]; if c { r = &[9,9]; } \
             std::process::exit(r.len() as i32) }",
            2,
        ),
        // 8. BRANCH-VARYING `&str` reassign, byte read-back: taken arm gives
        //    `"world"[1] == 'o' == 111`.
        (
            "str_reassign_branch_byte",
            "fn main(){ let mut s: &str = \"aa\"; \
             if std::hint::black_box(7i32) > 3 { s = \"world\"; } \
             std::process::exit(s.as_bytes()[1] as i32) }",
            111,
        ),
        // 9. COPY CHAIN after reassign (`r = ..; let q = r; let p = q;`): the fat
        //    pointer flows through two extra bare-local copies. `len(5)*10 + p[3](40)
        //    == 90` proves both halves survive the chain.
        (
            "slice_reassign_copy_chain",
            "fn main(){ let mut r: &[i32] = &[1,2,3]; r = &[10,20,30,40,50]; \
             let q = r; let p = q; std::process::exit((p.len() as i32)*10 + p[3]) }",
            90,
        ),
        // 10. MULTIPLE reassign (four stores into the same slot): last write wins,
        //     `len(4)*10 + r[1](8) == 48`.
        (
            "slice_reassign_multi",
            "fn main(){ let mut r: &[i32] = &[1]; r = &[2,2]; r = &[3,3,3]; \
             r = &[9,8,7,6]; std::process::exit((r.len() as i32)*10 + r[1]) }",
            48,
        ),
        // 11. LOOP-CARRIED subslice reassign (`r = &r[1..]` each iteration): the fat
        //     pointer slot is updated across the back-edge, summing `5+6+7+8+9 == 35`.
        (
            "slice_reassign_loop_subslice",
            "fn main(){ let data = [5,6,7,8,9]; let mut r: &[i32] = &data[..]; \
             let mut acc = 0i32; while r.len() > 0 { acc += r[0]; r = &r[1..]; } \
             std::process::exit(acc) }",
            35,
        ),
    ];

    for opt_level in ["-Copt-level=0", "-Copt-level=3"] {
        for (name, src, expected) in shapes {
            let case = format!("{name}_{}", &opt_level[opt_level.len() - 1..]);
            let llvm_bin = compile_at(&dir, &format!("{case}_llvm"), src, None, opt_level);
            let tcg_bin = compile_at(&dir, &format!("{case}_tcg"), src, Some(&dylib), opt_level);
            let llvm_exit = run_exit_code(&llvm_bin);
            let tcg_exit = run_exit_code(&tcg_bin);
            assert_eq!(
                llvm_exit, *expected,
                "LLVM backend exit code for `{case}` is {llvm_exit}, expected {expected}"
            );
            assert_eq!(
                tcg_exit, llvm_exit,
                "trust-cg exit code for `{case}` is {tcg_exit}, LLVM is {llvm_exit} (must match)"
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}
