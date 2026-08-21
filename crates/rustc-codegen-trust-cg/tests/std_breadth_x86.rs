#[path = "support/target_dir.rs"]
mod target_dir_support;

// crates/rustc-codegen-trust-cg/tests/std_breadth_x86.rs
//
// COMPLETE-6 (std breadth) — regression pins for the general-lowering gaps this
// task closed, each verified DIFFERENTIALLY against the LLVM oracle at -O0.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Fixes pinned here (see the COMPLETE-6 report):
//   1. MULTI-LATCH loop back-edge faithfulness false positive. A `match`/`switch`
//      loop whose arms each `goto` the header directly is a MULTI-LATCH loop; the
//      per-back-edge mutation-dominance check used to apply ONE latch's dominance
//      set to every edge, falsely flagging a loop-carried scalar that is
//      legitimately unchanged on another arm's edge as a dropped update
//      (interpreter / state-machine dispatch loops). Now computed per predecessor.
//      SINGLE-latch behavior (the union-loop store-drop gate) is unchanged.
//   2. `Vec::is_empty` general lowering (`len() == 0`).
//   3. `Vec::pop` general lowering (`len>0 ? Some(buf[len-1]) : None`, length
//      decremented only when non-empty; an EMPTY pop is crash-safe and yields
//      `None`, matching real `pop`).
//
// Each program is compiled through BOTH lanes (stock rustc/LLVM and the trust-cg
// bridge) at -O0, run, and the exit codes must MATCH (self-validating — no
// hard-coded oracle). A trust-cg fail-closed is a HARD failure here (these shapes
// MUST compile after this task); an exit-code divergence is a P0 miscompile.
//
// Run: cd crates/rustc-codegen-trust-cg
//      cargo test --release --test std_breadth_x86 -- --nocapture

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";
const MACOS_DEPLOYMENT_TARGET: &str = "13.0";

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

fn dylib_name() -> String {
    format!(
        "{}rustc_codegen_trust_cg{}",
        std::env::consts::DLL_PREFIX,
        std::env::consts::DLL_SUFFIX
    )
}

fn ensure_dylib_built() -> PathBuf {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let target_dir = target_dir_support::cargo_target_dir(crate_dir);
    let name = dylib_name();
    for cand in [
        target_dir.join("release").join(&name),
        target_dir.join("debug").join(&name),
    ] {
        if cand.exists() {
            return cand;
        }
    }
    let status = Command::new("cargo")
        .arg(format!("+{}", pinned_toolchain()))
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed");
    let built = target_dir.join("release").join(&name);
    assert!(built.exists(), "expected dylib at {built:?}");
    built
}

fn x86_64_std_available() -> bool {
    Command::new("rustup")
        .args(["target", "list", "--installed", "--toolchain"])
        .arg(pinned_toolchain())
        .output()
        .map(|o| {
            String::from_utf8_lossy(&o.stdout)
                .lines()
                .any(|l| l.trim() == TARGET)
        })
        .unwrap_or(false)
}

fn host_is_x86_64() -> bool {
    cfg!(target_arch = "x86_64")
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_stdbreadth_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile+link+run `src` at `-O0`. `dylib=Some` selects the trust-cg bridge;
/// `None` selects the LLVM oracle. Returns `Ok(exit_code)` or `Err(stderr_tail)`
/// when the compile fails closed.
fn compile_run_o0(dir: &Path, name: &str, src: &str, dylib: Option<&Path>) -> Result<i32, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);
    let mut cmd = Command::new("rustup");
    cmd.env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET);
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"]);
    if let Some(dylib) = dylib {
        let mut a = std::ffi::OsString::from("-Zcodegen-backend=");
        a.push(dylib);
        cmd.arg(a);
    }
    cmd.args([
        "--target",
        TARGET,
        "-Cpanic=abort",
        "-Coverflow-checks=off",
        "-Ccodegen-units=1",
        "-Copt-level=0",
    ])
    .arg("-o")
    .arg(&bin)
    .arg(&src_path);
    let out = cmd.output().expect("spawn rustc");
    if !out.status.success() {
        return Err(String::from_utf8_lossy(&out.stderr)
            .lines()
            .rev()
            .take(4)
            .collect::<Vec<_>>()
            .join(" | "));
    }
    Ok(Command::new(&bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("child exited via signal"))
}

#[test]
fn std_breadth_compile_and_match_o0() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 host required");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("run");

    // (name, source). Each MUST compile through the bridge and match LLVM's exit.
    let shapes: &[(&str, &str)] = &[
        // 1a. MULTI-LATCH dispatch loop: two loop-carried scalars updated on
        //     DISJOINT match arms (each arm `goto`s the header). Pre-fix this
        //     fail-closed with "back-edge value is the unchanged loop-header phi
        //     parameter"; the per-back-edge dominance fix admits it correctly.
        (
            "multilatch_dispatch",
            r#"
fn main() {
    let prog: [u8; 8] = [0, 2, 1, 0, 2, 1, 2, 9];
    let mut acc: u64 = 0;
    let mut ctr: u64 = 0;
    let mut pc: usize = 0;
    while pc < prog.len() {
        match prog[pc] {
            0 => { acc = acc.wrapping_add(5); pc += 1; }
            1 => { acc = acc.wrapping_mul(3); pc += 1; }
            2 => { ctr = ctr.wrapping_add(7); pc += 1; }
            _ => break,
        }
    }
    std::process::exit(((acc ^ ctr) % 251) as i32);
}
"#,
        ),
        // 1b. A MULTI-LATCH loop over a &[u8] slice (a bracket-depth scan): the
        //     `if/else` body is two back edges to the header; `max_depth` is
        //     updated only on the push edge and `balanced` only on the pop edge —
        //     the exact disjoint-conditional-update shape the per-back-edge fix
        //     admits (pre-fix: fail-closed on the edge that leaves one scalar
        //     unchanged). Compiles at BOTH O0 and O3.
        (
            "multilatch_slice_scan",
            r#"
fn main() {
    let input: &[u8] = b"([]{()[]}([{}]))[[({})]]{}()((([[{{}}]])))";
    let mut max_depth: usize = 0;
    let mut balanced: u64 = 1;
    let mut depth: usize = 0;
    let mut i = 0usize;
    while i < input.len() {
        let c = input[i];
        if c == b'(' || c == b'[' || c == b'{' {
            depth += 1;
            if depth > max_depth { max_depth = depth; }
        } else {
            if depth == 0 { balanced = 0; } else { depth -= 1; }
        }
        i += 1;
    }
    let h = (max_depth as u64).wrapping_mul(19).wrapping_add(balanced).wrapping_add(input.len() as u64);
    std::process::exit((h % 251) as i32);
}
"#,
        ),
        // 2. Vec::is_empty on empty / non-empty / cleared.
        (
            "vec_is_empty",
            r#"
fn bb(x: u8) -> u8 { std::hint::black_box(x) }
fn main() {
    let mut v: Vec<u8> = Vec::new();
    let mut acc: u64 = 0;
    if v.is_empty() { acc += 100; }
    let mut i = 0u8;
    while i < bb(5) { v.push(i); i += 1; }
    if !v.is_empty() { acc += 20; }
    v.clear();
    if v.is_empty() { acc += 3; }
    std::process::exit((acc % 251) as i32);
}
"#,
        ),
        // 3. Vec::pop, including the crash-safe EMPTY pop (must yield None, must
        //    not underflow the length nor deref a dangling buffer).
        (
            "vec_pop_stack",
            r#"
fn bb(x: u8) -> u8 { std::hint::black_box(x) }
fn main() {
    let mut s: Vec<u8> = Vec::new();
    let mut acc: u64 = 0;
    match s.pop() { Some(_) => acc += 1000, None => acc += 7 }   // empty -> None
    for i in 0..bb(5) { s.push(i * 3); }
    while let Some(v) = s.pop() { acc = acc.wrapping_mul(10).wrapping_add(v as u64); }
    match s.pop() { Some(_) => acc += 500, None => acc += 3 }    // empty again
    std::process::exit((acc % 251) as i32);
}
"#,
        ),
    ];

    let mut failures: Vec<String> = Vec::new();
    for (name, src) in shapes {
        let oracle = compile_run_o0(&dir, &format!("{name}_llvm"), src, None)
            .unwrap_or_else(|e| panic!("FIXTURE BROKEN: LLVM could not compile `{name}`: {e}"));
        match compile_run_o0(&dir, &format!("{name}_tcg"), src, Some(&dylib)) {
            Ok(tcg) if tcg == oracle => {
                eprintln!("std-breadth {name:<20} O0 MATCH (exit={tcg})");
            }
            Ok(tcg) => {
                failures.push(format!(
                    "{name}: P0 MISCOMPILE — llvm_exit={oracle} trust_cg_exit={tcg}"
                ));
            }
            Err(reason) => {
                failures.push(format!(
                    "{name}: FAIL-CLOSED regression (must compile after COMPLETE-6): {reason}"
                ));
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(failures.is_empty(), "std-breadth pins failed:\n{}", failures.join("\n"));
}
