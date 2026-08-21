#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: CT-BATCH Step 2/3 — per-CGU module batching
// (`TCG_BATCH_CGU=1`, `docs/module-batching-design-2026-07-04.md`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Pins the batched compile path end-to-end on a multi-function integer
// program (the corpus `#![no_std]` `#![no_main]` shape, one CGU):
//   1. batching FIRES (the `TCG_BATCH_TRACE` line reports a merged CGU) and
//      the object count drops to ONE for the whole CGU;
//   2. the batched binary computes the SAME exit code as the legacy
//      one-object-per-function binary (gate OFF);
//   3. the batched compile is DETERMINISTIC: two runs produce byte-identical
//      objects (this also pins the CT-5 parallel fan-out determinism, since
//      the batched path compiles with `CompilerConfig::parallel = true`);
//   4. with the gate OFF the legacy path still emits one object per function
//      (the zero-risk default is genuinely untouched).
//
// The per-CGU fail-closed FALLBACK (merge rejection -> legacy per-fn objects)
// is exercised by the ineligible-module corpus programs (globals / fn-pointer
// values) in the differential harness; this test pins the happy path.

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
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run batch test");
    let built = target_dir
        .join("release")
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

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_batchcgu_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// A five-function call chain (every fn `#[inline(never)]`, pure integer, no
/// globals) — every module merge-eligible, so the single CGU batches fully.
/// Expected exit code: iterate(27) = 111 Collatz steps, combine(9,5) =
/// (9*3+5) ^ (9>>1) = 32 ^ 4 = 36; (111 + 36) % 256 = 147.
const SRC: &str = r#"
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }

#[inline(never)]
fn add_mul(a: i64, b: i64) -> i64 { a.wrapping_mul(3).wrapping_add(b) }

#[inline(never)]
fn step(x: i64) -> i64 { if x % 2 == 0 { x / 2 } else { add_mul(x, 1) } }

#[inline(never)]
fn iterate(mut x: i64) -> i64 {
    let mut n = 0i64;
    while x > 1 && n < 200 { x = step(x); n += 1; }
    n
}

#[inline(never)]
fn combine(a: i64, b: i64) -> i64 { add_mul(a, b) ^ (a >> 1) }

#[no_mangle]
pub extern "C" fn main() -> i32 { ((iterate(27) + combine(9, 5)) % 256) as i32 }
"#;
const EXPECTED_EXIT: i32 = 147;

struct CompileOut {
    objects: Vec<PathBuf>,
    stderr: String,
    dir: PathBuf,
}

/// Compile `SRC` through the bridge into `--out-dir` (so every emitted object
/// is observable) with the given extra envs; returns the sorted object list.
fn bridge_compile(stem: &str, envs: &[(&str, &str)]) -> CompileOut {
    let dylib = ensure_dylib_built();
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, SRC).expect("write source");

    let backend_arg = {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(&dylib);
        s
    };
    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .arg("--crate-type")
        .arg("bin")
        .arg(&backend_arg)
        .args([
            "--target",
            TARGET,
            "-Cpanic=abort",
            "-Coverflow-checks=off",
            "-Ccodegen-units=1",
            "-Copt-level=2",
        ])
        .arg("--emit=obj")
        .arg("--out-dir")
        .arg(&dir)
        .arg(&src_path);
    for (k, v) in envs {
        cmd.env(k, v);
    }
    let output = cmd.output().expect("failed to spawn rustc via rustup");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        output.status.success(),
        "{stem}: bridge failed to compile. stderr: <<<{stderr}>>>"
    );
    let mut objects: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    objects.sort();
    CompileOut {
        objects,
        stderr,
        dir,
    }
}

/// Link every emitted object with abort stubs for undefined `panic*` symbols
/// and run; returns the exit code.
fn link_run(out: &CompileOut) -> i32 {
    let mut stubs = String::from("#include <stdlib.h>\n");
    let mut seen = std::collections::BTreeSet::new();
    for obj in &out.objects {
        let nm = Command::new("nm").arg("-u").arg(obj).output().expect("nm");
        for line in String::from_utf8_lossy(&nm.stdout).lines() {
            let sym = line.trim().trim_start_matches('U').trim();
            if sym.contains("panic") && seen.insert(sym.to_owned()) {
                let c = sym.strip_prefix('_').unwrap_or(sym);
                stubs.push_str(&format!(
                    "void {c}(void) __asm__(\"{sym}\"); void {c}(void){{ abort(); }}\n"
                ));
            }
        }
    }
    let stubs_path = out.dir.join("stubs.c");
    std::fs::write(&stubs_path, stubs).expect("write stubs");
    let bin = out.dir.join("bin");
    let mut link = Command::new("cc");
    link.arg("-o").arg(&bin);
    for obj in &out.objects {
        link.arg(obj);
    }
    link.arg(&stubs_path);
    let link = link.output().expect("cc link");
    assert!(
        link.status.success(),
        "link failed. stderr: <<<{}>>>",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(&bin).output().expect("run compiled binary");
    run.status.code().expect("process terminated by signal")
}

#[test]
fn batched_cgu_fires_matches_legacy_and_is_deterministic() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    if !cfg!(target_arch = "x86_64") {
        eprintln!("skipping: host is not x86_64");
        return;
    }

    // Legacy (gate OFF, explicit): one object per surviving function. The
    // panic-handler shim is GC-dropped from the LINK but its temp object file
    // still lands in --out-dir, so expect the 5 fn objects + 1 dropped shim.
    let legacy = bridge_compile("off", &[("TCG_BATCH_CGU", "0")]);
    assert!(
        legacy.objects.len() > 1,
        "gate OFF must keep one-object-per-function (got {})",
        legacy.objects.len()
    );
    let legacy_exit = link_run(&legacy);
    assert_eq!(legacy_exit, EXPECTED_EXIT, "legacy exit code");

    // Batched (gate ON): the CGU's five functions merge into ONE object.
    let batched = bridge_compile(
        "on",
        &[("TCG_BATCH_CGU", "1"), ("TCG_BATCH_TRACE", "1")],
    );
    assert!(
        batched.stderr.contains("BATCHED"),
        "expected a TCG_BATCH BATCHED trace line; stderr: <<<{}>>>",
        batched.stderr
    );
    assert_eq!(
        batched.objects.len(),
        1,
        "batched CGU must produce exactly one object; got {:?}",
        batched.objects
    );
    let batched_exit = link_run(&batched);
    assert_eq!(batched_exit, EXPECTED_EXIT, "batched exit code");
    assert_eq!(batched_exit, legacy_exit, "batched == legacy behavior");

    // Determinism: a second batched compile is byte-identical (also pins the
    // parallel fan-out, which the batched path enables).
    let batched2 = bridge_compile(
        "on2",
        &[("TCG_BATCH_CGU", "1"), ("TCG_BATCH_TRACE", "1")],
    );
    assert_eq!(batched2.objects.len(), 1);
    let a = std::fs::read(&batched.objects[0]).expect("read batched object");
    let b = std::fs::read(&batched2.objects[0]).expect("read batched2 object");
    assert_eq!(a, b, "batched compile must be byte-identical across runs");

    let _ = std::fs::remove_dir_all(&legacy.dir);
    let _ = std::fs::remove_dir_all(&batched.dir);
    let _ = std::fs::remove_dir_all(&batched2.dir);
}
