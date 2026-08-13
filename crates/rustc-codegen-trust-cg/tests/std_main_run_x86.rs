// Integration test: STANDARD-Rust `fn main` (std) compiled for x86_64 via the
// rustc_codegen_trust_cg bridge — COMPILED, LINKED, and RUN, with exit codes
// checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: WS4 — std `fn main` RUNS on x86_64. This is the milestone: a real std
// Rust `fn main` executing through trust-cg.
//
// The keystone is the `lang_start` closure + `&dyn Fn() -> i32` trait-object
// path. `std::rt::lang_start::<()>` constructs a `move || ...` closure capturing
// the user's `main` fn-pointer, coerces it to a `&dyn Fn() -> i32` fat pointer,
// and hands it to `lang_start_internal`. The bridge now:
//   * lowers the closure-environment aggregate and the `&closure` reference;
//   * emits the vtable as a read-only data global whose method/drop slots are
//     `Constant::SymbolAddr` data-section relocations (drop = null for the Copy
//     closure, size/align as raw bytes, the call_once shim + closure-body
//     methods as relocations) — matching rustc's `vtable_entries` layout;
//   * materializes the closure into an alloca for the fat pointer's data half,
//     binds the fat pointer `{ data, vtable }`, and passes it to
//     `lang_start_internal` as the two-word `(data, vtable)` ABI pair;
//   * lowers the closure body (`main().report().to_i32()`), `Termination::report`
//     (`ExitCode` modeled as its single `u8` scalar), the `FnPtrShim` of
//     `FnOnce::call_once` (an indirect call through the `main` fn-pointer), and
//     `black_box` (as identity); and
//   * emits defined trapping stubs for the `call_once` vtable/closure dispatch
//     shims (slot [3] of the `&dyn Fn` vtable), which are reachable only through
//     dynamic `FnOnce`/`FnMut` dispatch the `Fn::call`-driven `lang_start` never
//     performs — so they link but never execute.
//
// Each program is compiled with BOTH backends and run; the trust-cg exit code
// must equal the LLVM exit code (and the expected value).

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
    let target_dir = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| crate_dir.join("target"));
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
    assert!(status.success(), "cargo build failed; cannot run std-main test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_stdrun_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src` with the given backend (None = default LLVM) and return the
/// linked binary path, asserting the compile succeeded.
fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>) -> PathBuf {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"]);
    if let Some(dylib) = backend {
        cmd.arg(backend_arg(dylib));
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort"])
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    assert!(
        output.status.success(),
        "compile of `{name}` failed ({} backend). stderr: <<<{}>>>",
        if backend.is_some() { "trust-cg" } else { "llvm" },
        String::from_utf8_lossy(&output.stderr)
    );
    bin
}

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// The full differential: each std `fn main` shape is compiled by trust-cg AND
/// LLVM, run, and the exit codes must match each other and the expected value.
#[test]
fn std_main_shapes_run_and_match_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("shapes");

    // (name, source, expected exit code). Exit codes are 0..=255 (process exit
    // truncates to a byte), and chosen to be well within that range.
    let shapes: &[(&str, &str, i32)] = &[
        // Sum 1..=10 = 55 (the canonical loop-carried accumulator).
        (
            "sum",
            "fn main() { let mut s=0i32; let mut i=1i32; while i<=10 { s+=i; i+=1; } \
             std::process::exit(s); }",
            55,
        ),
        // 5! masked to a byte = 120 (multiply + bitand in a loop).
        (
            "fact",
            "fn main() { let mut f:i32=1; let mut i=1i32; while i<=5 { f=(f*i)&0xff; i+=1; } \
             std::process::exit(f); }",
            120,
        ),
        // gcd(48, 36) = 12 (remainder + swap loop).
        (
            "gcd",
            "fn main() { let mut a=48i32; let mut b=36i32; while b!=0 { let t=b; b=a%b; a=t; } \
             std::process::exit(a); }",
            12,
        ),
        // Branch shape: if x>y { x*2 } else { y+3 } with x=7,y=13 -> 16.
        (
            "branch",
            "fn main() { let x=7i32; let y=13i32; let r = if x>y { x*2 } else { y+3 }; \
             std::process::exit(r); }",
            16,
        ),
        // LICM kernel shape: a tight u64 loop whose body re-materializes two
        // loop-invariant constants every iteration (the multiplier 2654435761
        // and the loop bound). x86 LICM hoists those `mov reg,imm` into the
        // preheader; the differential exit code must still equal LLVM. Uses a
        // small bound so the test runs fast. Computes
        // (sum_{i=0}^{999} i*2654435761) & 0x7f. Both backends must agree.
        (
            "licm_const_hoist",
            "fn main(){ let mut a:u64=0; let mut i:u64=0; while i<1000 { \
             a=a.wrapping_add(i.wrapping_mul(2654435761)); i+=1; } \
             std::process::exit((a & 0x7f) as i32); }",
            // Expected value is asserted to equal LLVM at runtime; we still pin a
            // concrete byte so a silent both-backends-wrong regression is caught.
            // sum_{i=0}^{999} (i*2654435761 mod 2^64), then & 0x7f == 108.
            108,
        ),
    ];

    for (name, src, expected) in shapes {
        let llvm_bin = compile(&dir, &format!("{name}_llvm"), src, None);
        let tcg_bin = compile(&dir, &format!("{name}_tcg"), src, Some(&dylib));
        let llvm_exit = run_exit_code(&llvm_bin);
        let tcg_exit = run_exit_code(&tcg_bin);
        assert_eq!(
            llvm_exit, *expected,
            "LLVM backend exit code for `{name}` is {llvm_exit}, expected {expected}"
        );
        assert_eq!(
            tcg_exit, llvm_exit,
            "trust-cg exit code for `{name}` is {tcg_exit}, LLVM is {llvm_exit} (must match)"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}
