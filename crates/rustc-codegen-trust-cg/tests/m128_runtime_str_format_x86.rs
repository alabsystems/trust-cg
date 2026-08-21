#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: `format!` with a RUNTIME `&str` argument — a non-const `&str`
// (a fn parameter or a non-const local) whose LENGTH is only known at run time
// (the `len` half of its fat pointer). This is the common real-`std` shape
//
//     fn f(s: &str) -> usize { format!("hi {}", s).len() }
//
// which previously FAILED CLOSED ("format! &str arg has no known length") because
// the single-block, branchless `format!` emitter required every placeholder's byte
// length to be a compile-time constant. A runtime `&str`'s `(data, len)` fat
// pointer IS available at run time (via the same slice resolver `String::push_str`
// / `to_vec` use), so the emitter now:
//   * sizes the String capacity as a RUNTIME sum (static bytes + each runtime
//     `&str`'s `len`),
//   * copies each runtime `&str`'s bytes with a runtime-count loop (splitting the
//     block, as any dynamic-count copy does), advancing the cursor by the runtime
//     length.
// The const-literal + runtime-integer placeholders keep their branchless path, so
// a MIXED `format!("n={} s={}", n, s)` (runtime int + runtime `&str`) works too.
//
// This pins CONTENT (not just length): each program hashes the produced String's
// BYTES and exits with that hash, so an under-/over-copy, a wrong cursor, or a
// wrong capacity would diverge from the LLVM reference. Checked at -O0, -O2 AND -O3
// (at -O3 rustc inlines `format` into the `Option::<&str>::map_or_else` consumer,
// which the bridge recognizes and routes through the same emitter).
//
// The runtime `&str` args are taken through `#[inline(never)]` helpers so they are
// genuine runtime fat pointers (a memory-backed `&str` parameter), NOT const-folded
// literals — exercising the runtime-length path, not the const path.

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
    assert!(status.success(), "cargo build failed; cannot run m128 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m128_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src` with rustc's default LLVM backend at `-O` and return the run's
/// exit code (the GROUND TRUTH).
fn run_llvm(dir: &Path, src: &str) -> i32 {
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join("llvm_out");
    let status = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin", "-Cpanic=abort", "-O"])
        .arg("-o")
        .arg(&bin)
        .arg(&src_path)
        .status()
        .expect("spawn rustc (LLVM)");
    assert!(status.success(), "LLVM reference failed to compile: <<<{src}>>>");
    Command::new(&bin)
        .status()
        .expect("run LLVM binary")
        .code()
        .expect("LLVM binary exit code")
}

/// Compile `src` via the trust-cg bridge at `opt_level`. Returns `Some(exit_code)`
/// when it compiled, links, and ran; `None` when the bridge FAILED CLOSED (a safe
/// coverage gap), distinguished from a link/run error which `panic!`s.
fn run_bridge(dir: &Path, dylib: &Path, src: &str, opt_level: &str) -> Option<i32> {
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(format!("bridge_out_{opt_level}"));
    let output = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"])
        .arg(backend_arg(dylib))
        .args(["--target", TARGET, "-Cpanic=abort"])
        .arg(format!("-Copt-level={opt_level}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path)
        .output()
        .expect("spawn rustc (bridge)");
    let stderr = String::from_utf8_lossy(&output.stderr);
    if !output.status.success() {
        if stderr.contains("failing closed") || stderr.contains("unsupported") {
            return None;
        }
        panic!("bridge compile failed (not fail-closed) at -O{opt_level}: <<<{stderr}>>>");
    }
    assert!(
        !stderr.contains("Undefined symbols"),
        "bridge link has an undefined symbol at -O{opt_level}: <<<{stderr}>>>"
    );
    let code = Command::new(&bin)
        .status()
        .expect("run bridge binary")
        .code()
        .expect("bridge binary exit code");
    Some(code)
}

/// A runtime-`&str` `format!` program. `body` binds one or more `&str` locals to
/// `std::hint::black_box("...")` (an identity barrier, so the length is NOT a
/// compile-time constant to the bridge — the RUNTIME fat-pointer path) and builds a
/// `format!` String named `s` from them; the exit code is a 7-bit hash of `s`'s
/// BYTES — a strong content check. `format!` is used and consumed in-frame (a
/// String returned by value from a helper hits the unrelated return-escape guard).
fn rt_str_program(body: &str) -> String {
    format!(
        "#[inline(never)]\n\
         fn hash(s: &str) -> i32 {{\n\
         \x20   let mut h = 0i32;\n\
         \x20   for b in s.as_bytes() {{ h = h.wrapping_mul(31).wrapping_add(*b as i32); }}\n\
         \x20   h & 0x7f\n\
         }}\n\
         fn main() {{\n\
         \x20   {body}\n\
         \x20   std::process::exit(hash(&s));\n\
         }}\n"
    )
}

/// Every runtime-`&str` `format!` shape must be INTERCEPTED and its CONTENT must
/// MATCH the LLVM reference at -O0, -O2 AND -O3.
#[test]
fn runtime_str_format_content_matches_llvm_o0_o2_o3() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("content");

    // (body, label). Each binds runtime `&str` locals via `black_box` and builds a
    // `format!` String `s`; the exit code hashes its bytes.
    let cases: &[(&str, &str)] = &[
        // (a) prefix literal + one runtime &str: "hi world"
        (
            "let a: &str = std::hint::black_box(\"world\");\n\
             let s = format!(\"hi {}\", a);",
            "prefix + runtime &str",
        ),
        // (b) a bare runtime &str: "world"
        (
            "let a: &str = std::hint::black_box(\"world\");\n\
             let s = format!(\"{}\", a);",
            "bare runtime &str",
        ),
        // (c) two runtime &str back to back (two runtime copies): "worldXY"
        (
            "let a: &str = std::hint::black_box(\"world\");\n\
             let b: &str = std::hint::black_box(\"XY\");\n\
             let s = format!(\"{}{}\", a, b);",
            "two runtime &str",
        ),
        // (d) mixed runtime int + runtime &str: "n=42 s=x"
        (
            "let n: i32 = std::hint::black_box(42i32);\n\
             let a: &str = std::hint::black_box(\"x\");\n\
             let s = format!(\"n={} s={}\", n, a);",
            "mixed runtime int + &str",
        ),
        // (e) EMPTY runtime &str (len 0): "[]"
        (
            "let a: &str = std::hint::black_box(\"\");\n\
             let s = format!(\"[{}]\", a);",
            "empty runtime &str",
        ),
        // (f) LONG runtime &str (far exceeds the small static reserve): the runtime
        //     capacity must be sized to the runtime length, never under-copying.
        (
            "let a: &str = std::hint::black_box(\"the quick brown fox jumps over the lazy dog 0123456789\");\n\
             let s = format!(\"pre-{}-post\", a);",
            "long runtime &str",
        ),
        // (g) three runtime &str interleaved with literals: "<A|BB|CCC>"
        (
            "let a: &str = std::hint::black_box(\"A\");\n\
             let b: &str = std::hint::black_box(\"BB\");\n\
             let c: &str = std::hint::black_box(\"CCC\");\n\
             let s = format!(\"<{}|{}|{}>\", a, b, c);",
            "three interleaved runtime &str",
        ),
        // (h) non-ASCII (multi-byte UTF-8) runtime &str: bytes copied verbatim.
        (
            "let a: &str = std::hint::black_box(\"αβγ★\");\n\
             let s = format!(\"u:{}\", a);",
            "non-ascii runtime &str",
        ),
    ];

    let mut intercepted = 0usize;
    for (body, label) in cases {
        let src = rt_str_program(body);
        let llvm = run_llvm(&dir, &src);
        for opt in ["0", "2", "3"] {
            match run_bridge(&dir, &dylib, &src, opt) {
                Some(code) => {
                    assert_eq!(
                        code, llvm,
                        "O{opt} CONTENT MISMATCH for `{label}`: bridge={code} llvm={llvm}\nsrc:\n{src}"
                    );
                    intercepted += 1;
                }
                None => panic!(
                    "`{label}` unexpectedly FAILED CLOSED at O{opt} (a runtime &str format! should be intercepted)\nsrc:\n{src}"
                ),
            }
        }
    }
    assert_eq!(
        intercepted,
        cases.len() * 3,
        "every runtime &str format! case must be intercepted at O0/O2/O3"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// A runtime-`&str` placeholder with an UNSUPPORTED spec (Debug `{:?}`, a width /
/// precision, a float / i128 sibling) must NEVER miscompile: it either matches the
/// LLVM reference OR fails closed (`None`) — never a wrong content/length.
#[test]
fn runtime_str_unsupported_specs_never_miscompile() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("negative");

    let cases: &[(&str, &str)] = &[
        (
            "let a: &str = std::hint::black_box(\"world\");\n\
             let s = format!(\"{:?}\", a);",
            "Debug runtime &str",
        ),
        (
            "let a: &str = std::hint::black_box(\"hi\");\n\
             let s = format!(\"{:>5}\", a);",
            "width-padded runtime &str",
        ),
        (
            "let a: &str = std::hint::black_box(\"hello\");\n\
             let s = format!(\"{:.2}\", a);",
            "precision-truncated runtime &str",
        ),
        (
            "let f: f64 = std::hint::black_box(3.5f64);\n\
             let a: &str = std::hint::black_box(\"x\");\n\
             let s = format!(\"{} {}\", f, a);",
            "float sibling of a runtime &str",
        ),
        (
            "let n: u128 = std::hint::black_box(1u128);\n\
             let a: &str = std::hint::black_box(\"x\");\n\
             let s = format!(\"{} {}\", n, a);",
            "u128 sibling of a runtime &str",
        ),
    ];

    for (body, label) in cases {
        let src = rt_str_program(body);
        let llvm = run_llvm(&dir, &src);
        for opt in ["0", "2", "3"] {
            if let Some(code) = run_bridge(&dir, &dylib, &src, opt) {
                assert_eq!(
                    code, llvm,
                    "O{opt} MISCOMPILE for `{label}`: bridge={code} llvm={llvm} \
                     (an unsupported spec must fail closed, never produce a wrong value)\nsrc:\n{src}"
                );
            }
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}
