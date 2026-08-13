// Integration test: `String::from("literal")` / `String::from(&str)` /
// `str::to_string` / `str::to_owned` and String mutation compiled for
// x86_64 via the rustc_codegen_trust_cg bridge at `-O2`/`-O3` (STRFROM-1) —
// COMPILED, LINKED, and RUN, with exit codes checked against the default LLVM
// backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// At `-O2`/`-O3` rustc fully inlines `String::from(&str)` to the SROA'd
// `RawVecInner::try_allocate_in` allocation + an `if len > 0`-guarded
// `copy_nonoverlapping` whose SOURCE is a `&raw const (*const_str)` reborrow of
// the string literal. STRFROM-1 lands two sound pieces:
//   * the `to_vec` SROA recognizer now resolves an alloc-cap / copy-count taken
//     as `PtrMetadata` of a const `&str`/`&[T]` (a compile-time constant rustc
//     keeps as an SSA local) — so `try_allocate_in` is marked dead and its
//     buffer synthesized as `__rust_alloc(len * 1, 1)`;
//   * `lower_memory_slice_assign`'s `&raw const (*src)` reborrow arm reconstructs
//     the const-slice `{ data, len }` from the const-str binding (was
//     fail-closed on `Rvalue::RawPtr`), providing the guarded copy's source.
//
// The differential pins CONTENT, not just lengths: byte reads through
// `as_bytes`, a multi-byte pattern, `push`/`push_str` appends read past the
// original length, independent backing for multiple strings, and a `&str`
// PARAMETER source. The negative test pins that shapes we
// cannot lower soundly stay FAIL-CLOSED (never a silent wrong value):
// `String::clone` (until a faithful deep-copy lowering exists), the EMPTY
// string at `-O2`/`-O3` (`try_allocate_in(0)` returns a dangling `NonNull` with
// NO allocation, so `__rust_alloc(0)` is rejected — a completeness gap, sound),
// a `Box` (needs-drop) element, a USER method named `to_vec`, and a user fn
// RETURNING a `String` by value (the collection return-escape guard).

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
    assert!(status.success(), "cargo build failed; cannot run test");
    let built = target_dir
        .join("debug")
        .join("librustc_codegen_trust_cg.dylib");
    assert!(
        built.exists(),
        "expected dylib at {built:?} but none produced"
    );
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
    let dir = std::env::temp_dir().join(format!("rcl2_m129_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

fn try_compile(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt: &str,
) -> (std::process::Output, PathBuf) {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);

    let mut cmd = Command::new("rustup");
    cmd.args([
        "run",
        pinned_toolchain().as_str(),
        "rustc",
        "--edition=2021",
    ])
    .args(["--crate-type", "bin"]);
    if let Some(dylib) = backend {
        cmd.arg(backend_arg(dylib));
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort"])
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    (output, bin)
}

fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>, opt: &str) -> PathBuf {
    let (output, bin) = try_compile(dir, name, src, backend, opt);
    assert!(
        output.status.success(),
        "compile of `{name}` failed ({} backend, opt={opt}). stderr: <<<{}>>>",
        if backend.is_some() {
            "trust-cg"
        } else {
            "llvm"
        },
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

/// `String::from(&str)` / literal / `to_string` / `to_owned` / mutation
/// compiled by trust-cg AND LLVM at EVERY opt level, run, and the exit codes
/// must match each other and the expected value. Content (byte reads, a
/// multi-byte pattern, appended bytes, independent backing for multiple
/// strings, and a `&str` PARAMETER source) is part of every exit code, so a
/// wrong copied byte, wrong length, dropped append, or aliased pair diverges.
/// The `-O2`/`-O3` cases are the STRFROM-1 capability (the fully-SROA'd
/// `try_allocate_in` + guarded const-str copy).
#[test]
fn string_from_and_content_match_llvm_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("run");

    // (name, source, expected exit code).
    let shapes: &[(&str, &str, i32)] = &[
        // `String::from("literal").len()` — the fully-SROA'd immediate-consume shape.
        (
            "string_from_len",
            "fn main() { let s = String::from(\"hello\"); \
             std::process::exit(s.len() as i32); }",
            5,
        ),
        // Byte CONTENT via `as_bytes` (a wrong copied byte diverges): 'A'+'B'+'C'.
        (
            "string_from_content",
            "fn main() { let s = String::from(\"ABC\"); let b = s.as_bytes(); \
             std::process::exit(b[0] as i32 + b[1] as i32 + b[2] as i32); }",
            198,
        ),
        // A longer literal's length (the alloc size is `PtrMetadata(const str)`).
        (
            "string_from_long_len",
            "fn main() { let s = String::from(\"the quick brown fox jumps\"); \
             std::process::exit(s.len() as i32); }",
            25,
        ),
        // `str::to_string` + `str::to_owned` length + byte content ('z' = 122).
        (
            "to_string_and_to_owned",
            "fn main() { let s = \"xyz\".to_string(); let t = \"qq\".to_owned(); \
             std::process::exit(s.len() as i32 * 10 + t.len() as i32 + s.as_bytes()[2] as i32); }",
            154,
        ),
        // `String::from(&str PARAMETER)` — a runtime fat-pointer source, len*3 + 'a'.
        (
            "string_from_str_param",
            "#[inline(never)] fn mk(a: &str) -> i32 { let s = String::from(a); \
             s.len() as i32 * 3 + s.as_bytes()[0] as i32 } \
             fn main() { std::process::exit(mk(\"abc\")); }",
            106,
        ),
        // `push_str` appends: read a byte PAST the original length ('!' at index 6).
        (
            "push_str_append_content",
            "fn main() { let mut s = String::from(\"foo\"); s.push_str(\"bar!\"); \
             std::process::exit(s.len() as i32 + s.as_bytes()[6] as i32); }",
            40,
        ),
        // `push(char)` must mutate the content-bearing slot adopted by String.
        (
            "push_char_preserves_from_content",
            "fn main() { let mut s = String::from(\"ab\"); s.push('Z'); \
             std::process::exit(s.len() as i32 * 10 + s.as_bytes()[2] as i32 - 80); }",
            40,
        ),
        // At O2/O3 rustc may CSE the empty Vec used by both constructors. The
        // Strings still require distinct backing slots once either is mutated.
        (
            "two_string_new_slots_are_independent",
            "fn main() { let mut a = String::new(); let mut b = String::new(); \
             a.push_str(\"ab\"); b.push_str(\"xyz\"); \
             std::process::exit(a.len() as i32 * 10 + b.len() as i32); }",
            23,
        ),
        // Content-bearing Vec slots from separate String::from constructions
        // must both be preserved and remain mutually independent.
        (
            "two_string_from_slots_are_independent",
            "fn main() { let mut a = String::from(\"ab\"); let mut b = String::from(\"XY\"); \
             a.push_str(\"c\"); b.push_str(\"Z!\"); let aa = a.as_bytes(); let bb = b.as_bytes(); \
             std::process::exit(a.len() as i32 * 40 + b.len() as i32 * 10 \
                 + aa[2] as i32 - 90 + bb[3] as i32 - 30); }",
            172,
        ),
        // Both constructor orders pin that claiming an empty slot never causes
        // a later content-bearing slot (or vice versa) to be replaced or aliased.
        (
            "string_from_then_new_slots_are_independent",
            "fn main() { let mut a = String::from(\"hi\"); let mut b = String::new(); \
             a.push_str(\"!\"); b.push_str(\"q\"); let aa = a.as_bytes(); let bb = b.as_bytes(); \
             std::process::exit(a.len() as i32 * 30 + b.len() as i32 * 10 \
                 + aa[2] as i32 - 30 + bb[0] as i32 - 100); }",
            116,
        ),
        (
            "string_new_then_from_slots_are_independent",
            "fn main() { let mut a = String::new(); let mut b = String::from(\"ok\"); \
             a.push_str(\"rs\"); b.push_str(\"!\"); let aa = a.as_bytes(); let bb = b.as_bytes(); \
             std::process::exit(a.len() as i32 * 30 + b.len() as i32 * 10 \
                 + aa[1] as i32 - 100 + bb[2] as i32 - 30); }",
            108,
        ),
        // Gap-A: `\"abc\".as_bytes()` + a `&raw const (*b)` reborrow, indexed [0] = 'a'.
        (
            "gap_a_raw_const_reborrow",
            "#[inline(never)] fn m() -> i32 { let b = \"abc\".as_bytes(); \
             let p = &raw const *b; unsafe { (*p)[0] as i32 } } \
             fn main() { std::process::exit(m()); }",
            97,
        ),
    ];

    for opt in ["0", "2", "3"] {
        for (name, src, expected) in shapes {
            let llvm_bin = compile(&dir, &format!("{name}_llvm_o{opt}"), src, None, opt);
            let llvm_exit = run_exit_code(&llvm_bin);
            let tcg_bin = compile(&dir, &format!("{name}_tcg_o{opt}"), src, Some(&dylib), opt);
            let tcg_exit = run_exit_code(&tcg_bin);
            assert_eq!(
                tcg_exit, llvm_exit,
                "`{name}` (opt={opt}): trust-cg exit {tcg_exit} != LLVM exit {llvm_exit} (MISCOMPILE)"
            );
            assert_eq!(
                tcg_exit, *expected,
                "`{name}` (opt={opt}): exit {tcg_exit} != expected {expected}"
            );
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// A String clone needs a fresh buffer and a byte-for-byte copy. Until that
/// lowering exists, every content-observing clone shape must fail closed with
/// the dedicated diagnostic at every optimization level; the old general-call
/// fallback produced invalid pointers and shipped crashing binaries.
#[test]
fn string_clone_stays_fail_closed_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("clone_neg");

    let shapes: &[(&str, &str)] = &[
        (
            "string_clone_read_content",
            "fn main() { let s = String::from(\"abc\"); let c = s.clone(); \
             std::process::exit(c.as_bytes()[1] as i32); }",
        ),
        (
            "string_clone_then_mutate",
            "fn main() { let mut s = String::new(); s.push_str(\"ab\"); \
             let mut c = s.clone(); c.push_str(\"z\"); std::process::exit(c.len() as i32); }",
        ),
        (
            "to_owned_string_clone",
            "fn main() { let s = \"content\".to_owned(); let c = s.clone(); \
             std::process::exit(c.as_bytes()[6] as i32); }",
        ),
        (
            "multiple_string_clones",
            "fn main() { let s = String::from(\"xy\"); let a = s.clone(); let b = s.clone(); \
             std::process::exit(a.len() as i32 * 10 + b.len() as i32); }",
        ),
    ];

    for opt in ["0", "2", "3"] {
        for (name, src) in shapes {
            let (output, _bin) =
                try_compile(&dir, &format!("{name}_tcg_o{opt}"), src, Some(&dylib), opt);
            assert!(
                !output.status.success(),
                "`{name}` (opt={opt}): expected String::clone to fail closed, but it compiled"
            );
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                stderr.contains("TCG-STRING-CLONE"),
                "`{name}` (opt={opt}): missing [TCG-STRING-CLONE] diagnostic: <<<{stderr}>>>"
            );
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Shapes we cannot lower SOUNDLY stay FAIL-CLOSED (a loud
/// `[TCG-MIR-UNSUPPORTED]`, never a wrong value): the EMPTY string at
/// `-O2`/`-O3` (`try_allocate_in(0)` is a dangling `NonNull` with NO allocation —
/// a `0`-capacity alloc is rejected; the O0 real-call path handles it, so this is
/// a bounded completeness gap, not a miscompile), a `Box` (needs-drop) element,
/// a USER method named `to_vec` (must not be misrouted into the std
/// interception), and a user fn RETURNING a `String` by value (the collection
/// return-escape guard — its `{ptr,cap,len}` slot would die with the callee frame
/// at O0).
#[test]
fn unsupported_string_from_shapes_stay_fail_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("neg");

    // (name, source, opt, needle).
    let negatives: &[(&str, &str, &str, &str)] = &[
        (
            "empty_string_from_o2",
            "fn main() { let s = String::from(\"\"); std::process::exit(s.len() as i32 + 42); }",
            "2",
            "TCG-MIR-UNSUPPORTED",
        ),
        (
            "empty_string_from_o3",
            "fn main() { let s = String::from(\"\"); std::process::exit(s.len() as i32 + 42); }",
            "3",
            "TCG-MIR-UNSUPPORTED",
        ),
        (
            "box_element_to_vec_o3",
            "fn main() { let v = [Box::new(1i64), Box::new(2)].to_vec(); \
             std::process::exit(*v[0] as i32); }",
            "3",
            "TCG-MIR-UNSUPPORTED",
        ),
        (
            "user_to_vec_not_misrouted",
            "struct W; impl W { fn to_vec(&self) -> Vec<u8> { \
             let mut v = Vec::new(); v.push(9); v } } \
             fn main() { let v = W.to_vec(); std::process::exit(v[0] as i32); }",
            "3",
            "is not an intercepted Vec method",
        ),
        (
            "string_return_escape_guard_o0",
            "fn make() -> String { String::from(\"esc\") } \
             fn main() { let a = make(); std::process::exit(a.len() as i32 + 41); }",
            "0",
            "returning an intercepted collection",
        ),
    ];

    for (name, src, opt, needle) in negatives {
        let (output, _bin) = try_compile(&dir, name, src, Some(&dylib), opt);
        assert!(
            !output.status.success(),
            "`{name}` (opt={opt}): expected trust-cg to FAIL CLOSED but it compiled"
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(needle),
            "`{name}` (opt={opt}): fail-closed message does not contain {needle:?}: <<<{stderr}>>>"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}
