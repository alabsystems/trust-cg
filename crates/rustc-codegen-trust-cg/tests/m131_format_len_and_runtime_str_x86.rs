// Integration test: two `format!` SILENT-MISCOMPILE classes found by the FUZZ-1
// differential sweep over the runtime-`&str` `format!` surface (RTFMT-1), now
// closed by sound fail-closed gates. Each shape is compiled for x86_64 through the
// rustc_codegen_trust_cg bridge at -O0/-O2/-O3 alongside the default LLVM backend,
// and the INVARIANT asserted is: trust-cg either FAILS CLOSED (refuses to compile)
// OR produces the EXACT SAME exit code as LLVM — it must NEVER produce a different
// (wrong) value.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// CLASS 1 [TCG-FMT-LEN]: an INTEGER `format!` placeholder whose value derives from
// a slice/`str` `.len()` (`format!("{}#{}", a, a.len())` where `a` is a
// const-length `&str` binding). The `str::len` result is an undefined SSA value
// the isel catches when read directly ([TCG-REGALLOC-063], fail-closed), but the
// format integer emitter re-read it as a `Load` from an UNINITIALIZED slot,
// DEFEATING that guard and printing a stale garbage integer (differential:
// `a.len()==7` printed as `4096`, so `"measure#7"` became `"measure#4096"`). Now
// the classifier rejects any integer placeholder whose value transitively depends
// on a length.
//
// CLASS 2 [TCG-FMT-RTSTR]: a GENUINE runtime-length `&str` placeholder (no
// compile-time length), e.g. a pre-bound `String::as_str()` view: `let a =
// owned.as_str(); format!("({})", a)`. The runtime `(data, len)` resolution
// resolved a WRONG `(data, len)` and silently copied zero / garbage bytes
// (differential: `"(dynamic)"` became `"()"`). Now the genuine-runtime path fails
// closed. (Every SHIPPED runtime-`&str` fixture binds a `black_box("literal")`
// whose length is statically recovered — those take the CONST path and are
// unaffected; this file also pins two of them as a regression guard.)
//
// The hard invariant: a WRONG value is a P0 STOP; a fail-closed compile is SOUND.

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
    let dir = std::env::temp_dir().join(format!("rcl2_m131_{stem}_{}", std::process::id()));
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
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
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

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// `hash(&str)`: an `#[inline(never)]` byte-content hash folded to 7 bits — a
/// strong content check on the whole formatted string.
const HASH: &str = "#[inline(never)] fn hash(s: &str) -> i32 { let mut h = 0i32; \
     for b in s.as_bytes() { h = h.wrapping_mul(31).wrapping_add(*b as i32); } h & 0x7f }\n";

/// THE CORE INVARIANT: trust-cg either fails closed OR matches LLVM — never a
/// wrong value. `program` returns a String `s`; the exit code hashes its bytes, so
/// a wrong length OR a wrong byte would diverge.
fn assert_failclosed_or_matches(dylib: &Path, dir: &Path, name: &str, body: &str) {
    let src = format!(
        "#![allow(unused)]\nuse std::hint::black_box as bb;\n{HASH}\
         fn main() {{ {body} std::process::exit(hash(&s)); }}\n"
    );
    for opt in ["0", "2", "3"] {
        // LLVM is the reference; it must always compile and run.
        let (lout, lbin) = try_compile(dir, &format!("{name}_l"), &src, None, opt);
        assert!(
            lout.status.success(),
            "LLVM compile of `{name}` (opt={opt}) failed: {}",
            String::from_utf8_lossy(&lout.stderr)
        );
        let llvm = run_exit_code(&lbin);

        let (tout, tbin) = try_compile(dir, &format!("{name}_t"), &src, Some(dylib), opt);
        if !tout.status.success() {
            // Fail-closed is SOUND — the whole point of the fix.
            continue;
        }
        let tcg = run_exit_code(&tbin);
        assert_eq!(
            tcg, llvm,
            "[P0 MISCOMPILE] `{name}` (opt={opt}): trust-cg produced a WRONG value \
             tcg={tcg} vs llvm={llvm} (must fail closed OR match)"
        );
    }
}

/// CLASS 1 + CLASS 2 shapes: each must fail closed or match LLVM at every opt
/// level. These are the exact minimized reproducers the FUZZ-1 sweep flagged as
/// SILENT MISCOMPILES before the fix.
#[test]
fn format_len_and_runtime_str_never_miscompile() {
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

    let shapes: &[(&str, &str)] = &[
        // ---- CLASS 1 [TCG-FMT-LEN]: integer placeholder = a `.len()` ----
        // The canonical repro: `a.len()` printed as a stale `4096`.
        (
            "len_after_str",
            "let a: &str = bb(\"measure\"); let s = format!(\"{}#{}\", a, a.len());",
        ),
        // The int BEFORE the runtime str (position is irrelevant to the bug).
        (
            "len_before_str",
            "let a: &str = bb(\"measure\"); let n: usize = a.len(); \
             let s = format!(\"{}#{}\", n, a);",
        ),
        // Laundered through arithmetic — still a length dependency.
        (
            "len_plus_zero",
            "let a: &str = bb(\"measure\"); let s = format!(\"{}#{}\", a, a.len() + bb(0usize));",
        ),
        // A length as the SOLE placeholder.
        (
            "len_only",
            "let a: &str = bb(\"hello\"); let s = format!(\"L={}\", a.len());",
        ),
        // ---- CLASS 2 [TCG-FMT-RTSTR]: genuine runtime-length `&str` ----
        // Pre-bound `String::as_str()` view: printed `"()"` (copied 0 bytes).
        (
            "rtstr_asstr_prebound",
            "let mut owned = String::from(bb(\"dyn\")); owned.push_str(bb(\"amic\")); \
             let a: &str = owned.as_str(); let s = format!(\"({})\", a);",
        ),
        // `String::from` view, pre-bound.
        (
            "rtstr_from_view",
            "let owned = String::from(bb(\"dynamic\")); let a: &str = owned.as_str(); \
             let s = format!(\"({})\", a);",
        ),
        // A runtime `&str` fn-param view (a distinct provenance).
        (
            "rtstr_param",
            "#[inline(never)] fn go(a: &str) -> String { format!(\"<{}>\", a) } \
             let s = go(bb(\"measure\"));",
        ),
        // ---- REGRESSION GUARD: the CONST-length path must STILL WORK ----
        // A `black_box` literal has a statically-recovered length (the shipped
        // RTFMT-1 surface) — it takes the const path and must MATCH LLVM (not fail
        // closed). If the fail-closed gate ever widens to swallow these, the
        // assert_eq inside catches the divergence but they must also COMPILE.
        (
            "const_len_still_works_bare",
            "let a: &str = bb(\"world\"); let s = format!(\"{}\", a);",
        ),
        (
            "const_len_still_works_mixed",
            "let a: &str = bb(\"x\"); let n: i32 = bb(42); let s = format!(\"n={} s={}\", n, a);",
        ),
    ];

    for (name, body) in shapes {
        assert_failclosed_or_matches(&dylib, &dir, name, body);
    }
}

/// A focused positive check that the two CONST-length regression-guard shapes do
/// NOT fail closed (they are the actually-shipped, fixture-covered surface): at
/// least one opt level must produce a running binary that matches LLVM. This
/// guards against the fail-closed gates over-reaching into the working path.
#[test]
fn const_length_runtime_str_still_compiles_and_matches() {
    if !host_is_x86_64() || !x86_64_std_available() {
        eprintln!("skipping: needs x86_64 host + rust-std for {TARGET}");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("const");
    let src = format!(
        "#![allow(unused)]\nuse std::hint::black_box as bb;\n{HASH}\
         fn main() {{ let a: &str = bb(\"world\"); let s = format!(\"hi {{}}\", a); \
         std::process::exit(hash(&s)); }}\n"
    );
    let mut compiled_any = false;
    for opt in ["0", "2", "3"] {
        let (lout, lbin) = try_compile(&dir, "cl_l", &src, None, opt);
        assert!(lout.status.success(), "LLVM compile failed");
        let llvm = run_exit_code(&lbin);
        let (tout, tbin) = try_compile(&dir, "cl_t", &src, Some(&dylib), opt);
        if tout.status.success() {
            compiled_any = true;
            assert_eq!(run_exit_code(&tbin), llvm, "const-length format! diverged at opt={opt}");
        }
    }
    assert!(
        compiled_any,
        "const-length `format!(\"hi {{}}\", black_box(\"world\"))` must compile on trust-cg \
         at some opt level (the shipped RTFMT-1 surface) — it fully failed closed"
    );
}
