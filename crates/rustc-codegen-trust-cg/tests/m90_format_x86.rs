// Integration test: `format!` / `write!` / `Display`-based string formatting of
// basic types, compiled + run for x86_64 via the rustc_codegen_trust_cg bridge
// and DIFFERENTIALLY compared against rustc's default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: task #49 — `format!`/Display via interception.
//
// The bridge INTERCEPTS the `core::fmt` entry points the `format!` macro lowers
// to (`Arguments::new` / `Argument::new_display` / `alloc::fmt::format`) and
// SYNTHESIZES the formatted bytes directly into a `{ ptr, cap, len }` String slot
// — it never calls the (unlowerable) `core::fmt` Formatter/Arguments trait-object
// machinery. A SOUND PARTIAL covering the common case is supported:
//
//   * a `Display` placeholder of an INTEGER (any width, signed/unsigned), `&str`,
//     `char`, or `bool`, with NO flags / width / precision (plain `{}`),
//   * literal-piece + placeholder mixing (`"a{}b{}c"`), and multi-arg concat.
//
// Integer formatting is a branchless unrolled itoa (sign + leading-zero
// suppression); `bool`/`char` are branchless byte writes; `&str` is an unrolled
// byte copy of its compile-time-known length. Anything outside the subset (Debug,
// hex/octal, padding `{:>5}`, named/positional args, a non-primitive Display)
// FAILS CLOSED — it never miscompiles.
//
// LEVEL SCOPE: `format!` works at BOTH -Copt-level=0 AND -O2/-O3. At -O2/-O3
// rustc INLINES `alloc::fmt::format(args)` into
// `args.as_str().map_or_else(|| <closure: format>, str::to_owned)` (a
// `Option::<&str>::map_or_else` call whose closure captures `&Arguments`). The
// bridge RECOGNIZES that inlined consumer and synthesizes the SAME formatted
// String — both `map_or_else` arms produce `format(args)` — using the identical
// itoa/char/str emit helpers as the O0 path, and drops the dead `as_str()`
// niche-check region (its `SwitchInt` is replaced by an unconditional branch).
// So `format!` MATCHES LLVM at O0 AND O3. `write!` at -O2/-O3 fully inlines the
// `String::push_str` -> `Vec::extend_from_slice` -> `RawVec` grow +
// `copy_nonoverlapping` byte-append machinery (there is no `write_fmt` call to
// intercept and the bridge does not model `copy_nonoverlapping` / `RawVec`
// realloc), so `write!` still FAILS CLOSED at -O2/-O3 (a SAFE coverage gap, never
// a miscompile). The tests assert the O0 AND O3 runs match LLVM for `format!`, and
// that anything outside the supported subset (Debug, width/precision, hex; and
// `write!` at O3) either matches OR fails closed (never a wrong answer).

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
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run m90 format test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m90_{stem}_{}", std::process::id()));
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
        // A fail-closed diagnostic (the bridge refusing an unsupported shape) is an
        // ACCEPTED outcome — it is never a miscompile. Any OTHER failure (a real
        // ISel/link bug) is not.
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

/// A `format!` program that builds a String and exits with a value derived from
/// it. `expr` is the formatted expression; `exit_expr` derives the exit code from
/// the String `s`.
fn fmt_program(let_binding: &str, exit_expr: &str) -> String {
    format!(
        "fn main() {{\n    {let_binding}\n    std::process::exit({exit_expr});\n}}\n"
    )
}

/// Every accepted `format!` case must be INTERCEPTED and MATCH the LLVM reference
/// at BOTH -O0 AND -O3 (the inlined `map_or_else` consumer is recognized at O3).
#[test]
fn format_basic_types_match_llvm_at_o0_and_o3() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("basic");

    // (let-binding, exit-expr, human label). Each exits with the String's byte
    // LENGTH — a strong check on the itoa digit count, sign handling, char/bool
    // byte count, &str length, and literal-piece concatenation.
    let cases: &[(&str, &str, &str)] = &[
        ("let s = format!(\"{}\", std::hint::black_box(42i32));", "s.len() as i32", "int 42 -> 2"),
        ("let s = format!(\"{}\", std::hint::black_box(-12345i32));", "s.len() as i32", "int -12345 -> 6"),
        ("let s = format!(\"{}\", std::hint::black_box(0u32));", "s.len() as i32", "uint 0 -> 1"),
        ("let s = format!(\"{}\", std::hint::black_box(i32::MIN));", "s.len() as i32", "i32::MIN -> 11"),
        ("let s = format!(\"{}\", std::hint::black_box(255u8));", "s.len() as i32", "u8 255 -> 3"),
        ("let s = format!(\"{}\", std::hint::black_box(-9223372036854775808i64));", "s.len() as i32", "i64::MIN -> 20"),
        ("let s = format!(\"{}\", std::hint::black_box(true));", "s.len() as i32", "bool true -> 4"),
        ("let s = format!(\"{}\", std::hint::black_box(false));", "s.len() as i32", "bool false -> 5"),
        ("let s = format!(\"{}\", std::hint::black_box('Z'));", "s.len() as i32", "char Z -> 1"),
        ("let s = format!(\"{}\", std::hint::black_box('é'));", "s.len() as i32", "char é -> 2 (UTF-8)"),
        ("let s = format!(\"{}\", std::hint::black_box(\"hello\"));", "s.len() as i32", "&str hello -> 5"),
        ("let s = format!(\"{}{}\", std::hint::black_box(42i32), std::hint::black_box(\"x\"));", "s.len() as i32", "concat 42x -> 3"),
        ("let s = format!(\"a{}b{}c\", std::hint::black_box(1i32), std::hint::black_box(22i32));", "s.len() as i32", "lit-mix a1b22c -> 6"),
        // A `&str` placeholder through a PLAIN LOCAL (no black_box): the local
        // is a const-slice binding (`lower_const_slice_use` — data pointer in
        // `scalar_values`, length in the `pointer_metadata_lengths` side
        // table). PINS the Str-arm data-half resolution: the place kernel
        // deliberately rejects reading a metadata-bound local as a plain
        // scalar, so `emit_format_one_placeholder` resolves the data half
        // directly from `scalar_values` (this shape failed closed with
        // "pointer metadata-only reference used as scalar" before).
        ("let name = \"trust\"; let s = format!(\"hi, {}!\", name);", "s.len() as i32", "&str via plain local -> 10"),
        // FULLY-CONST-FOLDED `format!`: a plain literal arg (no black_box, no
        // variable) is folded by rustc itself into
        // `Arguments::from_str_nonconst(const "42")` (O0 call, decoded by
        // `decode_from_str_nonconst`) / the tagged-pointer `Arguments` struct
        // literal (O2/O3, decoded by `decode_o3_inlined_literal_arguments` +
        // the `trace_fmt_niche_scratch` tagged-literal terminal). Both failed
        // closed on `Ty::core::fmt::rt::ArgumentType` before.
        ("let s = format!(\"{}\", 42);", "s.len() as i32", "folded literal int -> 2"),
        // The explicit-literal builder (`Arguments::from_str`, no placeholder).
        ("let s = format!(\"hello\");", "s.len() as i32", "plain literal -> 5"),
        // Folded literal-mix (placeholders + pieces all folded to one string).
        ("let s = format!(\"x{}y{}z\", 1, \"ab\");", "s.len() as i32", "folded lit-mix x1yabz -> 6"),
    ];

    let mut intercepted_o0 = 0usize;
    let mut intercepted_o3 = 0usize;
    for (binding, exit_expr, label) in cases {
        let src = fmt_program(binding, exit_expr);
        let llvm = run_llvm(&dir, &src);

        match run_bridge(&dir, &dylib, &src, "0") {
            Some(code) => {
                assert_eq!(
                    code, llvm,
                    "O0 MISMATCH for `{label}`: bridge={code} llvm={llvm}\nsrc: {src}"
                );
                intercepted_o0 += 1;
            }
            None => panic!("`{label}` unexpectedly FAILED CLOSED at O0 (should be intercepted)"),
        }

        match run_bridge(&dir, &dylib, &src, "3") {
            Some(code) => {
                assert_eq!(
                    code, llvm,
                    "O3 MISMATCH for `{label}`: bridge={code} llvm={llvm} (a miscompile!)\nsrc: {src}"
                );
                intercepted_o3 += 1;
            }
            None => panic!("`{label}` unexpectedly FAILED CLOSED at O3 (should be intercepted)"),
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(
        intercepted_o0,
        cases.len(),
        "every accepted format! case must be intercepted at O0"
    );
    assert_eq!(
        intercepted_o3,
        cases.len(),
        "every accepted format! case must be intercepted at O3"
    );
}

/// CONTENT check (not just byte length): for each accepted `format!` case, exit
/// with a 31-rolling-hash of the formatted bytes (indexed via `as_bytes()[i]`, no
/// iterator). This catches a wrong DIGIT / sign / byte value that a length-only
/// check would miss. The check is asserted at -O3 (where the runtime-length
/// `as_bytes()` fat pointer + indexing loop the harness uses lowers); the same
/// reader FAILS CLOSED at -O0 (the bridge's O0 slice-metadata side table carries
/// only compile-time-constant lengths), which is a limitation of the verifier
/// HARNESS, not of `format!` (the O0 format bytes are themselves correct — the
/// length test above already exercises the O0 itoa/char/str emit). So O0 is allowed
/// to fail closed here; O3 must match LLVM byte-for-byte.
#[test]
fn format_byte_content_matches_llvm_at_o3() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("content");

    // Each binding builds `s`; the harness hashes its bytes deterministically.
    let bindings: &[(&str, &str)] = &[
        ("let s = format!(\"{}\", std::hint::black_box(42i64));", "int 42"),
        ("let s = format!(\"{}\", std::hint::black_box(-12345i32));", "neg -12345"),
        ("let s = format!(\"{}\", std::hint::black_box(255u8));", "u8 255"),
        ("let s = format!(\"{}\", std::hint::black_box(0u32));", "uint 0"),
        ("let s = format!(\"{}\", std::hint::black_box(i32::MIN));", "i32::MIN"),
        ("let s = format!(\"{}\", std::hint::black_box(-9223372036854775808i64));", "i64::MIN"),
        ("let s = format!(\"{}\", std::hint::black_box(u64::MAX));", "u64::MAX"),
        ("let s = format!(\"{}\", std::hint::black_box(true));", "bool true"),
        ("let s = format!(\"{}\", std::hint::black_box(false));", "bool false"),
        ("let s = format!(\"{}\", std::hint::black_box('Z'));", "char Z"),
        ("let s = format!(\"{}\", std::hint::black_box('é'));", "char é"),
        ("let s = format!(\"{}\", std::hint::black_box(\"hello world\"));", "&str"),
        ("let s = format!(\"{}{}\", std::hint::black_box(42i32), std::hint::black_box(\"x\"));", "concat"),
        ("let s = format!(\"a{}b{}c\", std::hint::black_box(1i32), std::hint::black_box(22i32));", "lit-mix"),
        ("let s = format!(\"val={} ok={}\", std::hint::black_box(-7i64), std::hint::black_box(true));", "mixed"),
        // CONTENT pin for the Str-arm data-half resolution (`&str` via a plain
        // local, a const-slice binding): a wrong data POINTER (not just a wrong
        // length) would surface here as a byte-hash mismatch.
        ("let name = \"trust\"; let s = format!(\"hi, {}!\", name);", "&str via plain local"),
        // CONTENT pins for the fully-const-folded `format!` (the O2/O3
        // tagged-pointer literal `Arguments` decode): wrong bytes, a wrong
        // literal, or a wrongly-neutralized niche switch would all surface.
        ("let s = format!(\"{}\", 42);", "folded literal int"),
        ("let s = format!(\"x{}y{}z\", 1, \"ab\");", "folded lit-mix"),
    ];

    for (binding, label) in bindings {
        let src = format!(
            "fn main() {{\n    {binding}\n    let b = s.as_bytes();\n    \
             let mut acc: i32 = 0;\n    let mut i = 0usize;\n    \
             while i < b.len() {{ acc = (acc.wrapping_mul(31).wrapping_add(b[i] as i32)) % 1000; i += 1; }}\n    \
             std::process::exit(((acc % 250) + 250) % 250);\n}}\n"
        );
        let llvm = run_llvm(&dir, &src);
        // O3: the format synthesis AND the runtime-length byte-indexing reader both
        // lower — the content MUST match LLVM (a wrong byte would surface here).
        match run_bridge(&dir, &dylib, &src, "3") {
            Some(code) => assert_eq!(
                code, llvm,
                "content MISMATCH for `{label}` at -O3: bridge={code} llvm={llvm}\nsrc: {src}"
            ),
            None => panic!("`{label}` unexpectedly FAILED CLOSED at -O3 (content check)"),
        }
        // O0: the byte-indexing reader fails closed (constant-length slice
        // metadata); if it ever DOES compile it must still match (never a wrong
        // answer).
        if let Some(code) = run_bridge(&dir, &dylib, &src, "0") {
            assert_eq!(
                code, llvm,
                "content MISMATCH for `{label}` at -O0: bridge={code} llvm={llvm}\nsrc: {src}"
            );
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// `write!(s, "{}", x)` appends to an existing String. At O0 the bridge intercepts
/// `<String as Write>::write_fmt`; the run must match the LLVM reference.
#[test]
fn write_fmt_appends_match_llvm_at_o0() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("write");

    // A `String::new()` + two `write!`s building "ab12" (len 4).
    let src = "use std::fmt::Write;\n\
        fn main() {\n\
        \x20   let mut s = String::new();\n\
        \x20   write!(s, \"{}\", std::hint::black_box(\"ab\")).unwrap();\n\
        \x20   write!(s, \"{}\", std::hint::black_box(12i32)).unwrap();\n\
        \x20   std::process::exit(s.len() as i32);\n\
        }\n";

    let llvm = run_llvm(&dir, src);
    match run_bridge(&dir, &dylib, src, "0") {
        Some(code) => assert_eq!(code, llvm, "write! O0 mismatch: bridge={code} llvm={llvm}"),
        None => panic!("write! unexpectedly failed closed at O0 (should be intercepted)"),
    }
    // O3 fully inlines `write_fmt` -> `String::push_str` -> `extend_from_slice` ->
    // `RawVec` grow + `copy_nonoverlapping` (no `write_fmt` call to intercept; the
    // bridge models neither `copy_nonoverlapping` nor `RawVec` realloc), so `write!`
    // FAILS CLOSED at O3 — a SAFE coverage gap. It must never miscompile: fail
    // closed (None) or match.
    if let Some(code) = run_bridge(&dir, &dylib, src, "3") {
        assert_eq!(code, llvm, "write! O3 MISMATCH (miscompile): bridge={code} llvm={llvm}");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// A format shape OUTSIDE the accepted subset (a Debug placeholder `{:?}` of a
/// tuple) must FAIL CLOSED at every opt level — never produce an object that runs
/// to a wrong answer.
#[test]
fn unsupported_format_fails_closed_not_miscompiles() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("unsupported");

    let cases: &[(&str, &str)] = &[
        // `{:?}` Debug of a tuple — the bridge does not synthesize Debug
        // formatting.
        (
            "debug_tuple",
            "fn main() {\n\
             \x20   let s = format!(\"{:?}\", std::hint::black_box((1i32, 2i32)));\n\
             \x20   std::process::exit(s.len() as i32);\n\
             }\n",
        ),
        // A BRANCH-VARYING `&str` placeholder: `name` is assigned in BOTH arms
        // (`if c { \"trust\" } else { \"cg\" }`), so it has no single
        // compile-time length. PINS a fixed SILENT MISCOMPILE: the `&str`
        // length reader (`str_arg_static_len`) fell back to
        // `find_local_assign`, which returns the FIRST assignment in block
        // order without checking uniqueness — it credited the not-taken
        // \"trust\" arm's length (5) and produced \"hi, cg!##\" with len 10
        // instead of LLVM's 7 at O0/O2/O3. The fix
        // (`local_has_unique_direct_def`) rejects multi-def value locals, so
        // this must now fail closed (or, if a future runtime-length lowering
        // lands, MATCH — never a wrong answer). `black_box(false)` selects the
        // arm the buggy reader did NOT credit, so a first-scanned-def
        // regression cannot sneak past as an accidental match.
        (
            "branch_varying_str",
            "fn main() {\n\
             \x20   let c = std::hint::black_box(false);\n\
             \x20   let name: &str = if c { \"trust\" } else { \"cg\" };\n\
             \x20   let s = format!(\"hi, {}!\", name);\n\
             \x20   std::process::exit(s.len() as i32);\n\
             }\n",
        ),
    ];

    for (case, src) in cases {
        for opt in ["0", "2", "3"] {
            // The only accepted outcomes are: fail closed (None) or match LLVM.
            // A mismatch would be a miscompile.
            if let Some(code) = run_bridge(&dir, &dylib, src, opt) {
                let llvm = run_llvm(&dir, src);
                assert_eq!(
                    code, llvm,
                    "unsupported format case `{case}` at -O{opt} ran to a WRONG \
                     answer (bridge={code} llvm={llvm}) — must fail closed or match"
                );
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}
