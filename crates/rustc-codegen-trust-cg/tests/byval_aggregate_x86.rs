// Integration test: BY-VALUE AGGREGATES across the ABI — structs / tuples /
// fixed arrays / multi-variant enums / Option passed, returned, stored, matched,
// and matched THROUGH A REFERENCE — compiled for x86_64 via the
// rustc_codegen_trust_cg bridge, COMPILED, LINKED, and RUN, with the exit code
// checked against the default LLVM backend (the SysV AMD64 ABI ground truth).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Every case is a FULL-PROGRAM differential: the same source is compiled by BOTH
// the trust-cg bridge AND the stock LLVM backend, both binaries are run, and the
// trust-cg exit code MUST equal the LLVM exit code. A wrong field offset or ABI
// register class (the danger of by-value aggregates) shows up as a mismatch.
//
// Shapes covered (the increment's validation gate):
//   * a 2-field `{ i64, i64 }` struct returned by value and both fields used;
//   * a struct passed by value into a fn and its fields read;
//   * a <=16-byte struct returned and round-tripped through a second fn;
//   * a >16-byte struct (5x i64) returned via sret and summed;
//   * a tuple `(i64, i32)` returned and consumed;
//   * a fixed array `[u8; 24]` returned from a fn and indexed (the
//     `Elf64Sym::encode` shape — see `elf64_sym_encode_proof_point`);
//   * a 3-variant enum returned by value and matched;
//   * `match &enum` over a >=6-variant enum returning a different value per
//     variant (the derived-PartialEq / hand-written `match &enum` path);
//   * an `Option<i64>` produced by value and matched.

use std::ffi::OsString;
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

fn dylib_name() -> String {
    format!(
        "{}rustc_codegen_trust_cg{}",
        std::env::consts::DLL_PREFIX,
        std::env::consts::DLL_SUFFIX
    )
}

fn ensure_dylib_built() -> PathBuf {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let target_dir = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| crate_dir.join("target"));
    let name = dylib_name();
    let candidates = [
        target_dir.join("release").join(&name),
        target_dir.join("debug").join(&name),
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
    assert!(status.success(), "cargo build failed; cannot run byval-aggregate test");
    let built = target_dir.join("release").join(&name);
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
    let dir = std::env::temp_dir().join(format!("rcl2_byval_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> OsString {
    let mut s = OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src` with the given backend (`None` = stock LLVM, `Some(dylib)` =
/// trust-cg) at `-Copt-level=0`. Returns `(compiled_ok, stderr)`.
fn compile(dylib: Option<&Path>, dir: &Path, src: &Path, out: &Path) -> (bool, String) {
    compile_at(dylib, dir, src, out, 0)
}

/// As `compile`, but at the requested `-Copt-level` (`0` or `3`). The const-folded
/// constant-aggregate shapes (a ctor body collapsing to `_0 = const Aggregate` /
/// a const struct argument) only appear at `-Copt-level=3`, so the differential
/// MUST cover both to lock in the eightbyte-packing AND const-aggregate fixes.
fn compile_at(
    dylib: Option<&Path>,
    dir: &Path,
    src: &Path,
    out: &Path,
    opt_level: u8,
) -> (bool, String) {
    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"]);
    if let Some(dylib) = dylib {
        cmd.arg(backend_arg(dylib));
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort"])
        .arg(format!("-Copt-level={opt_level}"))
        .arg("-o")
        .arg(out)
        .arg(src)
        .current_dir(dir);
    let output = cmd.output().expect("spawn rustc");
    (
        output.status.success(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

/// The core differential: compile `src` with BOTH backends, run both binaries,
/// and assert the trust-cg exit code equals the LLVM exit code.
fn assert_byval_matches_llvm(stem: &str, src_text: &str) {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir(stem);
    let src = dir.join("prog.rs");
    std::fs::write(&src, src_text).expect("write source");

    // LLVM ground truth.
    let llvm_bin = dir.join("llvm_out");
    let (llvm_ok, llvm_err) = compile(None, &dir, &src, &llvm_bin);
    assert!(llvm_ok, "[{stem}] LLVM backend failed to compile. stderr: <<<{llvm_err}>>>");
    let llvm_run = Command::new(&llvm_bin).output().expect("run llvm binary");
    let llvm_exit = llvm_run.status.code();

    // trust-cg.
    let tcg_bin = dir.join("tcg_out");
    let (tcg_ok, tcg_err) = compile(Some(&dylib), &dir, &src, &tcg_bin);
    assert!(
        tcg_ok,
        "[{stem}] trust-cg bridge failed to compile a by-value aggregate program. \
         stderr: <<<{tcg_err}>>>"
    );
    assert!(
        !tcg_err.contains("failing closed"),
        "[{stem}] trust-cg unexpectedly failed closed. stderr: <<<{tcg_err}>>>"
    );
    let tcg_run = Command::new(&tcg_bin).output().expect("run trust-cg binary");
    let tcg_exit = tcg_run.status.code();

    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(
        tcg_exit, llvm_exit,
        "[{stem}] trust-cg exit {tcg_exit:?} != LLVM exit {llvm_exit:?} (by-value aggregate miscompile)"
    );
}

/// The differential at a SPECIFIC `-Copt-level`: compile `src` with BOTH backends
/// at `opt_level`, run both, and assert the exit codes match. The bridge must NOT
/// fail closed (these are shapes it MUST support) and must produce a binary.
fn assert_byval_matches_llvm_at(stem: &str, src_text: &str, opt_level: u8) {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir(&format!("{stem}_o{opt_level}"));
    let src = dir.join("prog.rs");
    std::fs::write(&src, src_text).expect("write source");

    let llvm_bin = dir.join("llvm_out");
    let (llvm_ok, llvm_err) = compile_at(None, &dir, &src, &llvm_bin, opt_level);
    assert!(
        llvm_ok,
        "[{stem} O{opt_level}] LLVM backend failed to compile. stderr: <<<{llvm_err}>>>"
    );
    let llvm_exit = Command::new(&llvm_bin)
        .output()
        .expect("run llvm binary")
        .status
        .code();

    let tcg_bin = dir.join("tcg_out");
    let (tcg_ok, tcg_err) = compile_at(Some(&dylib), &dir, &src, &tcg_bin, opt_level);
    assert!(
        tcg_ok,
        "[{stem} O{opt_level}] trust-cg bridge failed to compile (a by-value aggregate \
         shape it must support). stderr: <<<{tcg_err}>>>"
    );
    assert!(
        !tcg_err.contains("failing closed"),
        "[{stem} O{opt_level}] trust-cg unexpectedly failed closed. stderr: <<<{tcg_err}>>>"
    );
    // The defect-5 silent-skip-as-unreachable bug produced a SILENTLY UNLINKABLE
    // binary: a reachable local ctor was dropped, so the link failed with an
    // undefined symbol. That manifests as `tcg_ok == false` above (caught), and the
    // exit-code comparison below catches any residual wrong value. (Upstream libcore
    // iterator glue that the bridge's `for`-loop interception genuinely replaces is
    // still soundly skipped — the program links and runs correctly — so we do NOT
    // forbid the skip message itself, only an unlinkable / mismatching result.)
    let tcg_exit = Command::new(&tcg_bin)
        .output()
        .expect("run trust-cg binary")
        .status
        .code();

    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(
        tcg_exit, llvm_exit,
        "[{stem} O{opt_level}] trust-cg exit {tcg_exit:?} != LLVM exit {llvm_exit:?} \
         (by-value aggregate miscompile)"
    );
}

/// Lock a shape in at BOTH `-Copt-level=0` and `-Copt-level=3`: the eightbyte
/// mispack / dropped-field / enum-by-value / const-aggregate defects manifested at
/// one or both opt levels, so both must match LLVM forever.
fn assert_byval_matches_llvm_both_opts(stem: &str, src_text: &str) {
    assert_byval_matches_llvm_at(stem, src_text, 0);
    assert_byval_matches_llvm_at(stem, src_text, 3);
}

// ───────────────────────────────────────────────────────────────────────────
// REGRESSION LOCK-INS for the 5 differential-fuzzer-found defect classes.
// Each was either a SILENT WRONG VALUE or a SILENTLY-UNLINKABLE binary before the
// eightbyte-packing / const-aggregate / fail-closed fixes; each is now pinned at
// BOTH opt levels so it can never silently regress.
// ───────────────────────────────────────────────────────────────────────────

/// DEFECT 1 — SUB-EIGHTBYTE MIS-PACK. A struct whose first eightbyte is a COMPOSITE
/// of several sub-8-byte fields (`Mix{i32,i16,i8,u8,i64}`, which rustc REORDERS to
/// `e@0, a@8`) passed BY VALUE. The callee read `m.a` from the WRONG eightbyte
/// (it got field `e`'s bytes) because the scalarized caller built the struct in
/// DECLARATION order while the callee read it in Rust LAYOUT order. Now the source
/// is memory-backed in layout order on both sides.
#[test]
fn mixed_width_struct_arg_eightbyte_packing() {
    assert_byval_matches_llvm_both_opts(
        "mixed_width_struct_arg",
        "struct Mix { a: i32, b: i16, c: i8, d: u8, e: i64 }\n\
         #[inline(never)]\n\
         fn get(m: Mix) -> i64 { m.a as i64 }\n\
         #[inline(never)]\n\
         fn fold(m: Mix) -> i64 {\n\
         \x20   (m.a as i64) + (m.b as i64) + (m.c as i64) + (m.d as i64) + m.e\n\
         }\n\
         fn main() {\n\
         \x20   let m = Mix { a: 0x0A0B_0C0D, b: 0x1E1F, c: 0x2A, d: 0xBC,\n\
         \x20                 e: 0x3344_5566_7788_99AAu64 as i64 };\n\
         \x20   let m2 = Mix { a: 0x0A0B_0C0D, b: 0x1E1F, c: 0x2A, d: 0xBC,\n\
         \x20                  e: 0x3344_5566_7788_99AAu64 as i64 };\n\
         \x20   std::process::exit((((get(m)) ^ (fold(m2))) & 0xff) as i32);\n\
         }\n",
    );
}

/// DEFECT 1 (variant) — a COMPOSITE first eightbyte assembled from two `i32`
/// fields plus a trailing `i64` (`S{i32,i32,i64}`), passed by value. Not specific
/// to mixed widths: ANY first eightbyte built from >1 field triggered the swap.
#[test]
fn composite_first_eightbyte_struct_arg() {
    assert_byval_matches_llvm_both_opts(
        "composite_first_eightbyte",
        "struct S { a: i32, b: i32, e: i64 }\n\
         #[inline(never)]\n\
         fn get(s: S) -> i64 { (s.a as i64) + (s.b as i64) + s.e }\n\
         fn main() {\n\
         \x20   let s = S { a: 0x1112_1314, b: 0x2122_2324, e: 0x3132_3334_3536_3738 };\n\
         \x20   std::process::exit((get(s) & 0xff) as i32);\n\
         }\n",
    );
}

/// DEFECT 1 (multi-arg) — a two-eightbyte struct at a LATER argument position
/// (4th), after register-consuming scalars, with mixed-width fields. The whole
/// struct was mis-read.
#[test]
fn mixed_struct_at_fourth_arg_position() {
    assert_byval_matches_llvm_both_opts(
        "mixed_struct_fourth_arg",
        "struct Mixed { x: u8, y: i32, z: i64, w: u16 }\n\
         #[inline(never)]\n\
         fn f(s0: i64, s1: i64, s2: i64, m: Mixed, s3: i64) -> i64 {\n\
         \x20   (m.x as i64) + (m.y as i64) + m.z + (m.w as i64) + s0 + s1 + s2 + s3\n\
         }\n\
         fn main() {\n\
         \x20   let m = Mixed { x: 0xAB, y: -123_456_789, z: 0x7766_5544_3322_1100u64 as i64,\n\
         \x20                   w: 0xBEEF };\n\
         \x20   std::process::exit((f(1, 2, 3, m, 4) & 0xff) as i32);\n\
         }\n",
    );
}

/// DEFECT 2 — >16-BYTE MEMORY-CLASS by-value arg with MIXED-WIDTH fields
/// (`Packed{u32,u64,u16}`, 24 bytes). The callee previously saw the entire
/// incoming struct as ZERO (fields dropped) because the scalarized caller and the
/// memory-class callee disagreed on the byte layout. Now both use the layout-order
/// slot.
#[test]
fn over_16_byte_memory_class_struct_arg() {
    assert_byval_matches_llvm_both_opts(
        "over16_memory_struct_arg",
        "struct Packed { head: u32, mid: u64, tail: u16 }\n\
         #[inline(never)]\n\
         fn run(p: Packed) -> Packed {\n\
         \x20   Packed { head: p.head + 1, mid: p.mid + 2, tail: p.tail + 3 }\n\
         }\n\
         fn main() {\n\
         \x20   let p = Packed { head: 0xDEAD_BEEF, mid: 0xFEDC_BA98_7654_3210, tail: 0xABCD };\n\
         \x20   let o = run(p);\n\
         \x20   let e = ((o.head as u64) ^ o.mid ^ (o.tail as u64)) & 0xff;\n\
         \x20   std::process::exit(e as i32);\n\
         }\n",
    );
}

/// DEFECT 3 — a 3-variant enum with MIXED-WIDTH payloads produced BY VALUE and
/// matched (driven by a runtime loop). Was a SILENT WRONG VALUE.
#[test]
fn enum_by_value_produced_and_matched() {
    assert_byval_matches_llvm_both_opts(
        "enum_by_value_matched",
        "enum E { A(i64, i32), B(i8, i64), C(u16, u32, i64) }\n\
         #[inline(never)]\n\
         fn make(sel: u8) -> E {\n\
         \x20   match sel { 0 => E::A(1000, 7), 1 => E::B(3, 5000), _ => E::C(11, 22, 33) }\n\
         }\n\
         #[inline(never)]\n\
         fn score(e: E) -> i64 {\n\
         \x20   match e {\n\
         \x20       E::A(x, y) => x + (y as i64),\n\
         \x20       E::B(a, b) => (a as i64) + b,\n\
         \x20       E::C(p, q, r) => (p as i64) + (q as i64) + r,\n\
         \x20   }\n\
         }\n\
         fn main() {\n\
         \x20   let mut acc: i64 = 0;\n\
         \x20   for s in 0u8..3 { acc += score(make(s)); }\n\
         \x20   std::process::exit((acc & 0xff) as i32);\n\
         }\n",
    );
}

/// DEFECT 3 (Option/Result) — `Option<i64>` / `Option<bool>` / `Result<i64,i32>`
/// produced and matched via `#[inline(never)]` helpers. At O3 the helpers were
/// silently skipped (link error); now they lower (const-aggregate materialization).
#[test]
fn option_result_by_value_helpers() {
    assert_byval_matches_llvm_both_opts(
        "option_result_helpers",
        "#[inline(never)] fn mk_opt_i64(b: bool) -> Option<i64> { if b { Some(42) } else { None } }\n\
         #[inline(never)] fn mk_opt_bool(b: bool) -> Option<bool> { if b { Some(true) } else { None } }\n\
         #[inline(never)] fn mk_res(b: bool) -> Result<i64, i32> { if b { Ok(64) } else { Err(7) } }\n\
         fn main() {\n\
         \x20   let mut acc: i64 = 0;\n\
         \x20   acc += match mk_opt_i64(true) { Some(x) => x, None => 0 };\n\
         \x20   acc += match mk_opt_bool(true) { Some(true) => 0, Some(false) => 1, None => 2 };\n\
         \x20   acc += match mk_res(true) { Ok(x) => x, Err(e) => e as i64 };\n\
         \x20   std::process::exit((acc & 0xff) as i32);\n\
         }\n",
    );
}

/// DEFECT 4 — `match &enum` (13 variants) whose arms feed a BY-VALUE struct, the
/// struct then consumed by a second by-value fn. Was wrong at both opt levels.
#[test]
fn match_ref_enum_feeding_by_value_struct() {
    assert_byval_matches_llvm_both_opts(
        "match_ref_enum_byval_struct",
        "enum K { V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12 }\n\
         struct Two { a: i64, b: i64 }\n\
         #[inline(never)]\n\
         fn classify(k: &K) -> Two {\n\
         \x20   match k {\n\
         \x20       K::V0 => Two { a: 1, b: 2 }, K::V1 => Two { a: 3, b: 4 },\n\
         \x20       K::V2 => Two { a: 5, b: 6 }, K::V3 => Two { a: 7, b: 8 },\n\
         \x20       K::V4 => Two { a: 9, b: 10 }, K::V5 => Two { a: 11, b: 12 },\n\
         \x20       K::V6 => Two { a: 13, b: 14 }, K::V7 => Two { a: 15, b: 16 },\n\
         \x20       K::V8 => Two { a: 17, b: 18 }, K::V9 => Two { a: 19, b: 20 },\n\
         \x20       K::V10 => Two { a: 21, b: 22 }, K::V11 => Two { a: 23, b: 24 },\n\
         \x20       K::V12 => Two { a: 25, b: 26 },\n\
         \x20   }\n\
         }\n\
         #[inline(never)]\n\
         fn add2(t: Two) -> i64 { t.a + t.b }\n\
         #[inline(never)]\n\
         fn run(sel: u8) -> i64 {\n\
         \x20   let k = match sel { 0 => K::V0, 3 => K::V3, 7 => K::V7, 12 => K::V12, _ => K::V5 };\n\
         \x20   add2(classify(&k))\n\
         }\n\
         fn main() {\n\
         \x20   let mut acc: i64 = 0;\n\
         \x20   let mut s: u8 = 0;\n\
         \x20   while s < 13 { acc += run(s); s += 1; }\n\
         \x20   std::process::exit((acc & 0xff) as i32);\n\
         }\n",
    );
}

/// DEFECT 5 — a CONSTANT-AGGREGATE return. At `-Copt-level=3` the ctor body folds
/// to `_0 = const Pair{a,b}`; the bridge previously could not lower it, then
/// SILENTLY SKIPPED the (live, `#[inline(never)]`) ctor as 'unreachable', producing
/// an UNLINKABLE binary. Now the constant is materialized into the return slot.
/// Tested at both opt levels (the fold only happens at O3).
#[test]
fn constant_aggregate_return_at_o3() {
    assert_byval_matches_llvm_both_opts(
        "const_aggregate_return",
        "struct Pair { a: i64, b: i64 }\n\
         #[inline(never)]\n\
         fn mk() -> Pair { Pair { a: 100, b: 37 } }\n\
         fn main() {\n\
         \x20   let p = mk();\n\
         \x20   std::process::exit(((p.a + p.b) & 0xff) as i32);\n\
         }\n",
    );
}

/// DEFECT 5 (Option/Result const ctors) — `Option<i64>` / `Result<i64,i32>` built
/// from CONSTANTS via `#[inline(never)]` ctors. The const-folded by-value return
/// must materialize the constant rather than silently skip the ctor.
#[test]
fn constant_option_result_ctors_at_o3() {
    assert_byval_matches_llvm_both_opts(
        "const_option_result_ctors",
        "#[inline(never)] fn opt() -> Option<i64> { Some(99) }\n\
         #[inline(never)] fn res() -> Result<i64, i32> { Ok(28) }\n\
         fn main() {\n\
         \x20   let a = match opt() { Some(x) => x, None => 0 };\n\
         \x20   let b = match res() { Ok(x) => x, Err(e) => e as i64 };\n\
         \x20   std::process::exit(((a + b) & 0xff) as i32);\n\
         }\n",
    );
}

/// A 2-field `{ i64, i64 }` struct returned BY VALUE (in RAX:RDX) and both fields
/// used by the caller.
#[test]
fn two_field_i64_struct_returned_by_value() {
    assert_byval_matches_llvm(
        "two_field_struct",
        "struct Pair { a: i64, b: i64 }\n\
         #[inline(never)]\n\
         fn mk(x: i64, y: i64) -> Pair { Pair { a: x, b: y } }\n\
         fn main() {\n\
         \x20   let p = mk(7, 13);\n\
         \x20   std::process::exit((p.a + p.b) as i32);\n\
         }\n",
    );
}

/// A struct passed BY VALUE into a fn whose body reads its fields.
#[test]
fn struct_passed_by_value_fields_read() {
    assert_byval_matches_llvm(
        "pass_struct",
        "struct Pair { a: i64, b: i64 }\n\
         #[inline(never)]\n\
         fn sum(p: Pair) -> i64 { p.a + p.b }\n\
         fn main() {\n\
         \x20   let p = Pair { a: 9, b: 11 };\n\
         \x20   std::process::exit(sum(p) as i32);\n\
         }\n",
    );
}

/// A <=16-byte struct returned and ROUND-TRIPPED (mk -> consume), so the
/// aggregate crosses two by-value boundaries.
#[test]
fn small_struct_round_tripped_by_value() {
    assert_byval_matches_llvm(
        "round_trip_struct",
        "struct P { a: i64, b: i64 }\n\
         #[inline(never)]\n\
         fn mk(x: i64) -> P { P { a: x, b: x + 1 } }\n\
         #[inline(never)]\n\
         fn consume(p: P) -> i64 { p.a * 10 + p.b }\n\
         fn main() {\n\
         \x20   let p = mk(4);\n\
         \x20   std::process::exit(consume(p) as i32);\n\
         }\n",
    );
}

/// A >16-byte struct (5x i64 = 40 bytes) returned via the SysV `sret` hidden
/// pointer and summed.
#[test]
fn large_struct_returned_via_sret() {
    assert_byval_matches_llvm(
        "sret_struct",
        "struct Big { a: i64, b: i64, c: i64, d: i64, e: i64 }\n\
         #[inline(never)]\n\
         fn mk() -> Big { Big { a: 1, b: 2, c: 3, d: 4, e: 5 } }\n\
         fn main() {\n\
         \x20   let b = mk();\n\
         \x20   std::process::exit((b.a + b.b + b.c + b.d + b.e) as i32);\n\
         }\n",
    );
}

/// A tuple `(i64, i32)` returned by value (16 bytes, RAX:RDX) and consumed.
#[test]
fn tuple_returned_and_consumed_by_value() {
    assert_byval_matches_llvm(
        "tuple",
        "#[inline(never)]\n\
         fn mk() -> (i64, i32) { (40, 2) }\n\
         fn main() {\n\
         \x20   let (a, b) = mk();\n\
         \x20   std::process::exit((a as i32) + b);\n\
         }\n",
    );
}

/// A fixed array `[u8; 24]` returned from a fn (via sret, 24 bytes) and indexed.
#[test]
fn fixed_array_u8_24_returned_and_indexed() {
    assert_byval_matches_llvm(
        "array24",
        "#[inline(never)]\n\
         fn mk() -> [u8; 24] {\n\
         \x20   let mut a = [0u8; 24];\n\
         \x20   let mut i = 0;\n\
         \x20   while i < 24 { a[i] = (i as u8) + 1; i += 1; }\n\
         \x20   a\n\
         }\n\
         fn main() {\n\
         \x20   let a = mk();\n\
         \x20   std::process::exit((a[0] as i32) + (a[23] as i32));\n\
         }\n",
    );
}

/// A 3-variant enum returned by value and matched (a Direct-tagged enum crossing
/// the by-value boundary).
#[test]
fn three_variant_enum_returned_by_value_and_matched() {
    assert_byval_matches_llvm(
        "enum3",
        "enum E { A, B(i64), C(i64, i64) }\n\
         #[inline(never)]\n\
         fn mk(n: i64) -> E { if n == 0 { E::A } else if n == 1 { E::B(10) } else { E::C(3, 4) } }\n\
         fn main() {\n\
         \x20   let e = mk(2);\n\
         \x20   let r = match e { E::A => 1, E::B(x) => x, E::C(a, b) => a + b };\n\
         \x20   std::process::exit(r as i32);\n\
         }\n",
    );
}

/// `match &enum` over a 6-variant enum returning a different value per variant.
/// This is the discriminant-through-reference path (also derived `PartialEq` /
/// `Hash`): the bridge reads the tag at the enum's byte offset THROUGH the `&E`.
#[test]
fn match_ref_enum_six_variants_returns_per_variant() {
    assert_byval_matches_llvm(
        "ref_enum6",
        "enum E { A, B, C, D, F, G }\n\
         #[inline(never)]\n\
         fn val(e: &E) -> i64 {\n\
         \x20   match e { E::A => 1, E::B => 2, E::C => 3, E::D => 4, E::F => 5, E::G => 6 }\n\
         }\n\
         fn main() {\n\
         \x20   let e = E::F;\n\
         \x20   std::process::exit(val(&e) as i32);\n\
         }\n",
    );
}

/// `match &enum` BINDING A PAYLOAD through the reference: `&((*e) as Variant).0`
/// is the payload field's byte address; `*x` loads it. Exercises the
/// payload-through-reference path on top of the discriminant readback.
#[test]
fn match_ref_enum_payload_read_through_reference() {
    assert_byval_matches_llvm(
        "ref_enum_payload",
        "enum E { A(i64), B(i64, i64), C }\n\
         #[inline(never)]\n\
         fn val(e: &E) -> i64 {\n\
         \x20   match e { E::A(x) => *x, E::B(a, b) => *a + *b, E::C => 99 }\n\
         }\n\
         fn main() {\n\
         \x20   let e = E::B(3, 4);\n\
         \x20   std::process::exit(val(&e) as i32);\n\
         }\n",
    );
}

/// An `Option<i64>` produced BY VALUE (a niche-encoded enum crossing the boundary)
/// and matched.
#[test]
fn option_i64_produced_by_value_and_matched() {
    assert_byval_matches_llvm(
        "option",
        "#[inline(never)]\n\
         fn mk(n: i64) -> Option<i64> { if n > 0 { Some(n * 2) } else { None } }\n\
         fn main() {\n\
         \x20   let o = mk(21);\n\
         \x20   let r = match o { Some(x) => x, None => 0 };\n\
         \x20   std::process::exit(r as i32);\n\
         }\n",
    );
}

/// A `&mut enum` WRITE-BACK through the reference: `*value = Choice::Left(3)`
/// stores the whole multi-variant enum through `&mut`, observed by a subsequent
/// read. (The case `unsupported_program.rs` previously pinned as fail-closed; it
/// is now sound, so it is exercised as a positive differential here.)
#[test]
fn write_multi_variant_enum_through_mut_reference() {
    assert_byval_matches_llvm(
        "write_enum",
        "pub enum Choice { Left(u64), Right(u64) }\n\
         #[inline(never)]\n\
         pub fn write_choice(value: &mut Choice, flag: bool) {\n\
         \x20   if flag { *value = Choice::Left(3); } else { *value = Choice::Right(5); }\n\
         }\n\
         #[inline(never)]\n\
         fn read(c: &Choice) -> u64 {\n\
         \x20   match c { Choice::Left(x) => 100 + *x, Choice::Right(y) => 200 + *y }\n\
         }\n\
         fn main() {\n\
         \x20   let mut c = Choice::Left(0);\n\
         \x20   write_choice(&mut c, false);\n\
         \x20   let a = read(&c);\n\
         \x20   write_choice(&mut c, true);\n\
         \x20   let b = read(&c);\n\
         \x20   std::process::exit(((a + b) & 0xff) as i32);\n\
         }\n",
    );
}

/// PROOF POINT: a standalone equivalent of the REAL `trust_cg_codegen::elf::
/// Elf64Sym::encode` — a struct-of-fields whose `encode(&self) -> [u8; 24]`
/// builds a 24-byte little-endian symbol entry by writing each field at its byte
/// offset, then RETURNS the fixed array BY VALUE. The caller indexes the returned
/// array. This combines struct-field reads + a `[u8; 24]` by-value return (the
/// universal aggregate wall) and must match LLVM byte-for-byte.
///
/// The real `Elf64Sym::encode` uses `u64::to_le_bytes` + `slice::copy_from_slice`.
/// `to_le_bytes` lowers to a SMALL (2/4/8-byte) sub-array returned by value, which
/// the backend's SysV aggregate-result classifier does not yet place (it fails
/// closed on a `Struct([I8, I8])` 2-byte result) — that small-aggregate-return
/// case is DEFERRED to a later increment. The semantically-identical byte-packing
/// here uses explicit `>> / as u8` shifts, exercising the load-bearing shape:
/// struct fields written into a stack `[u8; 24]` that is returned by value.
#[test]
fn elf64_sym_encode_proof_point() {
    assert_byval_matches_llvm(
        "elf64sym_encode",
        "// Standalone mirror of trust_cg_codegen::elf::Elf64Sym::encode (shift form).\n\
         struct Elf64Sym {\n\
         \x20   st_name: u32,\n\
         \x20   st_info: u8,\n\
         \x20   st_other: u8,\n\
         \x20   st_shndx: u16,\n\
         \x20   st_value: u64,\n\
         \x20   st_size: u64,\n\
         }\n\
         impl Elf64Sym {\n\
         \x20   #[inline(never)]\n\
         \x20   fn encode(&self) -> [u8; 24] {\n\
         \x20       let mut buf = [0u8; 24];\n\
         \x20       buf[0] = self.st_name as u8;\n\
         \x20       buf[1] = (self.st_name >> 8) as u8;\n\
         \x20       buf[2] = (self.st_name >> 16) as u8;\n\
         \x20       buf[3] = (self.st_name >> 24) as u8;\n\
         \x20       buf[4] = self.st_info;\n\
         \x20       buf[5] = self.st_other;\n\
         \x20       buf[6] = self.st_shndx as u8;\n\
         \x20       buf[7] = (self.st_shndx >> 8) as u8;\n\
         \x20       let mut i = 0;\n\
         \x20       while i < 8 { buf[8 + i] = (self.st_value >> (i * 8)) as u8; i += 1; }\n\
         \x20       let mut j = 0;\n\
         \x20       while j < 8 { buf[16 + j] = (self.st_size >> (j * 8)) as u8; j += 1; }\n\
         \x20       buf\n\
         \x20   }\n\
         }\n\
         fn main() {\n\
         \x20   let sym = Elf64Sym {\n\
         \x20       st_name: 0x04030201,\n\
         \x20       st_info: 0x12,\n\
         \x20       st_other: 0x03,\n\
         \x20       st_shndx: 0x0102,\n\
         \x20       st_value: 0x1122334455667788,\n\
         \x20       st_size: 24,\n\
         \x20   };\n\
         \x20   let bytes = sym.encode();\n\
         \x20   // Sum a few representative bytes across the struct fields.\n\
         \x20   let r = (bytes[0] as i32) + (bytes[4] as i32) + (bytes[6] as i32)\n\
         \x20         + (bytes[15] as i32) + (bytes[16] as i32);\n\
         \x20   std::process::exit(r);\n\
         }\n",
    );
}

// ───────────────────────────────────────────────────────────────────────────
// FLOAT / MIXED-CLASS by-value TUPLE returns (the `scalar_byval_tuple_eligible`
// increment). A bare TUPLE with a FLOAT leaf — `(f64, f64)`, `(i32, f64)`,
// `(f64, i32)`, a 3-tuple, a >16-byte all-float tuple — previously FAILED CLOSED
// at O0 (and O3) with `Ty::(f64, f64)` MIR-unsupported, while the IDENTICAL named
// struct (`struct { f64, f64 }`) already memory-backed and returned correctly.
// These tuples now ride the SAME verified SysV register-pair (eightbyte INTEGER
// -> RAX:RDX / SSE -> XMM0:XMM1) / sret machinery. A wrong eightbyte CLASS or a
// wrong field byte-offset would surface here as an exit-code mismatch, so these
// pin the float/mixed-class tuple-return ABI at BOTH opt levels forever.
// ───────────────────────────────────────────────────────────────────────────

/// `(f64, f64)` returned by value — both eightbytes SSE class (XMM0:XMM1).
#[test]
fn float_tuple_f64_f64_returned_by_value() {
    assert_byval_matches_llvm_both_opts(
        "ret_tuple_f64f64",
        "#[inline(never)] fn bb<T>(x: T) -> T { std::hint::black_box(x) }\n\
         #[inline(never)] fn mk(x: f64) -> (f64, f64) { (x, x * 2.0) }\n\
         fn main() {\n\
         \x20   let (a, b) = mk(bb(3.0));\n\
         \x20   std::process::exit(((a + b) as i32) & 0x7f);\n\
         }\n",
    );
}

/// `(i32, f64)` returned by value — MIXED class: eightbyte 0 INTEGER (RAX), eightbyte
/// 1 SSE (XMM0). The dangerous register-class case, now exercised end to end.
#[test]
fn mixed_tuple_i32_f64_returned_by_value() {
    assert_byval_matches_llvm_both_opts(
        "ret_tuple_i32f64",
        "#[inline(never)] fn bb<T>(x: T) -> T { std::hint::black_box(x) }\n\
         #[inline(never)] fn mk(x: i32) -> (i32, f64) { (x, (x as f64) * 2.0) }\n\
         fn main() {\n\
         \x20   let (a, b) = mk(bb(10i32));\n\
         \x20   std::process::exit(((a as f64 + b) as i32) & 0x7f);\n\
         }\n",
    );
}

/// `(f64, i32)` returned by value — MIXED class with the SSE eightbyte FIRST
/// (XMM0:RAX): the field reorder + class ordering are independent risks.
#[test]
fn mixed_tuple_f64_i32_returned_by_value() {
    assert_byval_matches_llvm_both_opts(
        "ret_tuple_f64i32",
        "#[inline(never)] fn bb<T>(x: T) -> T { std::hint::black_box(x) }\n\
         #[inline(never)] fn mk(x: i32) -> (f64, i32) { ((x as f64) * 2.0, x) }\n\
         fn main() {\n\
         \x20   let (a, b) = mk(bb(10i32));\n\
         \x20   std::process::exit(((a + b as f64) as i32) & 0x7f);\n\
         }\n",
    );
}

/// A >16-byte all-float tuple `(f64, f64, f64, f64)` (32 bytes) returned via the
/// sret hidden-pointer MEMORY class.
#[test]
fn large_float_tuple_returned_via_sret() {
    assert_byval_matches_llvm_both_opts(
        "ret_tuple_4f64",
        "#[inline(never)] fn bb<T>(x: T) -> T { std::hint::black_box(x) }\n\
         #[inline(never)] fn mk(x: f64) -> (f64, f64, f64, f64) { (x, x * 2.0, x * 3.0, x * 4.0) }\n\
         fn main() {\n\
         \x20   let (a, b, c, d) = mk(bb(2.0));\n\
         \x20   std::process::exit(((a + b + c + d) as i32) & 0x7f);\n\
         }\n",
    );
}

/// A by-value `(f64, f64)` TUPLE PARAMETER (the arg leg of the same predicate) and a
/// return round-trip through a second fn — both directions of the boundary.
#[test]
fn float_tuple_param_and_return_round_trip() {
    assert_byval_matches_llvm_both_opts(
        "rt_tuple_f64f64",
        "#[inline(never)] fn bb<T>(x: T) -> T { std::hint::black_box(x) }\n\
         #[inline(never)] fn mk(x: f64) -> (f64, f64) { (x, x * 2.0) }\n\
         #[inline(never)] fn cons(t: (f64, f64)) -> f64 { t.0 * 10.0 + t.1 }\n\
         fn main() {\n\
         \x20   let t = mk(bb(3.0));\n\
         \x20   std::process::exit((cons(t) as i32) & 0x7f);\n\
         }\n",
    );
}
