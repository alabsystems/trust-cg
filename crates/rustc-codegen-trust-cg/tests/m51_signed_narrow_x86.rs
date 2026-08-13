// Differential regression test for MISCOMPILE #51 (m51): signed-narrow i8/i16
// arithmetic shift right (SAR) and signed division/remainder whose operand came
// from a width-narrowing cast.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ROOT CAUSE. Sub-32-bit integers live in 32-bit GPRs, and the x86-64
// instructions that implement their signed operations — `SAR r32`, `CDQ`/`IDIV
// r32` — execute at the full 32-bit register width. A width-narrowing cast
// (`-100i32 as i8`) lowers via `select_trunc`, which ZERO-extends the low byte
// into the carrier (`MOVZX`). For an UNSIGNED consumer that is correct, but a
// SIGNED consumer then sees a non-negative 32-bit value: `SAR` shifts in zeros
// (a logical shift) and `IDIV` divides a wrong positive dividend/divisor. The
// fix (in `trust-cg-lower/src/x86_64_isel.rs`) sign-extends (`MOVSX`) the narrow
// operand at the use site of a signed SAR / IDIV so the operation observes the
// true sign at bit 31. The companion change (in `trust-cg-lower/src/adapter.rs`)
// accepts a shift whose count operand is a different integer width than the
// shifted value (`i8 >> 1` carries an I32 count literal), which the ISel already
// handles by taking the count from CL.
//
// The differential oracle is the SAME program compiled by rustc's default LLVM
// backend. Each case is compiled twice — once with `-Zcodegen-backend=<trust-cg
// dylib>` and once without — linked the same way, run, and the process exit
// codes are required to be EQUAL (and equal to the documented expected value).
// `core::hint::black_box` defeats const-folding so the narrowing cast and the
// signed op are materialized as real runtime instructions at every -Copt-level.
//
// The crate is `#![no_std] #![no_main]` exposing `#[no_mangle] pub extern "C" fn
// main() -> i32`, so the bridge compiles `main` directly and we avoid the std
// `std::rt::lang_start` entry path. Abort stubs are supplied for any referenced
// `panic_const_*` symbols (the overflow / div-by-zero checks never fire at the
// chosen inputs), so the LLVM object links standalone exactly like the trust-cg
// object (which drops those unreachable checks).

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
    assert!(status.success(), "cargo build failed; cannot run m51 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m51_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Write a C file with `abort()` stubs for every undefined `panic*` symbol the
/// object references, so the object links standalone (these checks never fire at
/// the chosen inputs). Returns the path to the generated stub file.
fn write_panic_stubs(dir: &Path, obj: &Path) -> PathBuf {
    let nm = Command::new("nm").arg("-u").arg(obj).output().expect("nm");
    let mut stubs = String::from("#include <stdlib.h>\n");
    for line in String::from_utf8_lossy(&nm.stdout).lines() {
        let sym = line.trim().trim_start_matches('U').trim();
        if sym.contains("panic") {
            let c = sym.strip_prefix('_').unwrap_or(sym);
            stubs.push_str(&format!(
                "void {c}(void) __asm__(\"{sym}\"); void {c}(void){{ abort(); }}\n"
            ));
        }
    }
    let stubs_path = dir.join("stubs.c");
    std::fs::write(&stubs_path, stubs).expect("write stubs");
    stubs_path
}

/// Compile `src` (with the given backend), link with abort stubs, run, and
/// return the process exit code. When `dylib` is `Some`, the trust-cg codegen
/// backend is used; when `None`, rustc's default LLVM backend is used (the
/// differential oracle). All emitted `.o` codegen units are linked together (a
/// `black_box` call may live in its own CGU object).
fn compile_link_run(stem: &str, src: &str, opt: &str, dylib: Option<&Path>) -> i32 {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .arg("--crate-type")
        .arg("bin");
    if let Some(dylib) = dylib {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(&backend_arg);
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort", "-Coverflow-checks=off"])
        .arg(format!("-Copt-level={opt}"))
        .arg("--emit=obj")
        // `--out-dir` (not `-o`) so EVERY codegen unit object is written with a
        // `.o` extension under both backends: rustc's LLVM backend emits a single
        // `prog.o`, while the trust-cg backend emits one `prog.<cgu>.rcgu.o` per
        // CGU (a `black_box` call lives in its own CGU). A bare `-o <name>` would
        // instead produce an extension-less file for the single-CGU LLVM build.
        .arg("--out-dir")
        .arg(&dir)
        .arg(&src_path);
    let output = cmd.output().expect("failed to spawn rustc via rustup");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "{stem} (opt={opt}, backend={}): failed to compile. stderr: <<<{stderr}>>>",
        if dylib.is_some() { "trust-cg" } else { "llvm" }
    );

    // Collect every emitted object codegen unit (the bridge / rustc name them
    // after the CGU, and a `black_box` call may be its own CGU).
    let objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    assert!(
        !objs.is_empty(),
        "{stem} (opt={opt}): no object file produced"
    );

    let stubs_path = write_panic_stubs(&dir, &objs[0]);

    let bin = dir.join("bin");
    let mut link = Command::new("cc");
    link.arg("-o").arg(&bin);
    for obj in &objs {
        link.arg(obj);
    }
    link.arg(&stubs_path);
    let link = link.output().expect("cc link");
    assert!(
        link.status.success(),
        "{stem} (opt={opt}): link failed. stderr: <<<{}>>>",
        String::from_utf8_lossy(&link.stderr)
    );

    let run = Command::new(&bin).output().expect("run compiled binary");
    let _ = std::fs::remove_dir_all(&dir);
    run.status.code().expect("process terminated by signal")
}

/// Compile `body` with BOTH backends at -Copt-level 0 and 3 and require the
/// trust-cg exit code to equal the LLVM exit code AND the documented `expected`.
fn differential_case(stem: &str, body: &str, expected: i32) {
    if !x86_64_std_available() {
        eprintln!("skipping {stem}: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    if !cfg!(target_arch = "x86_64") {
        eprintln!("skipping {stem} execution: host is not x86_64");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = format!(
        "#![no_std]\n#![no_main]\n\
         #[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! {{ loop {{}} }}\n\
         #[no_mangle]\npub extern \"C\" fn main() -> i32 {{\n{body}\n}}\n"
    );
    for opt in ["0", "3"] {
        let llvm = compile_link_run(stem, &src, opt, None);
        let trust = compile_link_run(stem, &src, opt, Some(&dylib));
        assert_eq!(
            llvm, expected,
            "{stem} (opt={opt}): LLVM oracle returned {llvm}, expected {expected}"
        );
        assert_eq!(
            trust, llvm,
            "{stem} (opt={opt}): trust-cg returned {trust} but LLVM returned {llvm} (miscompile)"
        );
    }
}

/// The canonical m51 repro: `(-100i8) >> 1`. A signed (arithmetic) shift right
/// of an i8 produced by a narrowing cast. -100 >> 1 = -50; `-50i8 as u8` = 206.
/// Before the fix the narrow carrier was zero-extended, so SAR shifted in zeros
/// (a logical shift) and the result was wrong.
#[test]
fn m51_i8_arithmetic_shift_right_from_narrowing_cast_matches_llvm() {
    differential_case(
        "i8_sar",
        "    let x: i8 = core::hint::black_box(-100i32) as i8;\n\
         \x20   let r: i8 = x >> 1;\n\
         \x20   (r as u8) as i32",
        206,
    );
}

/// i16 variant: `(-100i16) >> 2` = -25; `-25i16 as u16 as i32` low byte == 231.
/// Exercises the `MOVSXW` width of the narrow sign-extension.
#[test]
fn m51_i16_arithmetic_shift_right_from_narrowing_cast_matches_llvm() {
    differential_case(
        "i16_sar",
        "    let x: i16 = core::hint::black_box(-100i32) as i16;\n\
         \x20   let r: i16 = x >> 2;\n\
         \x20   ((r as u16) as i32) & 0xff",
        231,
    );
}

/// CONTROL: an UNSIGNED (logical) shift right of a narrow value must NOT be
/// sign-extended — it relies on the zero-extended carrier. `156u8 >> 1` = 78.
/// (`-100i8` reinterpreted as `u8` is 156.) Guards against over-eager
/// sign-extension that would corrupt unsigned shifts.
#[test]
fn m51_u8_logical_shift_right_stays_unsigned_matches_llvm() {
    differential_case(
        "u8_shr",
        "    let x: u8 = core::hint::black_box(-100i32) as u8;\n\
         \x20   let r: u8 = x >> 1;\n\
         \x20   r as i32",
        78,
    );
}

/// Signed division of a narrow value from a narrowing cast: `-100i8 / 3i8`
/// = -33; `-33i8 as u8` = 223. Exercises the IDIV dividend+divisor
/// sign-extension half of the m51 fix.
#[test]
fn m51_i8_signed_division_from_narrowing_cast_matches_llvm() {
    differential_case(
        "i8_sdiv",
        "    let x: i8 = core::hint::black_box(-100i32) as i8;\n\
         \x20   let d: i8 = core::hint::black_box(3i32) as i8;\n\
         \x20   (((x / d) as u8) as i32)",
        223,
    );
}

/// Signed remainder of a narrow value: `-100i8 % 3i8` = -1; `-1i8 as u8` = 255.
/// Exercises the IDIV remainder path with the same sign-extension.
#[test]
fn m51_i8_signed_remainder_from_narrowing_cast_matches_llvm() {
    differential_case(
        "i8_srem",
        "    let x: i8 = core::hint::black_box(-100i32) as i8;\n\
         \x20   let d: i8 = core::hint::black_box(3i32) as i8;\n\
         \x20   (((x % d) as u8) as i32)",
        255,
    );
}
