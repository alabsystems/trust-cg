// Integration test: x86 drop-glue Slice 1 — a USER `impl Drop` on a plain struct
// whose fields are all `Copy` (no-drop). This is the smallest genuinely-new
// droppable shape beyond the Box/Vec/String/map FLOOR, and the unblocker for the
// EH `TCG_ENABLE_UNWIND` flip (a cleanup-bearing frame's `drop(_g)` now lowers).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Each program is compiled for x86_64 through the rustc_codegen_trust_cg bridge at
// -O0/-O2/-O3 alongside the default LLVM backend. The HARD INVARIANT (a wrong drop
// is a P0 miscompile — a wrong side effect / double-free / use-after-free): trust-cg
// either FAILS CLOSED (refuses to compile) OR produces the EXACT SAME exit code as
// LLVM. A `Drop` that increments a static counter must run EXACTLY ONCE per value.
//
// Coverage:
//   * FLOOR regression: Box<i32>/Vec<i32>/String drop on a normal return still free.
//   * Slice 1 POSITIVE: a 1-field and a multi-Copy-field `Guard` drop runs once and
//     matches LLVM; a drop in a taken/untaken branch; NO double-free on a moved-out
//     value (rustc drop flags). These MUST compile and match (not just fail closed).
//   * Slices 2-6 STILL FAIL CLOSED: a struct with a droppable (`Vec`) field, a user
//     `Drop` + droppable field, an `enum` with a `Drop` impl, and an array of
//     needs-drop elements — each must fail closed OR match (never a wrong value).

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
    let dir = std::env::temp_dir().join(format!("rcl2_m133_{stem}_{}", std::process::id()));
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

/// THE CORE INVARIANT: trust-cg either fails closed OR matches LLVM — never a
/// wrong value. Each `src` is a complete program that `std::process::exit`s with a
/// value (a drop counter). Runs at O0/O2/O3.
fn assert_failclosed_or_matches(dylib: &Path, dir: &Path, name: &str, src: &str) {
    for opt in ["0", "2", "3"] {
        let (lout, lbin) = try_compile(dir, &format!("{name}_l"), src, None, opt);
        assert!(
            lout.status.success(),
            "LLVM compile of `{name}` (opt={opt}) failed: {}",
            String::from_utf8_lossy(&lout.stderr)
        );
        let llvm = run_exit_code(&lbin);

        let (tout, tbin) = try_compile(dir, &format!("{name}_t"), src, Some(dylib), opt);
        if !tout.status.success() {
            continue; // fail-closed is SOUND
        }
        let tcg = run_exit_code(&tbin);
        assert_eq!(
            tcg, llvm,
            "[P0 MISCOMPILE] `{name}` (opt={opt}): trust-cg produced a WRONG value \
             tcg={tcg} vs llvm={llvm} (must fail closed OR match)"
        );
    }
}

/// A POSITIVE check: `src` MUST compile on trust-cg at every opt level and match
/// LLVM — used for the Slice-1 shapes that are now supported (a wrong count, a
/// missed drop, or a double-free would diverge from LLVM's exit code).
fn assert_compiles_and_matches(dylib: &Path, dir: &Path, name: &str, src: &str) {
    for opt in ["0", "2", "3"] {
        let (lout, lbin) = try_compile(dir, &format!("{name}_l"), src, None, opt);
        assert!(lout.status.success(), "LLVM compile of `{name}` failed");
        let llvm = run_exit_code(&lbin);
        let (tout, tbin) = try_compile(dir, &format!("{name}_t"), src, Some(dylib), opt);
        assert!(
            tout.status.success(),
            "[SLICE-1 REGRESSION] trust-cg failed to compile `{name}` (opt={opt}) — the \
             user-Drop-with-Copy-fields shape must lower: {}",
            String::from_utf8_lossy(&tout.stderr)
        );
        let tcg = run_exit_code(&tbin);
        assert_eq!(
            tcg, llvm,
            "[P0 MISCOMPILE] `{name}` (opt={opt}): tcg={tcg} vs llvm={llvm}"
        );
    }
}

// A drop counter that does NOT use atomics (the backend fails closed on
// `atomic_load`/`atomic_xadd` intrinsics — unrelated to drop glue). A `static mut`
// RMW is supported and gives an observable, exact drop-count side effect.
const CTR: &str = "use std::hint::black_box as bb;\n\
    static mut TOTAL: i32 = 0;\n\
    #[inline(never)] fn add(x: i32) { unsafe { TOTAL += x; } }\n\
    #[inline(never)] fn total() -> i32 { unsafe { TOTAL } }\n";

/// FLOOR regression: Box/Vec/String dropped on a NORMAL return still free exactly
/// once (differential vs LLVM). This is the pinned baseline the Slice-1 arm must
/// not disturb.
#[test]
fn floor_heap_drop_still_frees() {
    if !host_is_x86_64() || !x86_64_std_available() {
        eprintln!("skipping: needs x86_64 host + rust-std for {TARGET}");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("floor");
    let src = "use std::hint::black_box as bb;\n\
        #[inline(never)] fn ub() -> i32 { let b = Box::new(bb(7i32)); *b * 3 }\n\
        #[inline(never)] fn uv() -> i32 { let mut v: Vec<i32> = Vec::new(); \
            for i in 0..bb(5) { v.push(i); } v.iter().sum() }\n\
        #[inline(never)] fn us() -> i32 { let mut s = String::from(bb(\"ab\")); \
            s.push_str(bb(\"cde\")); s.len() as i32 }\n\
        fn main() { std::process::exit(ub() + uv() + us()); }\n";
    assert_compiles_and_matches(&dylib, &dir, "floor", src);
}

/// SLICE 1 POSITIVE: a user `impl Drop` runs exactly once per scope exit and
/// matches LLVM at O0/O2/O3.
#[test]
fn user_drop_copy_fields_runs_once_and_matches() {
    if !host_is_x86_64() || !x86_64_std_available() {
        eprintln!("skipping: needs x86_64 host + rust-std for {TARGET}");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("pos");

    // 1-field guard, two scope exits -> +7 then +100 = 107.
    let one_field = format!(
        "{CTR}struct Guard {{ n: i32 }}\n\
         impl Drop for Guard {{ fn drop(&mut self) {{ add(self.n); }} }}\n\
         fn main() {{ {{ let _g = Guard {{ n: bb(7) }}; }} \
         {{ let _g = Guard {{ n: bb(100) }}; }} std::process::exit(total()); }}\n"
    );
    assert_compiles_and_matches(&dylib, &dir, "one_field", &one_field);

    // Multi Copy fields (i32 + i64 + u8); drop reads all -> 3+40+2 = 45 once.
    let multi = format!(
        "{CTR}struct Guard {{ a: i32, b: i64, c: u8 }}\n\
         impl Drop for Guard {{ fn drop(&mut self) {{ \
            add(self.a + self.b as i32 + self.c as i32); }} }}\n\
         fn main() {{ let g = Guard {{ a: bb(3), b: bb(40), c: bb(2) }}; \
            let _ = bb(g.a); drop(g); std::process::exit(total()); }}\n"
    );
    assert_compiles_and_matches(&dylib, &dir, "multi_field", &multi);

    // Drop in a branch: taken (+5) and untaken (never +999).
    let branch = format!(
        "{CTR}struct Guard {{ n: i32 }}\n\
         impl Drop for Guard {{ fn drop(&mut self) {{ add(self.n); }} }}\n\
         fn main() {{ if bb(true) {{ let _g = Guard {{ n: bb(5) }}; }} \
            if bb(false) {{ let _g = Guard {{ n: bb(999) }}; }} \
            std::process::exit(total()); }}\n"
    );
    assert_compiles_and_matches(&dylib, &dir, "branch", &branch);

    // NO double-free: a moved-out value's Drop runs EXACTLY once (drop flags) -> 11.
    let moved = format!(
        "{CTR}struct Guard {{ n: i32 }}\n\
         impl Drop for Guard {{ fn drop(&mut self) {{ add(self.n); }} }}\n\
         #[inline(never)] fn sink(g: Guard) {{ let _ = bb(g.n); }}\n\
         fn main() {{ let g = Guard {{ n: bb(11) }}; sink(g); \
            std::process::exit(total()); }}\n"
    );
    assert_compiles_and_matches(&dylib, &dir, "moved_out_no_double_free", &moved);
}

/// SLICES 2-6 STILL FAIL CLOSED (never a wrong value): a droppable field, a user
/// Drop plus a droppable field, an enum with a Drop impl, and an array of
/// needs-drop elements. Each must fail closed OR match LLVM.
#[test]
fn droppable_field_enum_and_needs_drop_elem_stay_fail_closed() {
    if !host_is_x86_64() || !x86_64_std_available() {
        eprintln!("skipping: needs x86_64 host + rust-std for {TARGET}");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("fc");

    // Slice 2: struct with a Vec field, no user Drop.
    let vec_field = "use std::hint::black_box as bb;\n\
        struct S { v: Vec<i32>, k: i32 }\n\
        fn main() { let s = S { v: vec![bb(1), bb(2), bb(3)], k: bb(9) }; \
            std::process::exit(s.v.iter().sum::<i32>() + s.k); }\n";
    assert_failclosed_or_matches(&dylib, &dir, "vec_field", vec_field);

    // Slice 3: user Drop AND a droppable (Vec) field.
    let drop_and_vec = format!(
        "{CTR}struct S {{ v: Vec<i32>, n: i32 }}\n\
         impl Drop for S {{ fn drop(&mut self) {{ add(self.n); }} }}\n\
         fn main() {{ let s = S {{ v: vec![bb(1), bb(2)], n: bb(4) }}; \
            let _ = bb(s.v.len()); drop(s); std::process::exit(total()); }}\n"
    );
    assert_failclosed_or_matches(&dylib, &dir, "drop_and_vec", &drop_and_vec);

    // Slice 4: enum with a Drop impl.
    let enum_drop = format!(
        "{CTR}enum E {{ A(i32), B }}\n\
         impl Drop for E {{ fn drop(&mut self) {{ \
            if let E::A(x) = self {{ add(*x); }} else {{ add(1); }} }} }}\n\
         fn main() {{ {{ let _e = E::A(bb(8)); }} {{ let _e = E::B; }} \
            std::process::exit(total()); }}\n"
    );
    assert_failclosed_or_matches(&dylib, &dir, "enum_drop", &enum_drop);

    // Slice 3: array of needs-drop elements [Guard; 3].
    let arr = format!(
        "{CTR}struct Guard {{ n: i32 }}\n\
         impl Drop for Guard {{ fn drop(&mut self) {{ add(self.n); }} }}\n\
         fn main() {{ let a = [Guard {{ n: bb(1) }}, Guard {{ n: bb(2) }}, Guard {{ n: bb(3) }}]; \
            let _ = bb(a[0].n); drop(a); std::process::exit(total()); }}\n"
    );
    assert_failclosed_or_matches(&dylib, &dir, "array_needs_drop_elem", &arr);
}
