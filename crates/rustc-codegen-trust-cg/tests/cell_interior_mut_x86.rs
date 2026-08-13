// Integration test: interior-mutability (`Cell` / `UnsafeCell`) completeness +
// stale-read soundness for the trust-cg bridge on x86_64 (COMPLETE-11 subset).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS EXISTS (COMPLETE-11): `Cell<iN>` accessor calls (`get`/`set`/`replace`)
// fail closed at rustc `-O0` because `main` passes `&c` (a shared reference to the
// interior-mutable cell local) as a call argument, and the scalarized snapshot model
// has no address to pass ("direct call aggregate reference arg 0 before aggregate
// borrow binding"). At `-O3` the accessors inline to `&raw` ops the RawPtr scalar-cell
// pass already handles, so the ENVELOPE was opt-fragmented. The fix cells an
// interior-mutable scalar cell whose `&c` borrow is a call argument, giving it a stable
// slot; `&c` then binds to the slot pointer and every get/set/replace routes through
// the slot with NO register caching across the call (the interior-mutability
// discipline). This test pins BOTH the correctness (bridge == LLVM at O0 AND O3) and
// the SOUNDNESS (set-then-read across a call / across a loop reads the NEW value — no
// stale-read-past-store), plus the deferred shapes still failing closed.

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
    assert!(status.success(), "cargo build failed; cannot run cell test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_cellmut_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src` with the LLVM (default) backend. Returns the exit code.
fn compile_run_llvm(dir: &Path, name: &str, src: &str, opt_level: &str) -> i32 {
    let src_path = dir.join(format!("{name}_llvm.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(format!("{name}_llvm"));
    let output = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin", "--target", TARGET, "-Cpanic=abort"])
        .arg(format!("-Copt-level={opt_level}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path)
        .output()
        .expect("spawn rustc (llvm)");
    assert!(
        output.status.success(),
        "LLVM reference compile of `{name}` at -Copt-level={opt_level} failed: <<<{}>>>",
        String::from_utf8_lossy(&output.stderr)
    );
    run_exit_code(&bin)
}

/// Attempt to compile `src` with the trust-cg bridge. Returns Ok(exit code) on a
/// successful compile+run, or Err(stderr) if the bridge failed closed.
fn compile_bridge(
    dir: &Path,
    name: &str,
    src: &str,
    dylib: &Path,
    opt_level: &str,
) -> Result<i32, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);
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
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(run_exit_code(&bin))
}

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// Programs that MUST compile through the bridge and match LLVM at O0 AND O3.
/// Each uses `black_box` so the compiler cannot const-fold the interior mutation.
const CELL_MATCH: &[(&str, &str)] = &[
    // Cell::new + set + get: 37.
    (
        "cell_get_set",
        "use std::cell::Cell; use std::hint::black_box as bb; \
         fn main() { let c = Cell::new(bb(10u32)); c.set(bb(37)); \
         std::process::exit((c.get() % 126) as i32); }",
    ),
    // Cell counter in a loop: set-then-read across iterations -> 45.
    (
        "cell_loop_counter",
        "use std::cell::Cell; use std::hint::black_box as bb; \
         fn main() { let c = Cell::new(bb(0u32)); for i in 0..bb(10u32) { c.set(c.get() + i); } \
         std::process::exit((c.get() % 126) as i32); }",
    ),
    // Cell::replace returns the old value: 5 + 20 = 25.
    (
        "cell_replace",
        "use std::cell::Cell; use std::hint::black_box as bb; \
         fn main() { let c = Cell::new(bb(5u32)); let old = c.replace(bb(20)); \
         std::process::exit(((old + c.get()) % 126) as i32); }",
    ),
    // Signed / narrow carrier: Cell<i64>.
    (
        "cell_i64",
        "use std::cell::Cell; use std::hint::black_box as bb; \
         fn main() { let c = Cell::new(bb(-3i64)); c.set(c.get() + bb(45i64)); \
         std::process::exit((c.get() % 126) as i32); }",
    ),
    // ADVERSARIAL STALE-READ across a call: read, mutate through a shared ref in a
    // separate (non-inlined at O0) function, read again. The second read MUST observe
    // the new value (no cached load past the store). 40 + 41 = 81.
    (
        "cell_stale_across_call",
        "use std::cell::Cell; use std::hint::black_box as bb; \
         #[inline(never)] fn bump(c: &Cell<u32>) { c.set(c.get() + bb(1)); } \
         fn main() { let c = Cell::new(bb(40u32)); let a = c.get(); bump(&c); let b = c.get(); \
         std::process::exit(((a + b) % 126) as i32); }",
    ),
    // UnsafeCell directly via get() raw pointer read/write.
    (
        "unsafe_cell_rw",
        "use std::cell::UnsafeCell; use std::hint::black_box as bb; \
         fn main() { let c = UnsafeCell::new(bb(30u32)); \
         unsafe { *c.get() = bb(42); std::process::exit((*c.get() % 126) as i32); } }",
    ),
];

/// The interior-mutability completeness + soundness matrix: every CELL_MATCH program
/// compiles through the bridge and matches LLVM at BOTH O0 and O3. Special attention
/// to the stale-read probes (a cached load past a set() would MISCOMPILE).
#[test]
fn cell_interior_mut_matches_llvm_o0_o3() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("match");

    for opt_level in ["0", "3"] {
        for (name, src) in CELL_MATCH {
            let expected = compile_run_llvm(&dir, name, src, opt_level);
            let got = compile_bridge(
                &dir,
                &format!("{name}_o{opt_level}"),
                src,
                &dylib,
                opt_level,
            )
            .unwrap_or_else(|err| {
                panic!(
                    "interior-mut COMPLETENESS regression: `{name}` failed closed at \
                     -Copt-level={opt_level} (must compile): <<<{err}>>>"
                )
            });
            assert_eq!(
                got, expected,
                "interior-mut MISCOMPILE (possible stale-read-past-store): `{name}` at \
                 -Copt-level={opt_level}: bridge exit {got}, LLVM exit {expected}"
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// Deferred shapes that MUST stay fail-closed (never silently miscompile): `RefCell`
/// borrow/borrow_mut return a `Ref`/`RefMut` guard whose Drop decrements the borrow
/// flag — blocked on user Drop glue (COMPLETE-4, not landed); `Rc` adds heap +
/// refcount + Drop. A bridge compile of these must ERROR (fail closed), not produce a
/// runnable binary. `RefCell::into_inner` (no guard) is deliberately NOT in this list —
/// it already compiles.
const DEFERRED_FAIL_CLOSED: &[(&str, &str)] = &[
    (
        "refcell_borrow_mut",
        "use std::cell::RefCell; use std::hint::black_box as bb; \
         fn main() { let c = RefCell::new(bb(1u32)); *c.borrow_mut() += bb(40); \
         std::process::exit((*c.borrow() % 126) as i32); }",
    ),
    (
        "rc_clone_count",
        "use std::rc::Rc; use std::hint::black_box as bb; \
         fn main() { let r = Rc::new(bb(10u32)); let r2 = Rc::clone(&r); \
         let c = Rc::strong_count(&r); std::process::exit(((*r2 + c as u32) % 126) as i32); }",
    ),
];

/// Negative test: the deferred interior-mutability / shared-ownership shapes must fail
/// closed at BOTH opt levels rather than compile-and-miscompile (soundness doctrine —
/// fail-closed always beats miscompile).
#[test]
fn cell_deferred_shapes_fail_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("deferred");

    for opt_level in ["0", "3"] {
        for (name, src) in DEFERRED_FAIL_CLOSED {
            let result = compile_bridge(
                &dir,
                &format!("{name}_o{opt_level}"),
                src,
                &dylib,
                opt_level,
            );
            assert!(
                result.is_err(),
                "SOUNDNESS: deferred shape `{name}` at -Copt-level={opt_level} unexpectedly \
                 COMPILED (exit {:?}); it must fail closed until its Drop/heap glue lands, \
                 not silently miscompile",
                result.ok()
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}
