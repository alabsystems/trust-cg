#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test for the rustc_codegen_trust_cg x86_64 target path.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: WS4 milestone M1, x86_64 target support.
//
// Companion to `hello_loop.rs`, which exercises the AArch64 path. This test
// drives the std-`fn main` entry pipeline with an explicit
// `--target x86_64-apple-darwin`.
//
// HISTORY: an earlier milestone had the entry wrapper synthesize a `lang_start`
// *stub* that returned 0 without ever calling the user's `main`. That was a bug
// (the program never ran); it has been fixed — `lang_start` is now an external
// symbol the entry wrapper genuinely calls, and a default-allocator shim is
// emitted. A std `fn main` like `fn main() { loop {} }` is now blocked only at
// the final step: lowering `std::rt::lang_start::<()>`, whose MIR builds a
// closure and a `&dyn Fn` trait object the backend cannot yet lower. The bridge
// fails closed with a precise diagnostic rather than miscompiling.
//
// This test therefore asserts the x86_64 entry+allocator progress: the bridge
// fails closed specifically on the lang_start closure (NOT on the allocator
// link error that used to block this program), and — via the test-only
// `TRUST_CG_TEST_SKIP_LANG_START` gate — that the emitted entry/allocator
// objects are x86_64 Mach-O (the bridge honoured `--target x86_64` and routed
// through trust-cg's x86_64 backend, not the AArch64 pipeline). Real x86_64
// execution of compute programs is covered by `no_main_compute_x86.rs`.
//
// Running this test:
//
//     cd crates/rustc-codegen-trust-cg
//     targo --unverified test --release -- --nocapture
//
// Prerequisites: the installed Trust package this crate pins
// (`rust-toolchain.toml` `channel = "trust"`; it ships the rustc_private crates
// and llvm-tools), with an `x86_64-apple-darwin` std in its sysroot.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = host_target_support::X86_64_TARGET;

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

/// The backend sibling of this Cargo test executable, not another profile or
/// whichever cached library happens to have the newest modification time.
fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn write_temp_source(stem: &str, contents: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!("rcl2_{}_{}.rs", stem, std::process::id()));
    std::fs::write(&path, contents).expect("failed to write temp source file");
    path
}

/// Whether the `x86_64-apple-darwin` rust-std component is installed for the
/// pinned toolchain. Without it, `trustc --target x86_64-apple-darwin` cannot
/// find `std` and the test cannot run; we skip rather than fail so the suite
/// stays green on hosts that have not added the target.
fn x86_64_std_available() -> bool {
    toolchain_support::target_std_available(TARGET)
}

#[test]
fn m1_hello_loop_compiles_for_x86_64() {
    if !x86_64_std_available() {
        eprintln!(
            "skipping: rust-std for {TARGET} is not in the {} toolchain's sysroot \
             (the installed Trust package ships no {TARGET} std today)",
            pinned_toolchain()
        );
        return;
    }

    let src = "fn main() { loop {} }\n";
    let src_path = write_temp_source("hello_loop_x86", src);

    let dylib = ensure_dylib_built();
    assert!(
        dylib.exists(),
        "backend dylib was not produced at {:?}",
        dylib
    );

    let out_bin =
        std::env::temp_dir().join(format!("rcl2_hello_loop_x86_out_{}", std::process::id()));

    let backend_arg = {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(&dylib);
        s
    };
    let output = toolchain_support::rustc_command()
        .arg(&backend_arg)
        .args(["--target", TARGET, "-Cpanic=abort"])
        .arg("-o")
        .arg(&out_bin)
        .arg(&src_path)
        .output()
        .expect("failed to spawn trustc");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc stdout:\n{stdout}");
    eprintln!("rustc exit: {:?}", output.status);

    let _ = std::fs::remove_file(&src_path);

    let load_failure_markers = [
        "failed to load",
        "could not load",
        "dlopen",
        "image not found",
        "Library not loaded",
    ];
    for marker in &load_failure_markers {
        assert!(
            !stderr.contains(marker),
            "rustc failed to load our backend dylib \
             (matched marker: {marker:?}). stderr: <<<{stderr}>>>"
        );
    }

    // The std `fn main` now COMPILES and LINKS on x86_64: the bridge lowers
    // `lang_start::<()>`'s `move` closure, emits the `&dyn Fn() -> i32` vtable as
    // a data-relocated global, builds the fat pointer, and calls
    // `lang_start_internal`. (`fn main() { loop {} }` diverges, so we assert it
    // BUILDS rather than running it — `std_main_run_x86.rs` runs terminating
    // programs and checks exit codes against the LLVM backend.) This must NOT
    // regress to the old fail-closed-on-`lang_start` path, nor to the allocator
    // link error (#2).
    assert!(
        output.status.success(),
        "x86_64 std `fn main` failed to compile/link; the closure + `&dyn Fn` vtable path \
         should now succeed. stderr: <<<{stderr}>>>"
    );
    assert!(
        !stderr.contains("failing closed"),
        "x86_64 std `fn main` unexpectedly failed closed; the closure/vtable path should now \
         compile. stderr: <<<{stderr}>>>"
    );
    assert!(
        !stderr.contains("Undefined symbols"),
        "x86_64 hello-loop has an undefined symbol at link (allocator shim / vtable method / \
         dispatch-shim stub should all be defined). stderr: <<<{stderr}>>>"
    );
    let _ = std::fs::remove_file(&out_bin);

    // Decisive target-awareness assertion: with the un-lowerable `lang_start`
    // skipped (test-only gate), the bridge still emits the entry wrapper and
    // allocator shim — and they must be x86_64 Mach-O objects (the bridge
    // honoured `--target x86_64`, routing through trust-cg's x86_64 backend,
    // not the AArch64 pipeline). We assert object format via the toolchain's
    // `llvm-objdump`.
    let obj_dir =
        std::env::temp_dir().join(format!("rcl2_hello_loop_x86_obj_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&obj_dir);
    std::fs::create_dir_all(&obj_dir).expect("create obj dir");
    let obj_src = obj_dir.join("prog.rs");
    std::fs::write(&obj_src, src).expect("write source");
    let obj_out = obj_dir.join("out");
    let obj_output = toolchain_support::rustc_command()
        .arg(&backend_arg)
        .args(["--target", TARGET, "-Cpanic=abort"])
        .arg("--emit=obj")
        .arg("-o")
        .arg(&obj_out)
        .arg(toolchain_support::backend_knobs_arg(&[
            "test-skip-lang-start",
        ]))
        .arg(&obj_src)
        .output()
        .expect("failed to spawn trustc (obj emit)");
    assert!(
        obj_output.status.success(),
        "with lang_start skipped, the x86_64 bridge must still emit objects. stderr: <<<{}>>>",
        String::from_utf8_lossy(&obj_output.stderr)
    );

    // Find the entry wrapper object and confirm it is x86_64 Mach-O.
    let sysroot = toolchain_support::rustc_driver_command()
        .args(["--print", "sysroot"])
        .output()
        .expect("rustc --print sysroot");
    let sysroot = String::from_utf8_lossy(&sysroot.stdout).trim().to_owned();
    let objdump = PathBuf::from(sysroot)
        .join("lib/rustlib")
        .join(TARGET)
        .join("bin/llvm-objdump");

    let mut checked = 0;
    for entry in std::fs::read_dir(&obj_dir).expect("read obj dir") {
        let path = entry.expect("dir entry").path();
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        if name.ends_with(".rustc_entry_main.rcgu.o") || name.ends_with(".allocator_shim.rcgu.o") {
            let dump = Command::new(&objdump)
                .arg("-d")
                .arg(&path)
                .output()
                .expect("llvm-objdump");
            let fmt = String::from_utf8_lossy(&dump.stdout);
            assert!(
                fmt.contains("x86-64") || fmt.contains("x86_64"),
                "{name} is not an x86_64 Mach-O object (bridge did not honour --target x86_64): \
                 {}",
                fmt.lines().take(3).collect::<Vec<_>>().join(" | ")
            );
            assert!(
                !fmt.contains("arm64") && !fmt.contains("aarch64"),
                "{name} unexpectedly reports an AArch64 architecture: {}",
                fmt.lines().take(3).collect::<Vec<_>>().join(" | ")
            );
            checked += 1;
        }
    }
    assert!(
        checked >= 2,
        "expected both the entry wrapper and allocator shim x86_64 objects, found {checked}"
    );

    let _ = std::fs::remove_dir_all(&obj_dir);
}
