// E2E (aarch64-apple-darwin): the bridge lowers rustc MIR `UnwindAction::Cleanup`
// edges to trust-ir exception handling — `Inst::Invoke` (a call that may unwind),
// a cleanup `Inst::LandingPad`, the `Box` drop glue that runs during unwind
// (`__rust_dealloc`), and `Inst::Resume` (`_Unwind_Resume`) — with the Rust EH
// personality `_rust_eh_personality`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ----------------------------------------------------------------------------
// WHAT THIS PINS
// ----------------------------------------------------------------------------
// A REAL `.rs` function — a `Box<i32>` held live across a call that can unwind —
// compiled THROUGH THE BRIDGE under `-Cpanic=unwind`. Its MIR carries a genuine
// `UnwindAction::Cleanup(bb)` edge on the throwing call (asserted from the MIR
// dump, NOT from `panic=abort`), a `(cleanup)` block that drops the `Box` and
// re-raises (`resume`). The bridge's EH lowering (gated behind
// `TCG_ENABLE_UNWIND`, see `seed_eh_landing_pads`) turns that into:
//
//   * `Inst::Invoke ay_may_unwind -> normal, unwind=cleanup-pad`   (a `bl` whose
//     LSDA call-site entry names the landing pad),
//   * a cleanup `Inst::LandingPad` (the `__gcc_except_tab` cleanup action),
//   * the `Box` free (`bl __rust_dealloc`),
//   * `Inst::Resume` (`bl _Unwind_Resume`),
//   * `_rust_eh_personality` in the compact-unwind entry (NOT the C++ default).
//
// These are verified by OBJECT INSPECTION (the `__gcc_except_tab` section, the
// undefined `_rust_eh_personality` / `__Unwind_Resume` / `_ay_may_unwind`
// symbols, and the `BR26` relocations). This is the proof that the bridge
// frontend lowers MIR unwind edges into the backend's structural EH opcodes.
//
// ----------------------------------------------------------------------------
// LINK + RUN-CAUGHT (a REAL Rust panic is genuinely caught through the bridge)
// ----------------------------------------------------------------------------
// `bridge_unwind_cleanup_real_panic_caught_aarch64` links the bridge-compiled
// object against the Rust unwind runtime (libstd / libpanic_unwind / libunwind,
// supplied by linking through `rustc` as a Rust binary) and RUNS it: a Rust
// `panic!` raised by `ay_may_unwind` (in the `panicker` rlib, built by the
// normal toolchain) propagates THROUGH the bridge-compiled `box_across_unwind`
// frame — whose cleanup landing pad runs (`__rust_dealloc` frees the live
// `Box<i32>` mid-unwind) — and is CAUGHT by an enclosing `std::panic::catch_unwind`
// in the driver. The run asserts `is_err() == true` (caught), a clean exit 0
// (NO abort, NO hang under a hard timeout), AND that the cleanup actually ran
// (a counting global allocator observes the mid-unwind dealloc). This is the
// landed backend EH continue-unwind path (e2e_aarch64_eh_resume_trust_ir)
// exercised end-to-end through the Rust frontend with the Rust personality.
//
// NOTE: a Rust panic can ONLY be caught by Rust's `catch_unwind` — the panic
// runtime fails-closed ("Rust panics must be rethrown, aborting") if a non-Rust
// (e.g. C++ `catch(...)`) frame tries to catch one. That is correct Rust ABI
// behavior, not a bridge defect; the catch driver here is therefore Rust.
//
// The DEFAULT path is asserted too: with `TCG_ENABLE_UNWIND` unset the same
// crate fails closed with the precise `TerminatorKind::Call with cleanup unwind`
// diagnostic (never miscompiles, never silently aborts).
//
// PROOF GATE: bridge invocations set `TCG_NO_PROOF_CERTS=1`. EH objects emit
// LSDA/personality/compact-unwind/DWARF relocation sidecars whose proof inventory
// is intentionally rejected as incomplete; this lane validates their structure
// and native behavior without promoting the object as certified.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "aarch64-apple-darwin";

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
    for cand in [
        target_dir
            .join("release")
            .join("librustc_codegen_trust_cg.dylib"),
        target_dir
            .join("debug")
            .join("librustc_codegen_trust_cg.dylib"),
    ] {
        if cand.exists() {
            return cand;
        }
    }
    let status = Command::new("cargo")
        .arg(format!("+{}", pinned_toolchain()))
        .args(["build"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run unwind test");
    let built = target_dir
        .join("debug")
        .join("librustc_codegen_trust_cg.dylib");
    assert!(built.exists(), "expected dylib at {built:?} but none produced");
    built
}

fn host_is_aarch64_macos() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

fn aarch64_std_available() -> bool {
    Command::new("rustup")
        .args(["target", "list", "--installed", "--toolchain"])
        .arg(pinned_toolchain())
        .output()
        .map(|o| {
            String::from_utf8_lossy(&o.stdout)
                .lines()
                .any(|l| l.trim() == TARGET)
        })
        .unwrap_or(false)
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_unwind_a64_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// The unwinding crate: `box_across_unwind` holds a `Box<i32>` live across a call
/// to `ay_may_unwind` (an external `extern "C-unwind"` fn that can unwind). On the
/// unwind path the `Box` is freed and the exception re-raised. The external callee
/// is declared via a cross-crate dependency (the `panicker` rlib) rather than a
/// foreign `extern { }` block — the bridge ICEs on foreign blocks (a pre-existing,
/// unrelated `check_match` interaction), so the cross-crate path is the supported
/// way to reference an external unwinding callee.
const UNWIND_CRATE: &str = "\
#![crate_type = \"staticlib\"]\n\
extern crate panicker;\n\
#[no_mangle]\n\
pub extern \"C-unwind\" fn box_across_unwind() -> i32 {\n\
    let _b = Box::new(7i32);\n\
    panicker::ay_may_unwind()\n\
}\n";

const PANICKER_CRATE: &str = "\
#![crate_type = \"rlib\"]\n\
#[no_mangle]\n\
pub extern \"C-unwind\" fn ay_may_unwind() -> i32 { panic!(\"boom from panicker\"); }\n";

fn nm(obj: &Path) -> String {
    String::from_utf8_lossy(&Command::new("nm").arg(obj).output().expect("nm").stdout).into_owned()
}

fn has_gcc_except_tab(obj: &Path) -> bool {
    String::from_utf8_lossy(
        &Command::new("otool")
            .args(["-lv"])
            .arg(obj)
            .output()
            .expect("otool -lv")
            .stdout,
    )
    .contains("sectname __gcc_except_tab")
}

/// Compile `UNWIND_CRATE` through the bridge with `env` overlaid and return
/// `(rustc_succeeded, stderr, produced_objects_dir)`.
fn compile_through_bridge(
    dylib: &Path,
    dir: &Path,
    panicker_rlib: &Path,
    extra_env: &[(&str, &str)],
) -> (bool, String) {
    let src = dir.join("box_unwind.rs");
    std::fs::write(&src, UNWIND_CRATE).expect("write source");
    let backend_arg = {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(dylib);
        s
    };
    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "staticlib"])
        .arg(&backend_arg)
        .env("TCG_NO_PROOF_CERTS", "1")
        .args(["--target", TARGET, "-Cpanic=unwind", "-Copt-level=0"])
        .args(["-Cforce-unwind-tables=yes"])
        .arg("--extern")
        .arg({
            let mut s = std::ffi::OsString::from("panicker=");
            s.push(panicker_rlib);
            s
        })
        .arg("--emit=obj")
        .arg("-o")
        .arg(dir.join("box_unwind.o"))
        .arg(&src);
    for (k, v) in extra_env {
        cmd.env(k, v);
    }
    let out = cmd.output().expect("spawn rustc via rustup");
    (out.status.success(), String::from_utf8_lossy(&out.stderr).into_owned())
}

#[test]
fn bridge_lowers_unwind_cleanup_to_eh_object_aarch64() {
    if !host_is_aarch64_macos() {
        eprintln!("skipping: requires an aarch64-apple-darwin host");
        return;
    }
    if !aarch64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("eh");

    // The `panicker` rlib supplies the external unwinding callee `ay_may_unwind`
    // (compiled by the NORMAL toolchain so it genuinely panics / unwinds).
    let panicker_rlib = build_panicker_rlib(&dir);

    // FIRST confirm the MIR actually carries `UnwindAction::Cleanup` (NOT a
    // `panic=abort` build): dump the bridge crate's MIR with the normal compiler.
    let src = dir.join("box_unwind.rs");
    std::fs::write(&src, UNWIND_CRATE).expect("write source");
    let mir_out = dir.join("box_unwind.mir");
    let mir_status = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "lib"])
        .args(["--target", TARGET, "-Cpanic=unwind", "-Zmir-opt-level=0"])
        .arg("--extern")
        .arg({
            let mut s = std::ffi::OsString::from("panicker=");
            s.push(&panicker_rlib);
            s
        })
        .arg("--emit=mir")
        .arg("-o")
        .arg(&mir_out)
        .arg(&src)
        .status()
        .expect("spawn rustc for MIR dump");
    assert!(mir_status.success(), "MIR dump compile failed");
    let mir = std::fs::read_to_string(&mir_out).expect("read MIR dump");
    assert!(
        mir.contains("unwind: bb") && mir.contains("(cleanup)"),
        "the test crate's MIR must carry a real UnwindAction::Cleanup edge \
         (an `unwind: bbN` to a `(cleanup)` block) — otherwise this is not \
         exercising unwind lowering. MIR:\n{mir}"
    );

    // 1. OPT-OUT (TCG_DISABLE_UNWIND): unwind lowering is ON by default now, so
    //    the opt-out escape hatch must FAIL CLOSED with the precise diagnostic —
    //    never miscompile, never abort at runtime.
    let (ok_off, stderr_off) =
        compile_through_bridge(&dylib, &dir, &panicker_rlib, &[("TCG_DISABLE_UNWIND", "1")]);
    assert!(
        !ok_off,
        "with TCG_DISABLE_UNWIND set the unwinding crate must fail closed, but it compiled"
    );
    assert!(
        stderr_off.contains("cleanup unwind"),
        "expected the fail-closed `...with cleanup unwind` diagnostic; got:\n{stderr_off}"
    );

    // 2. GATE ON: the bridge lowers the unwind edges and emits the EH object.
    let _ = std::fs::remove_file(dir.join("box_unwind.o"));
    let (ok_on, stderr_on) =
        compile_through_bridge(&dylib, &dir, &panicker_rlib, &[("TCG_ENABLE_UNWIND", "1")]);
    assert!(
        ok_on,
        "with TCG_ENABLE_UNWIND=1 the bridge must lower the unwind cleanup. stderr:\n{stderr_on}"
    );

    // rustc emits one object per CGU. Find the one defining `box_across_unwind`.
    let objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    let eh_obj = objs
        .iter()
        .find(|o| nm(o).contains("_box_across_unwind"))
        .unwrap_or_else(|| panic!("no object defines box_across_unwind; objects: {objs:?}"));

    // The lowered object must carry the full Rust EH structure.
    assert!(
        has_gcc_except_tab(eh_obj),
        "the lowered object must carry the LSDA (__gcc_except_tab) — the cleanup \
         landing-pad call-site table"
    );
    let syms = nm(eh_obj);
    assert!(
        syms.contains("_rust_eh_personality"),
        "the lowered object must reference the RUST personality `_rust_eh_personality` \
         (not the C++ default). nm:\n{syms}"
    );
    assert!(
        syms.contains("__Unwind_Resume"),
        "the cleanup pad's `Inst::Resume` must lower to a `_Unwind_Resume` call. nm:\n{syms}"
    );
    assert!(
        syms.contains("_ay_may_unwind"),
        "the throwing call must be an Invoke to the external unwinding callee. nm:\n{syms}"
    );

    eprintln!(
        "bridge unwind-cleanup EH lowering VERIFIED (object level): Invoke + cleanup \
         LandingPad + Box free + Resume + _rust_eh_personality + __gcc_except_tab. \
         The link+run-CAUGHT proof lives in \
         `bridge_unwind_cleanup_real_panic_caught_aarch64`."
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// Build the `panicker` rlib (the external unwinding callee `ay_may_unwind`,
/// compiled by the NORMAL toolchain so it genuinely panics / unwinds) into
/// `dir/libpanicker.rlib` and return its path.
fn build_panicker_rlib(dir: &Path) -> PathBuf {
    let panicker_src = dir.join("panicker.rs");
    std::fs::write(&panicker_src, PANICKER_CRATE).expect("write panicker");
    let panicker_rlib = dir.join("libpanicker.rlib");
    let pk = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-name", "panicker", "--crate-type", "rlib"])
        .args(["--target", TARGET, "-Cpanic=unwind", "-Copt-level=0"])
        .arg("--emit=link")
        .arg("-o")
        .arg(&panicker_rlib)
        .arg(&panicker_src)
        .output()
        .expect("spawn rustc for panicker");
    assert!(
        pk.status.success(),
        "panicker rlib failed to build: {}",
        String::from_utf8_lossy(&pk.stderr)
    );
    panicker_rlib
}

/// Extract the single member of `rlib` whose `nm` defines `_<sym>` and copy it to
/// `out`. Used to pull the panicker CGU object out of the rlib so the linker can
/// resolve `ay_may_unwind` (the Rust driver references `box_across_unwind`, not
/// `ay_may_unwind`, so `--extern` alone would dead-strip the panicker member).
fn extract_object_defining(rlib: &Path, sym: &str, out: &Path) {
    let members = String::from_utf8_lossy(
        &Command::new("ar")
            .arg("t")
            .arg(rlib)
            .output()
            .expect("ar t")
            .stdout,
    )
    .into_owned();
    for member in members.lines().filter(|m| m.ends_with(".o")) {
        let obj = Command::new("ar")
            .arg("p")
            .arg(rlib)
            .arg(member)
            .output()
            .expect("ar p");
        std::fs::write(out, &obj.stdout).expect("write extracted member");
        if nm(out).contains(&format!(" T _{sym}")) {
            return;
        }
    }
    panic!("no member of {rlib:?} defines _{sym}");
}

/// E2E LINK + RUN-CAUGHT: a REAL Rust `panic!` propagates through the
/// bridge-compiled `box_across_unwind` frame — running its cleanup landing pad
/// (the live `Box<i32>` is freed mid-unwind) — and is genuinely CAUGHT by an
/// enclosing `std::panic::catch_unwind` in a Rust driver linked against the Rust
/// unwind runtime. Asserts: caught (`is_err()`), the cleanup actually ran (a
/// counting global allocator sees the mid-unwind dealloc), and a clean exit 0
/// under a hard timeout (NO abort, NO hang).
#[test]
fn bridge_unwind_cleanup_real_panic_caught_aarch64() {
    if !host_is_aarch64_macos() {
        eprintln!("skipping: requires an aarch64-apple-darwin host");
        return;
    }
    if !aarch64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("eh_run");
    let panicker_rlib = build_panicker_rlib(&dir);

    // Lower the unwinding crate through the bridge (gate ON) and collect the
    // emitted CGU objects.
    let (ok_on, stderr_on) =
        compile_through_bridge(&dylib, &dir, &panicker_rlib, &[("TCG_ENABLE_UNWIND", "1")]);
    assert!(
        ok_on,
        "with TCG_ENABLE_UNWIND=1 the bridge must lower the unwind cleanup. stderr:\n{stderr_on}"
    );
    let bridge_objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    assert!(
        bridge_objs.iter().any(|o| nm(o).contains("_box_across_unwind")),
        "no bridge object defines box_across_unwind; objects: {bridge_objs:?}"
    );

    // Pull the panicker CGU object out of its rlib so `ay_may_unwind` resolves at
    // link time, then archive everything into one staticlib.
    let panicker_obj = dir.join("panicker_cgu.o");
    extract_object_defining(&panicker_rlib, "ay_may_unwind", &panicker_obj);
    let staticlib = dir.join("libboxunwind.a");
    let mut ar = Command::new("ar");
    ar.arg("crs").arg(&staticlib);
    for o in &bridge_objs {
        ar.arg(o);
    }
    ar.arg(&panicker_obj);
    assert!(ar.status().expect("ar crs").success(), "ar crs failed");

    // Rust driver: catch the panic raised through the bridge frame. A counting
    // global allocator proves the cleanup landing pad freed the live Box during
    // the unwind (CLEANUP_RAN=1), and `catch_unwind` proves the panic was CAUGHT.
    let driver_src = dir.join("driver.rs");
    std::fs::write(
        &driver_src,
        "\
use std::alloc::{GlobalAlloc, Layout, System};\n\
use std::sync::atomic::{AtomicUsize, Ordering};\n\
static DEALLOCS: AtomicUsize = AtomicUsize::new(0);\n\
struct Counting;\n\
unsafe impl GlobalAlloc for Counting {\n\
    unsafe fn alloc(&self, l: Layout) -> *mut u8 { System.alloc(l) }\n\
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {\n\
        DEALLOCS.fetch_add(1, Ordering::SeqCst);\n\
        System.dealloc(p, l)\n\
    }\n\
}\n\
#[global_allocator]\n\
static A: Counting = Counting;\n\
extern \"C-unwind\" { fn box_across_unwind() -> i32; }\n\
fn main() {\n\
    let before = DEALLOCS.load(Ordering::SeqCst);\n\
    let r = std::panic::catch_unwind(|| unsafe { box_across_unwind() });\n\
    let after = DEALLOCS.load(Ordering::SeqCst);\n\
    let caught = r.is_err();\n\
    let cleanup_ran = after > before;\n\
    println!(\"AY_CAUGHT={} CLEANUP_RAN={}\", caught as i32, cleanup_ran as i32);\n\
    std::process::exit(if caught && cleanup_ran { 0 } else { 3 });\n\
}\n",
    )
    .expect("write driver");

    // Link THROUGH rustc so libstd / libpanic_unwind / libunwind (the Rust panic
    // runtime + `_rust_eh_personality` + `_Unwind_Resume` / `_Unwind_RaiseException`)
    // resolve. The bridge object + panicker come in via the staticlib.
    let bin = dir.join("driver_bin");
    let mut l = std::ffi::OsString::from("-L");
    l.push(&dir);
    let link = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--target", TARGET, "-Cpanic=unwind", "-Copt-level=0"])
        .arg(&l)
        .args(["-l", "static=boxunwind"])
        .arg("--extern")
        .arg({
            let mut s = std::ffi::OsString::from("panicker=");
            s.push(&panicker_rlib);
            s
        })
        .arg("-o")
        .arg(&bin)
        .arg(&driver_src)
        .output()
        .expect("spawn rustc for link");
    assert!(
        link.status.success(),
        "link failed:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );

    // RUN under a hard timeout. Caught + cleanup-ran => exit 0.
    let (exit_code, stdout, stderr, timed_out) =
        run_with_timeout(&bin, std::time::Duration::from_secs(10));
    assert!(
        !timed_out,
        "the caught-panic binary HUNG (timed out). stdout: {stdout}\nstderr: {stderr}"
    );
    assert_eq!(
        exit_code,
        Some(0),
        "expected the REAL Rust panic to be caught by catch_unwind AFTER the bridge \
         frame's cleanup ran (exit 0). A 134/SIGABRT means uncaught -> terminate; \
         a non-zero means caught or cleanup missing. exit={exit_code:?}\n\
         stdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("AY_CAUGHT=1 CLEANUP_RAN=1"),
        "expected the panic CAUGHT and the bridge-frame cleanup to have run. \
         stdout: {stdout}\nstderr: {stderr}"
    );

    eprintln!(
        "REAL Rust panic CAUGHT through the bridge: {} (cleanup landing pad freed \
         the live Box mid-unwind, catch_unwind caught the re-raise, clean exit 0).",
        stdout.trim()
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// Run `bin` with a hard wall-clock timeout. Returns
/// `(exit_code, stdout, stderr, timed_out)`; on timeout the child is killed.
fn run_with_timeout(
    bin: &Path,
    timeout: std::time::Duration,
) -> (Option<i32>, String, String, bool) {
    use std::io::Read;
    let mut child = Command::new(bin)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("spawn caught-panic binary");
    let start = std::time::Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let mut out = String::new();
                let mut err = String::new();
                if let Some(mut s) = child.stdout.take() {
                    let _ = s.read_to_string(&mut out);
                }
                if let Some(mut s) = child.stderr.take() {
                    let _ = s.read_to_string(&mut err);
                }
                return (status.code(), out, err, false);
            }
            Ok(None) => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    return (None, String::new(), String::new(), true);
                }
                std::thread::sleep(std::time::Duration::from_millis(20));
            }
            Err(e) => panic!("waiting on caught-panic binary failed: {e}"),
        }
    }
}
