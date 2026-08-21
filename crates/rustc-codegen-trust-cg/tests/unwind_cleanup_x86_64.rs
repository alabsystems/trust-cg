#[path = "support/target_dir.rs"]
mod target_dir_support;

// E2E (x86_64-apple-darwin): the bridge lowers rustc MIR `UnwindAction::Cleanup`
// edges to trust-ir exception handling — `Inst::Invoke` (a call that may unwind),
// a cleanup `Inst::LandingPad`, a user `impl Drop` (drop-glue Slice 1) that runs
// during unwind, and `Inst::Resume` (`_Unwind_Resume`) — with the Rust EH
// personality `_rust_eh_personality`, on x86-64. [EH flip Slice C]
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ----------------------------------------------------------------------------
// WHAT THIS PINS — the x86 analog of `unwind_cleanup_aarch64`, and the
// PROOF-OF-FLIP for `TCG_ENABLE_UNWIND` (now default ON; `TCG_DISABLE_UNWIND`
// opts out)
// ----------------------------------------------------------------------------
// A REAL `.rs` function — a user-`Drop` `Guard` held live across a call that can
// unwind — compiled THROUGH THE BRIDGE under `-Cpanic=unwind`. Its MIR carries a
// genuine `UnwindAction::Cleanup(bb)` edge on the throwing call, a `(cleanup)`
// block that drops the `Guard` (whose `Drop` bumps a `static mut` counter — an
// observable side channel) and re-raises (`resume`). The bridge lowers that into
// an `Inst::Invoke`, a cleanup `Inst::LandingPad`, the user Drop glue, an
// `Inst::Resume` (`_Unwind_Resume`), and the Rust personality
// `_rust_eh_personality` — verified by OBJECT INSPECTION.
//
// The demo holds a user `impl Drop` `Guard` (drop-glue Slice 1: user Drop with
// Copy fields, the x86-lowerable shape proven by `m133_x86_user_drop_x86`), NOT
// a `Box`/`Vec`/`String` — the x86 backend fails closed on the alloc/`NonNull`
// heap drop glue, so a heap side channel is not available on x86 today. The drop
// counter uses a `static mut` RMW (NOT atomics — the backend fails closed on the
// atomic intrinsics).
//
// ----------------------------------------------------------------------------
// LINK + RUN-CAUGHT (a REAL Rust panic genuinely caught through the bridge) +
// DIRECT DIFFERENTIAL vs the all-LLVM binary of the same source
// ----------------------------------------------------------------------------
// `bridge_unwind_cleanup_real_panic_caught_x86_64` links the bridge-compiled
// object against the Rust unwind runtime (libstd / libpanic_unwind / libunwind,
// via linking through `rustc`) and RUNS it: a Rust `panic!` raised by
// `ay_may_unwind` (in the `panicker` rlib, normal toolchain) propagates THROUGH
// the bridge-compiled `guard_across_unwind` frame — whose cleanup landing pad
// runs the `Guard`'s `Drop` mid-unwind (bumping the counter) — and is CAUGHT by
// an enclosing `std::panic::catch_unwind` in the driver (the catch stays on the
// LLVM/rustc side — the split model). Asserts caught + the Drop ran mid-unwind +
// clean exit 0 under a hard timeout, AND that the bridge binary's stdout + exit
// code MATCH the all-LLVM binary of the identical source (a DIRECT tcg-vs-LLVM
// differential — the host is x86_64, so both run natively; NOT `bench.sh`, which
// reports phantom SIGILL/abort on unwind programs).
//
// A Rust panic can ONLY be caught by Rust's `catch_unwind` (the panic runtime
// fails closed if a non-Rust frame tries), so the catch driver is Rust — correct
// Rust ABI, not a bridge defect.
//
// The OPT-OUT path is asserted too: with `TCG_DISABLE_UNWIND` set the same crate
// fails closed with the precise `...with cleanup unwind` diagnostic (never
// miscompiles, never silently aborts).

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

fn host_is_x86_64_macos() -> bool {
    cfg!(all(target_os = "macos", target_arch = "x86_64"))
}

fn x86_64_std_available() -> bool {
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
    let dir = std::env::temp_dir().join(format!("rcl2_unwind_x64_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// The unwinding crate: `guard_across_unwind` holds a user-`Drop` `Guard` live
/// across a call to `ay_may_unwind` (an external `extern "C-unwind"` fn that can
/// unwind). On the unwind path the `Guard`'s `Drop` runs (bumping a `static mut`
/// counter — the observable side channel) and the exception is re-raised. The
/// external callee is declared via a cross-crate dependency (the `panicker`
/// rlib) rather than a foreign `extern { }` block — the bridge ICEs on foreign
/// blocks (a pre-existing, unrelated `check_match` interaction), so the
/// cross-crate path is the supported way to reference an external unwinding
/// callee. `guard_drops` is a `static mut` accessor the (LLVM) driver reads to
/// confirm the mid-unwind Drop ran.
const UNWIND_CRATE: &str = "\
#![crate_type = \"staticlib\"]\n\
extern crate panicker;\n\
static mut DROPS: i32 = 0;\n\
#[inline(never)]\n\
fn bump(x: i32) { unsafe { DROPS += x; } }\n\
struct Guard { n: i32 }\n\
impl Drop for Guard {\n\
    fn drop(&mut self) { bump(self.n); }\n\
}\n\
#[no_mangle]\n\
pub extern \"C-unwind\" fn guard_across_unwind() -> i32 {\n\
    let _g = Guard { n: 5 };\n\
    panicker::ay_may_unwind()\n\
}\n\
#[no_mangle]\n\
pub extern \"C\" fn guard_drops() -> i32 { unsafe { DROPS } }\n";

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

/// Compile `UNWIND_CRATE` through the bridge (when `dylib` is `Some`) or through
/// plain rustc/LLVM (when `None`, the differential ORACLE), with `extra_env`
/// overlaid, into `dir/out_name`. Returns `(rustc_succeeded, stderr)`.
fn compile_unwind_crate(
    dylib: Option<&Path>,
    dir: &Path,
    panicker_rlib: &Path,
    out_name: &str,
    extra_env: &[(&str, &str)],
) -> (bool, String) {
    let src = dir.join("guard_unwind.rs");
    std::fs::write(&src, UNWIND_CRATE).expect("write source");
    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "staticlib"]);
    if let Some(dylib) = dylib {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(dylib);
        cmd.arg(&s).env("TCG_NO_PROOF_CERTS", "1");
    }
    cmd.args(["--target", TARGET, "-Cpanic=unwind", "-Copt-level=0"])
        .args(["-Cforce-unwind-tables=yes"])
        // One CGU so the named `-o` object is self-contained (defines
        // guard_across_unwind + its Drop glue + the counter), and the bridge and
        // LLVM objects in the shared dir don't split across files.
        .args(["-Ccodegen-units=1"])
        .arg("--extern")
        .arg({
            let mut s = std::ffi::OsString::from("panicker=");
            s.push(panicker_rlib);
            s
        })
        .arg("--emit=obj")
        .arg("-o")
        .arg(dir.join(out_name))
        .arg(&src);
    for (k, v) in extra_env {
        cmd.env(k, v);
    }
    let out = cmd.output().expect("spawn rustc via rustup");
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

#[test]
fn bridge_lowers_unwind_cleanup_to_eh_object_x86_64() {
    if !host_is_x86_64_macos() {
        eprintln!("skipping: requires an x86_64-apple-darwin host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("eh");
    let panicker_rlib = build_panicker_rlib(&dir);

    // FIRST confirm the MIR actually carries `UnwindAction::Cleanup` (NOT a
    // `panic=abort` build): dump the bridge crate's MIR with the normal compiler.
    let src = dir.join("guard_unwind.rs");
    std::fs::write(&src, UNWIND_CRATE).expect("write source");
    let mir_out = dir.join("guard_unwind.mir");
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

    // 1. OPT-OUT (TCG_DISABLE_UNWIND): the unwinding crate must FAIL CLOSED with
    //    the precise diagnostic — never miscompile, never abort at runtime.
    let (ok_off, stderr_off) = compile_unwind_crate(
        Some(&dylib),
        &dir,
        &panicker_rlib,
        "guard_unwind.o",
        &[("TCG_DISABLE_UNWIND", "1")],
    );
    assert!(
        !ok_off,
        "with TCG_DISABLE_UNWIND set the unwinding crate must fail closed, but it compiled"
    );
    assert!(
        stderr_off.contains("cleanup unwind"),
        "expected the fail-closed `...with cleanup unwind` diagnostic; got:\n{stderr_off}"
    );

    // 2. DEFAULT (gate ON by the flip): the bridge lowers the unwind edges and
    //    emits the EH object — no env var needed.
    let _ = std::fs::remove_file(dir.join("guard_unwind.o"));
    let (ok_on, stderr_on) =
        compile_unwind_crate(Some(&dylib), &dir, &panicker_rlib, "guard_unwind.o", &[]);
    assert!(
        ok_on,
        "with the flip ON by default the bridge must lower the unwind cleanup. stderr:\n{stderr_on}"
    );

    let objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    let eh_obj = objs
        .iter()
        .find(|o| nm(o).contains("_guard_across_unwind"))
        .unwrap_or_else(|| panic!("no object defines guard_across_unwind; objects: {objs:?}"));

    assert!(
        has_gcc_except_tab(eh_obj),
        "the lowered object must carry the LSDA (__gcc_except_tab) — the cleanup \
         landing-pad call-site table"
    );
    let syms = nm(eh_obj);
    assert!(
        syms.contains("_rust_eh_personality"),
        "the lowered object must reference the RUST personality `_rust_eh_personality` \
         (not the C++ default, and not the undefined `___rust_eh_personality`). nm:\n{syms}"
    );
    assert!(
        !syms.contains("___rust_eh_personality"),
        "the lowered object must NOT reference the undefined `___rust_eh_personality` \
         (the double-prefix link failure Slice A removes). nm:\n{syms}"
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
        "bridge unwind-cleanup EH lowering VERIFIED (object level, x86-64): Invoke + \
         cleanup LandingPad + user Drop glue + Resume + _rust_eh_personality + \
         __gcc_except_tab. The link+run-CAUGHT proof lives in \
         `bridge_unwind_cleanup_real_panic_caught_x86_64`."
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
/// resolve `ay_may_unwind`.
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

const DRIVER_SRC: &str = "\
extern \"C-unwind\" { fn guard_across_unwind() -> i32; }\n\
extern \"C\" { fn guard_drops() -> i32; }\n\
fn main() {\n\
    let before = unsafe { guard_drops() };\n\
    let r = std::panic::catch_unwind(|| unsafe { guard_across_unwind() });\n\
    let after = unsafe { guard_drops() };\n\
    let caught = r.is_err();\n\
    let cleanup_ran = after > before;\n\
    println!(\"AY_CAUGHT={} CLEANUP_RAN={}\", caught as i32, cleanup_ran as i32);\n\
    std::process::exit(if caught && cleanup_ran { 0 } else { 3 });\n\
}\n";

/// Collect the objects rustc emitted for a `--emit=obj -o <stem>.o` compile.
/// rustc names them `<stem>.<cgu>.rcgu.o` (a main CGU, the `DROPS` static, and an
/// allocator shim), never the literal `<stem>.o`. Return the code-bearing ones
/// (skip the allocator shim — the Guard demo does not allocate, and the driver
/// binary supplies its own allocator).
fn collect_bridge_objects(dir: &Path, stem: &str) -> Vec<PathBuf> {
    let prefix = format!("{stem}.");
    let objs: Vec<PathBuf> = std::fs::read_dir(dir)
        .expect("read dir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| {
            p.extension().is_some_and(|x| x == "o")
                && p.file_name()
                    .and_then(|n| n.to_str())
                    .is_some_and(|n| n.starts_with(&prefix) && !n.contains("allocator_shim"))
        })
        .collect();
    assert!(
        objs.iter().any(|o| nm(o).contains("_guard_across_unwind")),
        "no `{stem}.*` object defines guard_across_unwind; found: {objs:?}"
    );
    objs
}

/// Archive the compile's code objects (defining `guard_across_unwind`) + the
/// panicker CGU into `dir/lib<name>.a`, then link `DRIVER_SRC` through rustc
/// against the Rust unwind runtime and return the binary path.
fn link_driver_binary(
    dir: &Path,
    panicker_rlib: &Path,
    obj_stem: &str,
    staticlib_name: &str,
    bin_name: &str,
) -> PathBuf {
    let unwind_objs = collect_bridge_objects(dir, obj_stem);
    let panicker_obj = dir.join(format!("panicker_cgu_{staticlib_name}.o"));
    extract_object_defining(panicker_rlib, "ay_may_unwind", &panicker_obj);
    let staticlib = dir.join(format!("lib{staticlib_name}.a"));
    let _ = std::fs::remove_file(&staticlib);
    let mut ar = Command::new("ar");
    ar.arg("crs").arg(&staticlib);
    for o in &unwind_objs {
        ar.arg(o);
    }
    ar.arg(&panicker_obj);
    assert!(ar.status().expect("ar crs").success(), "ar crs failed");

    let driver_src = dir.join(format!("driver_{staticlib_name}.rs"));
    std::fs::write(&driver_src, DRIVER_SRC).expect("write driver");

    let bin = dir.join(bin_name);
    let mut l = std::ffi::OsString::from("-L");
    l.push(dir);
    let link = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--target", TARGET, "-Cpanic=unwind", "-Copt-level=0"])
        .arg(&l)
        .args(["-l", &format!("static={staticlib_name}")])
        .arg("--extern")
        .arg({
            let mut s = std::ffi::OsString::from("panicker=");
            s.push(panicker_rlib);
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
    bin
}

/// E2E LINK + RUN-CAUGHT + DIFFERENTIAL: a REAL Rust `panic!` propagates through
/// the bridge-compiled `guard_across_unwind` frame — running its cleanup landing
/// pad (the `Guard`'s `Drop` bumps the counter mid-unwind) — and is genuinely
/// CAUGHT by an enclosing `std::panic::catch_unwind` in a Rust driver linked
/// against the Rust unwind runtime. Asserts caught + Drop-ran + clean exit 0
/// under a hard timeout, AND that the bridge binary matches the all-LLVM binary
/// of the same source (direct differential; both run natively on the x86_64 host).
#[test]
fn bridge_unwind_cleanup_real_panic_caught_x86_64() {
    if !host_is_x86_64_macos() {
        eprintln!("skipping: requires an x86_64-apple-darwin host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("eh_run");
    let panicker_rlib = build_panicker_rlib(&dir);

    // (a) Bridge-compiled guard_across_unwind (gate ON by default).
    let (ok_on, stderr_on) =
        compile_unwind_crate(Some(&dylib), &dir, &panicker_rlib, "guard_unwind_tcg.o", &[]);
    assert!(
        ok_on,
        "with the flip ON by default the bridge must lower the unwind cleanup. stderr:\n{stderr_on}"
    );
    let tcg_bin =
        link_driver_binary(&dir, &panicker_rlib, "guard_unwind_tcg", "guardunwindtcg", "driver_tcg");

    // (b) All-LLVM guard_across_unwind (the differential ORACLE): identical
    //     source, plain rustc/LLVM, same driver + link.
    let (ok_llvm, stderr_llvm) =
        compile_unwind_crate(None, &dir, &panicker_rlib, "guard_unwind_llvm.o", &[]);
    assert!(
        ok_llvm,
        "the all-LLVM oracle must compile the unwind cleanup. stderr:\n{stderr_llvm}"
    );
    let llvm_bin = link_driver_binary(
        &dir,
        &panicker_rlib,
        "guard_unwind_llvm",
        "guardunwindllvm",
        "driver_llvm",
    );

    // RUN both natively under a hard timeout. Caught + Drop-ran => exit 0.
    let (tcg_exit, tcg_out, tcg_err, tcg_hung) =
        run_with_timeout(&tcg_bin, std::time::Duration::from_secs(20));
    let (llvm_exit, llvm_out, llvm_err, llvm_hung) =
        run_with_timeout(&llvm_bin, std::time::Duration::from_secs(20));

    assert!(
        !tcg_hung,
        "the bridge caught-panic binary HUNG (timed out). stdout: {tcg_out}\nstderr: {tcg_err}"
    );
    assert!(
        !llvm_hung,
        "the LLVM oracle binary HUNG (timed out). stdout: {llvm_out}\nstderr: {llvm_err}"
    );
    assert_eq!(
        tcg_exit,
        Some(0),
        "expected the REAL Rust panic to be caught by catch_unwind AFTER the bridge \
         frame's Drop ran mid-unwind (exit 0). A 134/SIGABRT means uncaught -> terminate. \
         exit={tcg_exit:?}\nstdout: {tcg_out}\nstderr: {tcg_err}"
    );
    assert!(
        tcg_out.contains("AY_CAUGHT=1 CLEANUP_RAN=1"),
        "expected the panic CAUGHT and the bridge-frame Drop to have run mid-unwind. \
         stdout: {tcg_out}\nstderr: {tcg_err}"
    );

    // DIRECT DIFFERENTIAL: the bridge binary must match the all-LLVM binary.
    assert_eq!(
        tcg_exit, llvm_exit,
        "bridge exit {tcg_exit:?} != LLVM oracle exit {llvm_exit:?} \
         (tcg stdout: {tcg_out}; llvm stdout: {llvm_out})"
    );
    assert_eq!(
        tcg_out.trim(),
        llvm_out.trim(),
        "bridge stdout != LLVM oracle stdout"
    );

    eprintln!(
        "REAL Rust panic CAUGHT through the bridge (x86-64): {} — cleanup landing pad \
         ran the Guard's Drop mid-unwind, catch_unwind caught the re-raise, clean exit 0, \
         MATCHES the all-LLVM binary ({}).",
        tcg_out.trim(),
        llvm_out.trim()
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

const ABORT_CLEANUP_SUCCESS: &str = r#"
#[inline(never)]
fn unwrap_with_live_drop(value: Option<i32>) -> i32 {
    let live = String::from("hello");
    let unwrapped = value.unwrap();
    unwrapped + live.len() as i32
}

fn main() {
    let value = std::hint::black_box(Some(37));
    std::process::exit(unwrap_with_live_drop(value));
}
"#;

const ABORT_CLEANUP_PANIC: &str = r#"
#[inline(never)]
fn unwrap_with_live_drop(value: Option<i32>) -> i32 {
    let live = String::from("hello");
    let unwrapped = value.unwrap();
    unwrapped + live.len() as i32
}

fn main() {
    let value = std::hint::black_box(None::<i32>);
    let _ = unwrap_with_live_drop(value);
}
"#;

fn compile_abort_cleanup_program(
    dir: &Path,
    name: &str,
    src: &str,
    dylib: Option<&Path>,
) -> (PathBuf, String) {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write panic=abort cleanup source");
    let bin = dir.join(name);
    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--target", TARGET, "-Cpanic=abort", "-Copt-level=0"]);
    if let Some(dylib) = dylib {
        let mut backend = std::ffi::OsString::from("-Zcodegen-backend=");
        backend.push(dylib);
        cmd.arg(backend);
    }
    let output = cmd.arg("-o").arg(&bin).arg(&src_path).output().expect("spawn rustc");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        output.status.success(),
        "{name} must compile with {} at panic=abort; stderr:\n{stderr}",
        if dylib.is_some() { "trust-cg" } else { "LLVM" }
    );
    (bin, stderr)
}

/// Panic=abort makes every cleanup unwind edge dead, but only the panic path is
/// dead. Pin both sides of the contract: a live-Drop `Some` path returns its real
/// value, while the corresponding `None` path aborts just like LLVM. A regression
/// to the old cleanup-edge fail-closed behavior is a compile failure here.
#[test]
fn abort_strategy_cleanup_edges_compile_and_match_llvm_x86_64() {
    if !host_is_x86_64_macos() {
        eprintln!("skipping: requires an x86_64-apple-darwin host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("abort_cleanup");

    let (llvm_ok, _) =
        compile_abort_cleanup_program(&dir, "abort_cleanup_ok_llvm", ABORT_CLEANUP_SUCCESS, None);
    let (tcg_ok, _) = compile_abort_cleanup_program(
        &dir,
        "abort_cleanup_ok_tcg",
        ABORT_CLEANUP_SUCCESS,
        Some(&dylib),
    );
    let llvm_ok_run = run_with_timeout(&llvm_ok, std::time::Duration::from_secs(10));
    let tcg_ok_run = run_with_timeout(&tcg_ok, std::time::Duration::from_secs(10));
    assert_eq!(llvm_ok_run.0, Some(42), "LLVM readable oracle changed: {llvm_ok_run:?}");
    assert_eq!(tcg_ok_run.0, llvm_ok_run.0, "trust-cg live path differs: {tcg_ok_run:?}");
    assert!(!tcg_ok_run.3, "trust-cg live path hung");

    let (llvm_panic, _) =
        compile_abort_cleanup_program(&dir, "abort_cleanup_panic_llvm", ABORT_CLEANUP_PANIC, None);
    let (tcg_panic, _) = compile_abort_cleanup_program(
        &dir,
        "abort_cleanup_panic_tcg",
        ABORT_CLEANUP_PANIC,
        Some(&dylib),
    );
    let llvm_panic_run = run_with_timeout(&llvm_panic, std::time::Duration::from_secs(10));
    let tcg_panic_run = run_with_timeout(&tcg_panic, std::time::Duration::from_secs(10));
    assert!(!llvm_panic_run.3 && !tcg_panic_run.3, "panic path hung");
    assert_eq!(llvm_panic_run.0, None, "LLVM panic=abort path did not signal");
    assert_eq!(tcg_panic_run.0, None, "trust-cg panic=abort path did not signal");

    let _ = std::fs::remove_dir_all(&dir);
}
