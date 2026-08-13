// E2E (x86_64-apple-darwin): HEAP `Drop` across an EH cleanup/unwind path.
// A `Box` held live across a may-unwind (panicking) call is FREED by the cleanup
// landing pad MID-UNWIND, through the SAME `__rust_dealloc` interception the
// normal-return drop uses (`lower_box_drop`/`lower_vec_drop` -> `vec_dealloc_callee`,
// I64 size/align from rustc's own layout, the box/vec SCALAR pointer — NEVER a
// `NonNull<[u8]>` fat-ptr or an `AlignmentEnum` niche). [dealloc Slice 1]
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ----------------------------------------------------------------------------
// WHAT THIS PINS — heap Drop-across-unwind BEYOND the stack `Guard` that
// `unwind_cleanup_x86_64` proves (which uses a stack `Guard` precisely because
// heap drop-across-unwind used to fail closed on x86).
// ----------------------------------------------------------------------------
// The EH-cleanup-path Box/Vec/String drop reaches the EXISTING (already-correct,
// normal-return) dealloc interception: `lower_drop_terminator`'s `eh_active`
// bypass admits a `Box`/`Vec`/`String` drop terminator sitting in a `(cleanup)`
// landing pad, the collection's `{ptr}`/`{ptr,cap,len}` scalar binding threads
// into the pad through the `Cleanup` CFG edge, and the drop lowers to a NOUNWIND
// `__rust_dealloc(ptr, size, align)`. rustc's mono collector pulls in the real
// (unlowerable) `drop_in_place::<Box<T>>` / `box_new_uninit` / `Global::deallocate`
// / `<Box<T> as Drop>::drop` bodies from the ORIGINAL MIR; the bridge never emits
// a call to any of them (interception replaces every site), so they are trapped as
// dead `Unreachable` stubs (`is_dead_intercepted_heap_alloc_glue`) — exactly the
// discipline the dead-iterator bodies follow — instead of failing the library
// crate closed.
//
// ----------------------------------------------------------------------------
// PARAMOUNT INVARIANT — a mis-lowered drop MUST fail closed, NEVER
// double-free/leak/use-after-free.
// ----------------------------------------------------------------------------
// A COUNTING `#[global_allocator]` (driver / LLVM side — atomics are fine there;
// the bridge-compiled frame never touches the counter) tracks a DISTINCTIVELY
// SIZED heap value (`Box<[i64; 512]>` = 4096 bytes, isolated from all std noise):
//   * `TARGET_ALLOCS == 1`  — the box allocated exactly once;
//   * `TARGET_DEALLOCS == 1` — freed EXACTLY once (a double-free would push it to
//     2; a leak would leave it 0) — and, for the EH demo, freed DURING the unwind;
//   * identical to the all-LLVM binary of the identical source (a DIRECT
//     tcg-vs-LLVM binary differential — the host is x86_64, both run natively;
//     NOT `bench.sh`, which reports phantom SIGILL/abort on heap+unwind programs).
//
// The negative sweep asserts the risky surface STAYS fail-closed: a struct-with-Vec
// field / enum-variant Box / projected Box / `Vec<Box>` drop is a COMPILE Err
// (clean), never a wrong dealloc, never a runtime ud2/SIGILL/abort.

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
    assert!(status.success(), "cargo build failed; cannot run heap-drop test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m135_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn nm(obj: &Path) -> String {
    String::from_utf8_lossy(&Command::new("nm").arg(obj).output().expect("nm").stdout).into_owned()
}

/// The external unwinding callee `ay_may_unwind` (compiled by the NORMAL toolchain
/// so it genuinely panics / unwinds). Referenced cross-crate (the bridge ICEs on
/// foreign `extern { }` blocks — a pre-existing, unrelated interaction).
const PANICKER_CRATE: &str = "\
#![crate_type = \"rlib\"]\n\
#[no_mangle]\n\
pub extern \"C-unwind\" fn ay_may_unwind() -> i64 { panic!(\"boom from panicker\"); }\n";

/// The bridge-compiled unwinding crate: `box_across_unwind` holds a DISTINCTIVELY
/// SIZED `Box<[i64; 512]>` (4096 bytes) live across a call to `ay_may_unwind`. On
/// the unwind path the cleanup landing pad FREES the box (its `__rust_dealloc`
/// interception) mid-unwind and the exception re-raises. The counting allocator in
/// the driver observes exactly one alloc + one free of the 4096-byte block.
const UNWIND_CRATE: &str = "\
#![crate_type = \"staticlib\"]\n\
extern crate panicker;\n\
#[no_mangle]\n\
pub extern \"C-unwind\" fn box_across_unwind() -> i64 {\n\
    let b: Box<[i64; 512]> = Box::new([7i64; 512]);\n\
    panicker::ay_may_unwind();\n\
    b[0]\n\
}\n";

/// The normal-return floor (STEP 0 regression baseline): the SAME distinctively
/// sized `Box<[i64; 512]>` constructed and dropped on a NORMAL return (no unwind).
const FLOOR_CRATE: &str = "\
#![crate_type = \"staticlib\"]\n\
#[no_mangle]\n\
pub extern \"C\" fn floor_box() -> i64 {\n\
    let b: Box<[i64; 512]> = Box::new([3i64; 512]);\n\
    b[0]\n\
}\n";

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

/// Extract the single member of `rlib` whose `nm` defines `_<sym>` to `out`.
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

/// Compile `src` to an object at `dir/<stem>.o` (rustc actually names the CGUs
/// `<stem>.<cgu>.rcgu.o`), through the bridge when `dylib` is `Some`, else plain
/// LLVM. Returns `(compiled_ok, stderr)`.
fn compile_staticlib(
    dylib: Option<&Path>,
    dir: &Path,
    src_body: &str,
    src_name: &str,
    out_stem: &str,
    opt: &str,
    panic: &str,
    panicker_rlib: Option<&Path>,
) -> (bool, String) {
    let src = dir.join(src_name);
    std::fs::write(&src, src_body).expect("write source");
    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "staticlib"]);
    if let Some(dylib) = dylib {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(dylib);
        cmd.arg(&s).env("TCG_NO_PROOF_CERTS", "1");
    }
    cmd.args(["--target", TARGET])
        .arg(format!("-Cpanic={panic}"))
        .arg(format!("-Copt-level={opt}"))
        .args(["-Cforce-unwind-tables=yes", "-Ccodegen-units=1"]);
    if let Some(rlib) = panicker_rlib {
        cmd.arg("--extern").arg({
            let mut s = std::ffi::OsString::from("panicker=");
            s.push(rlib);
            s
        });
    }
    cmd.arg("--emit=obj")
        .arg("-o")
        .arg(dir.join(format!("{out_stem}.o")))
        .arg(&src);
    let out = cmd.output().expect("spawn rustc via rustup");
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

/// The `<stem>.*` object that DEFINES symbol `_<def>` (the real code object; the
/// dead trapped-glue stubs and the allocator shim are skipped). `nm`-based so it
/// works at both O0 (per-CGU objects) and O3 (an inlined single CGU).
fn object_defining(dir: &Path, stem: &str, def: &str) -> PathBuf {
    let prefix = format!("{stem}.");
    for entry in std::fs::read_dir(dir).expect("read dir").flatten() {
        let p = entry.path();
        if p.extension().is_some_and(|x| x == "o")
            && p.file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n == format!("{stem}.o") || n.starts_with(&prefix))
            && nm(&p).contains(&format!(" T _{def}"))
        {
            return p;
        }
    }
    panic!("no `{stem}.*` object defines _{def} in {dir:?}");
}

fn ar_staticlib(dir: &Path, name: &str, objs: &[PathBuf]) -> PathBuf {
    let lib = dir.join(format!("lib{name}.a"));
    let _ = std::fs::remove_file(&lib);
    let mut ar = Command::new("ar");
    ar.arg("crs").arg(&lib);
    for o in objs {
        ar.arg(o);
    }
    assert!(ar.status().expect("ar crs").success(), "ar crs failed");
    lib
}

/// The counting-allocator driver: a `#[global_allocator]` wrapping `System` that
/// isolates a DISTINCTIVELY SIZED (`TARGET`-byte) allocation. It calls `entry`
/// (inside `catch_unwind` when `catches`) and prints the caught flag + the
/// target-size alloc/dealloc counts. Atomics are used only because the driver is
/// LLVM-compiled (the bridge frame never touches them).
fn driver_src(entry: &str, catches: bool) -> String {
    let call = if catches {
        format!(
            "let r = std::panic::catch_unwind(|| unsafe {{ {entry}() }}); let caught = r.is_err() as i32; let v = *r.as_ref().unwrap_or(&0);"
        )
    } else {
        format!("let v = unsafe {{ {entry}() }}; let caught = 1i32;")
    };
    format!(
        "\
use std::alloc::{{GlobalAlloc, Layout, System}};\n\
use std::sync::atomic::{{AtomicUsize, Ordering}};\n\
const TARGET: usize = 4096;\n\
static TA: AtomicUsize = AtomicUsize::new(0);\n\
static TD: AtomicUsize = AtomicUsize::new(0);\n\
struct Counting;\n\
unsafe impl GlobalAlloc for Counting {{\n\
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {{\n\
        let p = System.alloc(l);\n\
        if l.size() == TARGET {{ TA.fetch_add(1, Ordering::SeqCst); }}\n\
        p\n\
    }}\n\
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {{\n\
        if l.size() == TARGET {{ TD.fetch_add(1, Ordering::SeqCst); }}\n\
        System.dealloc(p, l)\n\
    }}\n\
}}\n\
#[global_allocator]\n\
static A: Counting = Counting;\n\
extern \"C-unwind\" {{ fn {entry}() -> i64; }}\n\
fn main() {{\n\
    {call}\n\
    println!(\"CAUGHT={{}} TA={{}} TD={{}} V={{}}\", caught, TA.load(Ordering::SeqCst), TD.load(Ordering::SeqCst), v);\n\
    std::process::exit(0);\n\
}}\n"
    )
}

fn link_driver(
    dir: &Path,
    panicker_rlib: &Path,
    staticlib: &Path,
    staticlib_name: &str,
    driver: &str,
    bin_name: &str,
) -> PathBuf {
    let driver_src_path = dir.join(format!("driver_{bin_name}.rs"));
    std::fs::write(&driver_src_path, driver).expect("write driver");
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
        .arg(&driver_src_path)
        .output()
        .expect("spawn rustc for link");
    assert!(
        link.status.success(),
        "link failed:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let _ = staticlib; // archived via -L/-l above
    bin
}

fn run_with_timeout(
    bin: &Path,
    timeout: std::time::Duration,
) -> (Option<i32>, String, String, bool) {
    use std::io::Read;
    let mut child = Command::new(bin)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("spawn heap-drop binary");
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
            Err(e) => panic!("waiting on heap-drop binary failed: {e}"),
        }
    }
}

/// THE EH DEMO (STEP 2): a distinctively-sized `Box` held live across a real Rust
/// `panic!`, FREED by the bridge frame's cleanup landing pad MID-UNWIND, and the
/// re-raise CAUGHT by an enclosing `std::panic::catch_unwind` in an LLVM driver
/// (the split model). The counting allocator proves the box was allocated once and
/// freed EXACTLY once during the unwind; the bridge binary matches the all-LLVM
/// binary of the identical source.
#[test]
fn bridge_heap_box_drop_across_unwind_freed_once_and_matches_llvm_x86_64() {
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

    // FIRST confirm the MIR carries a real `UnwindAction::Cleanup` edge (NOT a
    // panic=abort build) — otherwise this would not exercise the EH path.
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
        "the test crate's MIR must carry a real UnwindAction::Cleanup edge; MIR:\n{mir}"
    );

    // Build both the bridge and the LLVM frame, link each against the SAME
    // counting-allocator driver, run, and differential.
    let mut results = Vec::new();
    for (label, backend) in [("tcg", Some(dylib.as_path())), ("llvm", None)] {
        let stem = format!("box_unwind_{label}");
        let (ok, stderr) = compile_staticlib(
            backend,
            &dir,
            UNWIND_CRATE,
            &format!("box_unwind_{label}.rs"),
            &stem,
            "0",
            "unwind",
            Some(&panicker_rlib),
        );
        assert!(ok, "[{label}] frame must compile. stderr:\n{stderr}");

        // The dead intercepted-heap-glue stubs are unreferenced by the emitted
        // frame (interception -> direct __rust_alloc/__rust_dealloc), so only the
        // real code object + the panicker CGU are needed to link.
        let frame_obj = object_defining(&dir, &stem, "box_across_unwind");
        let panicker_obj = dir.join(format!("panicker_cgu_{label}.o"));
        extract_object_defining(&panicker_rlib, "ay_may_unwind", &panicker_obj);
        let staticlib_name = format!("boxunwind{label}");
        let staticlib = ar_staticlib(&dir, &staticlib_name, &[frame_obj, panicker_obj]);

        let bin = link_driver(
            &dir,
            &panicker_rlib,
            &staticlib,
            &staticlib_name,
            &driver_src("box_across_unwind", true),
            &format!("driver_{label}"),
        );
        let (exit, out, err, hung) = run_with_timeout(&bin, std::time::Duration::from_secs(20));
        assert!(!hung, "[{label}] heap-drop binary HUNG. stdout:{out}\nstderr:{err}");
        assert_eq!(
            exit,
            Some(0),
            "[{label}] expected clean exit 0 (a double-free would abort via the \
             system allocator). exit={exit:?}\nstdout:{out}\nstderr:{err}"
        );
        results.push((label, out.trim().to_owned()));
    }

    let (tcg_out, llvm_out) = (&results[0].1, &results[1].1);
    // The box (distinctive 4096-byte allocation) was allocated ONCE and freed
    // EXACTLY once — during the unwind — and the panic was caught.
    assert!(
        tcg_out.contains("CAUGHT=1") && tcg_out.contains("TA=1") && tcg_out.contains("TD=1"),
        "[tcg] the box must be allocated once and freed EXACTLY once mid-unwind, \
         and the panic caught. got: {tcg_out}"
    );
    assert_eq!(
        tcg_out, llvm_out,
        "bridge heap-drop-across-unwind output must MATCH the all-LLVM binary \
         (tcg: {tcg_out}; llvm: {llvm_out})"
    );
    eprintln!("HEAP Drop-across-unwind VERIFIED (x86-64): {tcg_out} (freed EXACTLY once mid-unwind, matches all-LLVM)");
    let _ = std::fs::remove_dir_all(&dir);
}

/// THE FLOOR (STEP 0 regression baseline): the SAME distinctively-sized `Box`
/// constructed + dropped on a NORMAL return (no unwind), at O0 AND O3. The box is
/// freed EXACTLY once and the bridge binary matches the all-LLVM binary. This is
/// the interception the EH cleanup path mirrors.
#[test]
fn bridge_heap_box_normal_return_drop_freed_once_matches_llvm_x86_64() {
    if !host_is_x86_64_macos() {
        eprintln!("skipping: requires an x86_64-apple-darwin host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("floor");
    let panicker_rlib = build_panicker_rlib(&dir);

    for opt in ["0", "3"] {
        let mut results = Vec::new();
        for (label, backend) in [("tcg", Some(dylib.as_path())), ("llvm", None)] {
            let stem = format!("floor_{label}_{opt}");
            let (ok, stderr) = compile_staticlib(
                backend,
                &dir,
                FLOOR_CRATE,
                &format!("floor_{label}_{opt}.rs"),
                &stem,
                opt,
                "abort",
                None,
            );
            assert!(ok, "[{label} O{opt}] floor frame must compile. stderr:\n{stderr}");
            let frame_obj = object_defining(&dir, &stem, "floor_box");
            let staticlib_name = format!("floor{label}{opt}");
            let staticlib = ar_staticlib(&dir, &staticlib_name, &[frame_obj]);
            let bin = link_driver(
                &dir,
                &panicker_rlib,
                &staticlib,
                &staticlib_name,
                &driver_src("floor_box", false),
                &format!("floorbin_{label}_{opt}"),
            );
            let (exit, out, err, hung) = run_with_timeout(&bin, std::time::Duration::from_secs(20));
            assert!(!hung, "[{label} O{opt}] floor binary HUNG. stdout:{out}\nstderr:{err}");
            assert_eq!(
                exit,
                Some(0),
                "[{label} O{opt}] expected clean exit 0. exit={exit:?}\nstdout:{out}\nstderr:{err}"
            );
            results.push((label, out.trim().to_owned()));
        }
        let (tcg_out, llvm_out) = (&results[0].1, &results[1].1);
        assert!(
            tcg_out.contains("TA=1") && tcg_out.contains("TD=1"),
            "[tcg O{opt}] the box must be allocated once and freed EXACTLY once on a \
             normal return. got: {tcg_out}"
        );
        assert_eq!(
            tcg_out, llvm_out,
            "[O{opt}] bridge normal-return heap-drop output must MATCH the all-LLVM \
             binary (tcg: {tcg_out}; llvm: {llvm_out})"
        );
        eprintln!("HEAP normal-return floor VERIFIED (x86-64, O{opt}): {tcg_out}");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// THE NEGATIVE SWEEP (STEP 3): the risky surface STAYS fail-closed. A
/// struct-with-Vec-field / enum-variant Box / projected Box / `Vec<Box>` drop must
/// be a COMPILE Err (clean) — never a wrong dealloc, never a runtime ud2/SIGILL/
/// abort. Each is compiled through the bridge under `panic=unwind` (EH active) and
/// asserted to FAIL to compile with a drop/aggregate fail-closed diagnostic.
#[test]
fn bridge_heap_aggregate_and_projected_drops_fail_closed_x86_64() {
    if !host_is_x86_64_macos() {
        eprintln!("skipping: requires an x86_64-apple-darwin host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("neg");
    let panicker_rlib = build_panicker_rlib(&dir);

    let cases: &[(&str, &str)] = &[
        (
            "struct_vec_field",
            "#![crate_type=\"staticlib\"]\n\
             extern crate panicker;\n\
             struct S { v: Vec<i64> }\n\
             #[no_mangle] pub extern \"C-unwind\" fn f() -> i64 {\n\
                 let s = S { v: vec![1i64, 2, 3] };\n\
                 panicker::ay_may_unwind();\n\
                 s.v[0]\n\
             }\n",
        ),
        (
            "enum_variant_box",
            "#![crate_type=\"staticlib\"]\n\
             extern crate panicker;\n\
             enum E { A(Box<i64>), B }\n\
             #[no_mangle] pub extern \"C-unwind\" fn f() -> i64 {\n\
                 let e = E::A(Box::new(9));\n\
                 panicker::ay_may_unwind();\n\
                 match e { E::A(b) => *b, E::B => 0 }\n\
             }\n",
        ),
        (
            "tuple_box",
            "#![crate_type=\"staticlib\"]\n\
             extern crate panicker;\n\
             #[no_mangle] pub extern \"C-unwind\" fn f() -> i64 {\n\
                 let t = (Box::new(1i64), Box::new(2i64));\n\
                 panicker::ay_may_unwind();\n\
                 *t.0 + *t.1\n\
             }\n",
        ),
        (
            "vec_of_box",
            "#![crate_type=\"staticlib\"]\n\
             extern crate panicker;\n\
             #[no_mangle] pub extern \"C-unwind\" fn f() -> i64 {\n\
                 let v: Vec<Box<i64>> = vec![Box::new(1i64)];\n\
                 panicker::ay_may_unwind();\n\
                 *v[0]\n\
             }\n",
        ),
    ];

    for (name, src) in cases {
        let (ok, stderr) = compile_staticlib(
            Some(&dylib),
            &dir,
            src,
            &format!("neg_{name}.rs"),
            &format!("neg_{name}"),
            "0",
            "unwind",
            Some(&panicker_rlib),
        );
        // MUST be a clean COMPILE error (fail closed), NOT a successful compile
        // (which could emit a wrong dealloc) and NOT a runtime crash.
        assert!(
            !ok,
            "[{name}] a projected / aggregate / needs-drop-element heap drop MUST \
             fail closed at compile time, but it compiled (risk of a wrong dealloc)"
        );
        // A CLEAN compile-time fail-closed: the `[TCG-MIR-UNSUPPORTED]` gate fired
        // ("failing closed rather than miscompiling"), never a wrong dealloc, never
        // a runtime crash. (The per-item detail line — e.g. "TerminatorKind::Drop of
        // a projected Box place" / "projected Vec place" / "Drop of type that needs
        // drop" — is the exact reason but is not always captured verbatim when
        // rustc's stderr is piped, so the assertion keys on the gate markers, which
        // are the load-bearing fail-closed evidence.)
        assert!(
            stderr.contains("TCG-MIR-UNSUPPORTED")
                && stderr.contains("failing closed rather than miscompiling"),
            "[{name}] expected the clean [TCG-MIR-UNSUPPORTED] fail-closed gate; got:\n{stderr}"
        );
        eprintln!("[{name}] fail-closed at compile time (no wrong dealloc, no runtime crash) — GOOD");
    }
    let _ = std::fs::remove_dir_all(&dir);
}
