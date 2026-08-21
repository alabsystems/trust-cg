#[path = "support/target_dir.rs"]
mod target_dir_support;

// Runtime oracle for rustc_codegen_trust_cg scalar aggregate, reference, and union
// semantics.
//
// This keeps #782's reference/union evidence tied to an executable produced by
// the backend. Broader reference memory remains outside this oracle; mixed-width
// integer union cases are expected to link/run through the backend.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output, Stdio};
use std::sync::Mutex;
use std::time::{Duration, Instant};

static RUNTIME_ORACLE_LOCK: Mutex<()> = Mutex::new(());

fn dylib_name() -> String {
    format!(
        "{}rustc_codegen_trust_cg{}",
        std::env::consts::DLL_PREFIX,
        std::env::consts::DLL_SUFFIX
    )
}

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
    let dylib_name = dylib_name();
    let candidates = [
        target_dir.join("release").join(&dylib_name),
        target_dir.join("debug").join(&dylib_name),
    ];
    for candidate in &candidates {
        if candidate.exists() {
            return candidate.clone();
        }
    }

    let pinned_cargo_toolchain = format!("+{}", pinned_toolchain());
    let status = Command::new("cargo")
        .arg(pinned_cargo_toolchain)
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(
        status.success(),
        "cargo build failed; cannot run reference-union test"
    );

    let built = target_dir.join("release").join(&dylib_name);
    assert!(
        built.exists(),
        "expected dylib at {:?} but it was not produced",
        built
    );
    built
}

fn write_temp_source(stem: &str, contents: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!("rcl2_{}_{}.rs", stem, std::process::id()));
    std::fs::write(&path, contents).expect("failed to write temp source file");
    path
}

fn temp_artifact_path(stem: &str, suffix: &str) -> PathBuf {
    std::env::temp_dir().join(format!("rcl2_{stem}_{}_{}", std::process::id(), suffix))
}

struct BackendCompile {
    status: ExitStatus,
    stdout: String,
    stderr: String,
    out_bin: PathBuf,
}

fn compile_backend_source(stem: &str, src: &str) -> BackendCompile {
    let out_bin = temp_artifact_path(stem, "out");
    compile_backend_source_to(stem, src, out_bin, &[])
}

fn compile_backend_source_to(
    stem: &str,
    src: &str,
    out_bin: PathBuf,
    extra_args: &[OsString],
) -> BackendCompile {
    let src_path = write_temp_source(stem, src);
    let dylib = ensure_dylib_built();

    let backend_arg = {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(&dylib);
        s
    };
    let toolchain = pinned_toolchain();
    let output = Command::new("rustup")
        .args(["run", toolchain.as_str(), "rustc", "--edition=2021"])
        .arg(&backend_arg)
        .args(extra_args)
        .arg("-o")
        .arg(&out_bin)
        .arg(&src_path)
        .output()
        .expect("failed to spawn rustc via rustup");

    let _ = std::fs::remove_file(&src_path);

    BackendCompile {
        status: output.status,
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        out_bin,
    }
}

fn compile_pinned_source_to(
    stem: &str,
    src: &str,
    out_bin: PathBuf,
    extra_args: &[OsString],
) -> BackendCompile {
    let src_path = write_temp_source(stem, src);
    let toolchain = pinned_toolchain();
    let output = Command::new("rustup")
        .args(["run", toolchain.as_str(), "rustc", "--edition=2021"])
        .args(extra_args)
        .arg("-o")
        .arg(&out_bin)
        .arg(&src_path)
        .output()
        .expect("failed to spawn rustc via rustup");

    let _ = std::fs::remove_file(&src_path);

    BackendCompile {
        status: output.status,
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        out_bin,
    }
}

/// True while the aarch64 Mach-O object-relocation Certified composition
/// has not landed (ObjectRelocationProofRegistry::aarch64_macho_production()
/// is deliberately empty): every backend compile on this host fails
/// promotion with TCG-PROOF-465/object-relocation-inventory. When the
/// lanes register, this returns false and the original capability
/// assertions below resume automatically — nothing to un-ignore.
fn aarch64_macho_promotion_ratchet(stderr: &str) -> bool {
    cfg!(all(target_arch = "aarch64", target_os = "macos"))
        && stderr.contains("TCG-PROOF-465")
        && stderr.contains("object relocation inventory")
}

/// If a backend compile failed on the promotion ratchet, assert the
/// diagnostic still has the documented fail-closed shape and tell the
/// caller to return early instead of asserting pre-ratchet capabilities.
fn backend_compile_hit_promotion_ratchet(compiled: &BackendCompile) -> bool {
    if compiled.status.success() || !aarch64_macho_promotion_ratchet(&compiled.stderr) {
        return false;
    }
    assert!(
        compiled.stderr.contains("proof promotion rejected")
            && compiled
                .stderr
                .contains("no object relocation proof is registered"),
        "promotion ratchet diagnostic lost its documented fail-closed shape. \
         stderr: <<<{stderr}>>>",
        stderr = compiled.stderr
    );
    true
}

fn assert_backend_source_compiles(stem: &str, src: &str) {
    let compiled = compile_backend_source(stem, src);
    eprintln!("rustc stdout:\n{}", compiled.stdout);
    eprintln!("rustc stderr:\n{}", compiled.stderr);
    eprintln!("rustc exit: {:?}", compiled.status);

    if backend_compile_hit_promotion_ratchet(&compiled) {
        return;
    }
    assert!(
        compiled.status.success(),
        "rustc failed to compile {stem}. stderr was: <<<{stderr}>>>",
        stderr = compiled.stderr
    );
    assert!(
        compiled.out_bin.exists(),
        "rustc succeeded but did not produce {:?}",
        compiled.out_bin
    );
    let _ = std::fs::remove_file(&compiled.out_bin);

    let load_failure_markers = [
        "failed to load",
        "could not load",
        "couldn't load",
        "dlopen",
        "image not found",
        "Library not loaded",
    ];
    for marker in &load_failure_markers {
        assert!(
            !compiled.stderr.contains(marker),
            "rustc failed to load our backend dylib \
             (matched marker: {marker:?}). stderr: <<<{stderr}>>>",
            stderr = compiled.stderr
        );
    }
}

fn run_binary_with_timeout(path: &Path, timeout: Duration) -> Output {
    let mut child = Command::new(path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn compiled reference-union binary");
    let start = Instant::now();
    loop {
        if child
            .try_wait()
            .expect("failed to poll compiled reference-union binary")
            .is_some()
        {
            return child
                .wait_with_output()
                .expect("failed to collect reference-union output");
        }
        if start.elapsed() >= timeout {
            child
                .kill()
                .expect("failed to kill timed-out reference-union binary");
            let killed = child
                .wait_with_output()
                .expect("failed to collect timed-out reference-union output");
            panic!(
                "reference-union binary did not exit before timeout; \
                 stdout=<<<{}>>> stderr=<<<{}>>>",
                String::from_utf8_lossy(&killed.stdout),
                String::from_utf8_lossy(&killed.stderr)
            );
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

fn assert_backend_source_exits_success(stem: &str, src: &str) {
    // The oracle lock guards only serialization of concurrent rustc/oracle
    // invocations (Mutex<()> — it protects no shared data). Recover from poison
    // so that a genuine assertion failure in ONE test does not cascade
    // "lock poisoned" panics across every other test in this binary, which
    // masked the true result (turning 1 real failure into 29 reported ones).
    let _guard = RUNTIME_ORACLE_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let compiled = compile_backend_source(stem, src);
    eprintln!("rustc stdout:\n{}", compiled.stdout);
    eprintln!("rustc stderr:\n{}", compiled.stderr);
    eprintln!("rustc exit: {:?}", compiled.status);

    if backend_compile_hit_promotion_ratchet(&compiled) {
        return;
    }
    assert!(
        compiled.status.success(),
        "rustc failed to compile {stem} oracle. stderr was: <<<{stderr}>>>",
        stderr = compiled.stderr
    );
    assert!(
        compiled.out_bin.exists(),
        "rustc succeeded but did not produce {:?}",
        compiled.out_bin
    );
    let load_failure_markers = [
        "failed to load",
        "could not load",
        "couldn't load",
        "dlopen",
        "image not found",
        "Library not loaded",
    ];
    for marker in &load_failure_markers {
        assert!(
            !compiled.stderr.contains(marker),
            "rustc failed to load our backend dylib \
             (matched marker: {marker:?}). stderr: <<<{stderr}>>>",
            stderr = compiled.stderr
        );
    }

    let run = run_binary_with_timeout(&compiled.out_bin, Duration::from_secs(3));
    let run_stdout = String::from_utf8_lossy(&run.stdout);
    let run_stderr = String::from_utf8_lossy(&run.stderr);
    let _ = std::fs::remove_file(&compiled.out_bin);

    assert!(
        run.status.success(),
        "{stem} oracle exited with {:?}; stdout=<<<{}>>> stderr=<<<{}>>>",
        run.status,
        run_stdout,
        run_stderr
    );
    assert_eq!(run_stdout, "", "{stem} oracle wrote stdout");
    assert_eq!(run_stderr, "", "{stem} oracle wrote stderr");
}

fn assert_backend_library_links_and_runs(
    stem: &str,
    lib_src: &str,
    bin_src: &str,
    crate_name: &str,
) {
    // The oracle lock guards only serialization of concurrent rustc/oracle
    // invocations (Mutex<()> — it protects no shared data). Recover from poison
    // so that a genuine assertion failure in ONE test does not cascade
    // "lock poisoned" panics across every other test in this binary, which
    // masked the true result (turning 1 real failure into 29 reported ones).
    let _guard = RUNTIME_ORACLE_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let lib_path = std::env::temp_dir().join(format!(
        "lib{crate_name}_{}_{}.rlib",
        std::process::id(),
        stem
    ));
    let lib_args = [
        OsString::from("--crate-type=lib"),
        OsString::from("--crate-name"),
        OsString::from(crate_name),
    ];
    let lib = compile_backend_source_to(stem, lib_src, lib_path.clone(), &lib_args);
    eprintln!("{stem} lib rustc stdout:\n{}", lib.stdout);
    eprintln!("{stem} lib rustc stderr:\n{}", lib.stderr);
    eprintln!("{stem} lib rustc exit: {:?}", lib.status);
    if backend_compile_hit_promotion_ratchet(&lib) {
        return;
    }
    assert!(
        lib.status.success(),
        "{stem}: rustc failed to compile library oracle. stderr was: <<<{stderr}>>>",
        stderr = lib.stderr
    );
    assert!(
        lib_path.exists(),
        "{stem}: rustc succeeded but did not produce {:?}",
        lib_path
    );

    let extern_arg = {
        let mut arg = OsString::from("--extern=");
        arg.push(crate_name);
        arg.push("=");
        arg.push(&lib_path);
        arg
    };
    let bin_path = temp_artifact_path(stem, "bin");
    let bin = compile_pinned_source_to(stem, bin_src, bin_path.clone(), &[extern_arg]);
    eprintln!("{stem} bin rustc stdout:\n{}", bin.stdout);
    eprintln!("{stem} bin rustc stderr:\n{}", bin.stderr);
    eprintln!("{stem} bin rustc exit: {:?}", bin.status);
    assert!(
        bin.status.success(),
        "{stem}: rustc failed to compile linked binary oracle. stderr was: <<<{stderr}>>>",
        stderr = bin.stderr
    );
    assert!(
        bin_path.exists(),
        "{stem}: rustc succeeded but did not produce {:?}",
        bin_path
    );

    let load_failure_markers = [
        "failed to load",
        "could not load",
        "couldn't load",
        "dlopen",
        "image not found",
        "Library not loaded",
    ];
    for marker in &load_failure_markers {
        assert!(
            !lib.stderr.contains(marker),
            "{stem}: rustc failed to load our backend dylib during lib compilation \
             (matched marker: {marker:?}). stderr: <<<{stderr}>>>",
            stderr = lib.stderr
        );
    }

    let run = run_binary_with_timeout(&bin_path, Duration::from_secs(3));
    let run_stdout = String::from_utf8_lossy(&run.stdout);
    let run_stderr = String::from_utf8_lossy(&run.stderr);
    let _ = std::fs::remove_file(&lib_path);
    let _ = std::fs::remove_file(&bin_path);

    assert!(
        run.status.success(),
        "{stem} linked oracle exited with {:?}; stdout=<<<{}>>> stderr=<<<{}>>>",
        run.status,
        run_stdout,
        run_stderr
    );
    assert_eq!(run_stdout, "", "{stem} linked oracle wrote stdout");
    assert_eq!(run_stderr, "", "{stem} linked oracle wrote stderr");
}

fn assert_backend_library_and_backend_caller_link_and_run(
    stem: &str,
    lib_src: &str,
    bin_src: &str,
    crate_name: &str,
) {
    // The oracle lock guards only serialization of concurrent rustc/oracle
    // invocations (Mutex<()> — it protects no shared data). Recover from poison
    // so that a genuine assertion failure in ONE test does not cascade
    // "lock poisoned" panics across every other test in this binary, which
    // masked the true result (turning 1 real failure into 29 reported ones).
    let _guard = RUNTIME_ORACLE_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let lib_path = std::env::temp_dir().join(format!(
        "lib{crate_name}_{}_{}.rlib",
        std::process::id(),
        stem
    ));
    let lib_args = [
        OsString::from("--crate-type=lib"),
        OsString::from("--crate-name"),
        OsString::from(crate_name),
    ];
    let lib = compile_backend_source_to(stem, lib_src, lib_path.clone(), &lib_args);
    eprintln!("{stem} lib rustc stdout:\n{}", lib.stdout);
    eprintln!("{stem} lib rustc stderr:\n{}", lib.stderr);
    eprintln!("{stem} lib rustc exit: {:?}", lib.status);
    if backend_compile_hit_promotion_ratchet(&lib) {
        return;
    }
    assert!(
        lib.status.success(),
        "{stem}: rustc failed to compile backend library oracle. stderr was: <<<{stderr}>>>",
        stderr = lib.stderr
    );
    assert!(
        lib_path.exists(),
        "{stem}: rustc succeeded but did not produce {:?}",
        lib_path
    );

    let extern_arg = {
        let mut arg = OsString::from("--extern=");
        arg.push(crate_name);
        arg.push("=");
        arg.push(&lib_path);
        arg
    };
    let bin_path = temp_artifact_path(stem, "backend_bin");
    let bin = compile_backend_source_to(stem, bin_src, bin_path.clone(), &[extern_arg]);
    eprintln!("{stem} backend bin rustc stdout:\n{}", bin.stdout);
    eprintln!("{stem} backend bin rustc stderr:\n{}", bin.stderr);
    eprintln!("{stem} backend bin rustc exit: {:?}", bin.status);
    if backend_compile_hit_promotion_ratchet(&bin) {
        let _ = std::fs::remove_file(&lib_path);
        return;
    }
    assert!(
        bin.status.success(),
        "{stem}: rustc failed to compile backend caller oracle. stderr was: <<<{stderr}>>>",
        stderr = bin.stderr
    );
    assert!(
        bin_path.exists(),
        "{stem}: rustc succeeded but did not produce {:?}",
        bin_path
    );

    let load_failure_markers = [
        "failed to load",
        "could not load",
        "couldn't load",
        "dlopen",
        "image not found",
        "Library not loaded",
    ];
    for marker in &load_failure_markers {
        assert!(
            !lib.stderr.contains(marker) && !bin.stderr.contains(marker),
            "{stem}: rustc failed to load our backend dylib \
             (matched marker: {marker:?}). lib stderr: <<<{lib_stderr}>>> \
             bin stderr: <<<{bin_stderr}>>>",
            lib_stderr = lib.stderr,
            bin_stderr = bin.stderr
        );
    }

    let run = run_binary_with_timeout(&bin_path, Duration::from_secs(3));
    let run_stdout = String::from_utf8_lossy(&run.stdout);
    let run_stderr = String::from_utf8_lossy(&run.stderr);
    let _ = std::fs::remove_file(&lib_path);
    let _ = std::fs::remove_file(&bin_path);

    assert!(
        run.status.success(),
        "{stem} backend caller oracle exited with {:?}; stdout=<<<{}>>> stderr=<<<{}>>>",
        run.status,
        run_stdout,
        run_stderr
    );
    assert_eq!(run_stdout, "", "{stem} backend caller oracle wrote stdout");
    assert_eq!(run_stderr, "", "{stem} backend caller oracle wrote stderr");
}

#[test]
fn scalar_references_and_same_typed_union_run_with_rust_semantics() {
    let src = r#"
#![no_main]

struct Pair {
    left: u64,
    right: u64,
}

union Slot {
    bits: u64,
    alias: u64,
}

#[inline(never)]
fn make_slot(value: u64) -> Slot {
    Slot { bits: value }
}

#[inline(never)]
fn read_slot(slot: Slot) -> u64 {
    unsafe { slot.alias }
}

#[inline(never)]
fn identity_ref<T>(value: &T) -> &T {
    value
}

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    let mut pair = Pair { left: 10, right: 5 };
    let left_ref = &pair.left;
    let left_identity = identity_ref(left_ref);
    let mut total = *left_identity;
    if total != 10 {
        return 11;
    }

    let right_ref = &mut pair.right;
    *right_ref = *right_ref ^ 3;
    if pair.right != 6 {
        return 12;
    }

    let total_ref = &mut total;
    *total_ref = *total_ref + pair.right;
    if total != 16 {
        return 13;
    }

    let slot = Slot { bits: total ^ pair.right };
    let alias = unsafe { slot.alias };
    if alias != 22 {
        return 14;
    }

    let slot_copy = slot;
    let bits = unsafe { slot_copy.bits };
    if bits != alias {
        return 15;
    }

    let called_slot = make_slot(alias ^ 5);
    let called_alias = read_slot(called_slot);
    if called_alias != 19 {
        return 16;
    }

    0
}
"#;

    assert_backend_source_exits_success("reference_union_semantics", src);
}

#[test]
fn target_sized_integer_scalars_run_with_rustc_layout_width() {
    let src = r#"
#![no_main]

#[inline(never)]
fn mix_target_sized(argc: isize, base: usize) -> usize {
    let signed = argc - 3;
    let unsigned = base + 11usize;
    if signed < 0 {
        unsigned ^ ((0isize - signed) as usize)
    } else {
        unsigned ^ (signed as usize)
    }
}

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let observed = mix_target_sized(argc as isize, 0x30usize);
    if argc == 1 {
        if observed == 0x39 { 0 } else { 21 }
    } else if observed == 0x3b {
        0
    } else {
        22
    }
}
"#;

    assert_backend_source_exits_success("target_sized_integer_scalars", src);
}

#[test]
fn branch_variant_scalarized_projections_run_with_rust_semantics() {
    let src = r#"
#![no_main]

struct Pair {
    left: u64,
    right: u64,
}

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let mut tuple = (1u64, 2u64);
    let mut array = [3u64, 4u64];
    let mut pair = Pair { left: 5, right: 6 };

    if argc != 0 {
        tuple = (10, 20);
        array = [30, 40];
        pair = Pair { left: 50, right: 60 };
    }

    let folded = tuple.0 + array[1] + pair.right;
    if argc != 0 {
        if folded == 110 {
            0
        } else {
            31
        }
    } else if folded == 11 {
        0
    } else {
        32
    }
}
"#;

    assert_backend_source_exits_success("branch_scalarized_projection", src);
}

#[test]
fn small_scalarized_projection_branch_joins_run_with_rust_semantics() {
    let src = r#"
#![no_main]

struct Pair {
    left: u64,
    right: u64,
}

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let mut tuple = (1u64, 2u64);
    if argc == 1 {
        tuple = (10, 20);
    }
    if tuple.0 + tuple.1 != 30 {
        return 41;
    }

    let mut array = [3u64, 4u64];
    if argc == 0 {
        array = [30, 40];
    }
    if array[0] + array[1] != 7 {
        return 42;
    }

    let mut pair = Pair { left: 5, right: 6 };
    if argc == 1 {
        pair = Pair { left: 50, right: 60 };
    }
    if pair.left + pair.right != 110 {
        return 43;
    }

    0
}
"#;

    assert_backend_source_exits_success("small_scalarized_projection_branch_joins", src);
}

#[test]
fn branch_variant_immutable_scalar_references_run_with_rust_semantics() {
    let src = r#"
#![no_main]

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let left = 11u64;
    let right = 29u64;
    let mut selected = &left;

    if argc != 0 {
        selected = &right;
    }

    let copied = selected;
    if *copied != 29 {
        return 41;
    }

    let mut selected_left = &left;
    if argc == 0 {
        selected_left = &right;
    }

    if *selected_left != 11 {
        return 42;
    }

    0
}
"#;

    assert_backend_source_exits_success("branch_scalar_reference", src);
}

#[test]
fn branch_variant_mutable_scalar_references_run_with_rust_semantics() {
    let src = r#"
#![no_main]

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let mut left = 11u64;
    let mut right = 29u64;
    let mut selected = &mut left;

    if argc != 0 {
        selected = &mut right;
    }

    *selected = *selected + 1;
    if *selected != 30 {
        return 43;
    }

    let mut selected_left = &mut left;
    if argc == 0 {
        selected_left = &mut right;
    }

    *selected_left = *selected_left + 3;
    if *selected_left != 14 {
        return 44;
    }

    0
}
"#;

    assert_backend_source_exits_success("branch_mutable_scalar_reference", src);
}

#[test]
fn branch_variant_mutable_scalar_reference_call_arg_runs_with_rust_semantics() {
    let src = r#"
#![no_main]

#[inline(never)]
fn bump_ref(value: &mut u64) -> u64 {
    *value = *value + 5;
    *value
}

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let mut left = 7u64;
    let mut right = 13u64;
    let mut selected = &mut left;

    if argc != 0 {
        selected = &mut right;
    }

    let observed = bump_ref(selected);
    if observed != 18 {
        return 45;
    }
    if *selected != 18 {
        return 46;
    }

    let mut selected_left = &mut left;
    if argc == 0 {
        selected_left = &mut right;
    }

    let observed_left = bump_ref(selected_left);
    if observed_left != 12 {
        return 47;
    }
    if *selected_left != 12 {
        return 48;
    }

    0
}
"#;

    assert_backend_source_exits_success("branch_mutable_scalar_reference_call_arg", src);
}

#[test]
fn scalar_reference_return_non_escaping_runs_with_rust_semantics() {
    let src = r#"
#![no_main]

#[inline(never)]
fn pick_ref<'a>(flag: bool, left: &'a u64, right: &'a u64) -> &'a u64 {
    if flag { right } else { left }
}

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let left = 11u64;
    let right = 29u64;

    let selected = pick_ref(argc != 0, &left, &right);
    if *selected != 29 {
        return 49;
    }

    let selected_left = pick_ref(argc == 0, &left, &right);
    if *selected_left != 11 {
        return 50;
    }

    let copied = selected;
    if *copied != 29 {
        return 51;
    }

    0
}
"#;

    // Named unsupported-MIR gap: returning a promoted scalar reference and
    // then passing it as an argument requires scalar borrow materialization,
    // which the backend fails closed on today ([TCG-MIR-UNSUPPORTED]). When
    // borrow materialization lands the refusal disappears and the original
    // runtime oracle below resumes automatically.
    let compiled = compile_backend_source("scalar_reference_return_non_escaping", src);
    if !compiled.status.success()
        && compiled
            .stderr
            .contains("requires scalar borrow materialization")
    {
        assert!(
            compiled.stderr.contains("[TCG-MIR-UNSUPPORTED]"),
            "scalar-borrow refusal fired without the documented fail-closed \
             diagnostic. stderr: <<<{}>>>",
            compiled.stderr
        );
        return;
    }
    assert_backend_source_exits_success("scalar_reference_return_non_escaping", src);
}

#[test]
fn same_typed_union_by_value_abi_compiles_library() {
    let src = r#"
#![crate_type = "lib"]

#[repr(C)]
pub union Slot {
    pub bits: u64,
    pub alias: u64,
}

#[inline(never)]
#[no_mangle]
pub fn read_slot(slot: Slot) -> u64 {
    unsafe { slot.alias }
}
"#;

    assert_backend_source_compiles("same_typed_union_by_value_abi", src);
}

#[test]
fn same_typed_union_return_abi_compiles_library() {
    let src = r#"
#![crate_type = "lib"]

#[repr(C)]
pub union Slot {
    pub bits: u64,
    pub alias: u64,
}

#[inline(never)]
#[no_mangle]
pub fn make_slot(value: u64) -> Slot {
    Slot { bits: value }
}
"#;

    assert_backend_source_compiles("same_typed_union_return_abi", src);
}

#[test]
fn same_typed_union_abi_links_and_runs_with_rust_semantics() {
    let lib_src = r#"
#![crate_type = "lib"]

#[repr(C)]
pub union Slot {
    pub bits: u64,
    pub alias: u64,
}

#[inline(never)]
#[no_mangle]
pub fn read_bits(slot: Slot) -> u64 {
    unsafe { slot.bits }
}

#[inline(never)]
#[no_mangle]
pub fn read_alias(slot: Slot) -> u64 {
    unsafe { slot.alias }
}

#[inline(never)]
#[no_mangle]
pub fn make_bits(value: u64) -> Slot {
    Slot { bits: value }
}

#[inline(never)]
#[no_mangle]
pub fn make_alias(value: u64) -> Slot {
    Slot { alias: value }
}

#[inline(never)]
#[no_mangle]
pub fn xor_slots(left: Slot, right: Slot) -> Slot {
    let lhs = unsafe { left.bits };
    let rhs = unsafe { right.alias };
    Slot { bits: lhs ^ rhs }
}
"#;

    let bin_src = r#"
extern crate rcl2_same_typed_union_abi;

fn main() {
    let from_bits = rcl2_same_typed_union_abi::make_bits(0x0123_4567_89ab_cdefu64);
    if rcl2_same_typed_union_abi::read_alias(from_bits) != 0x0123_4567_89ab_cdefu64 {
        std::process::exit(71);
    }

    let from_alias = rcl2_same_typed_union_abi::make_alias(0xfedc_ba98_7654_3210u64);
    if rcl2_same_typed_union_abi::read_bits(from_alias) != 0xfedc_ba98_7654_3210u64 {
        std::process::exit(72);
    }

    let combined = rcl2_same_typed_union_abi::xor_slots(
        rcl2_same_typed_union_abi::make_bits(0x00ff_00ff_00ff_00ffu64),
        rcl2_same_typed_union_abi::make_alias(0xff00_ff00_ff00_ff00u64),
    );
    if rcl2_same_typed_union_abi::read_alias(combined) != 0xffff_ffff_ffff_ffffu64 {
        std::process::exit(73);
    }

    let high_bit = rcl2_same_typed_union_abi::make_alias(1u64 << 63);
    if rcl2_same_typed_union_abi::read_bits(high_bit) != 1u64 << 63 {
        std::process::exit(74);
    }
}
"#;

    assert_backend_library_links_and_runs(
        "same_typed_union_abi",
        lib_src,
        bin_src,
        "rcl2_same_typed_union_abi",
    );
}

#[test]
fn same_width_integer_union_by_value_abi_compiles_library() {
    let src = r#"
#![crate_type = "lib"]

#[repr(C)]
pub union Slot {
    pub unsigned: u64,
    pub signed: i64,
}

#[inline(never)]
#[no_mangle]
pub fn read_signed(slot: Slot) -> i64 {
    unsafe { slot.signed }
}
"#;

    assert_backend_source_compiles("same_width_union_by_value_abi", src);
}

#[test]
fn same_width_integer_union_return_abi_compiles_library() {
    let src = r#"
#![crate_type = "lib"]

#[repr(C)]
pub union Slot {
    pub unsigned: u64,
    pub signed: i64,
}

#[inline(never)]
#[no_mangle]
pub fn make_signed(value: i64) -> Slot {
    Slot { signed: value }
}
"#;

    assert_backend_source_compiles("same_width_union_return_abi", src);
}

#[test]
fn same_width_integer_union_abi_links_and_runs_with_rust_semantics() {
    let lib_src = r#"
#![crate_type = "lib"]

#[repr(C)]
pub union Slot {
    pub unsigned: u64,
    pub signed: i64,
}

#[inline(never)]
#[no_mangle]
pub fn read_signed(slot: Slot) -> i64 {
    unsafe { slot.signed }
}

#[inline(never)]
#[no_mangle]
pub fn read_unsigned(slot: Slot) -> u64 {
    unsafe { slot.unsigned }
}

#[inline(never)]
#[no_mangle]
pub fn make_signed(value: i64) -> Slot {
    Slot { signed: value }
}

#[inline(never)]
#[no_mangle]
pub fn make_unsigned(value: u64) -> Slot {
    Slot { unsigned: value }
}
"#;

    let bin_src = r#"
extern crate rcl2_same_width_union_abi;

fn main() {
    let from_unsigned = rcl2_same_width_union_abi::make_unsigned(0xffff_ffff_ffff_fffeu64);
    if rcl2_same_width_union_abi::read_signed(from_unsigned) != -2 {
        std::process::exit(61);
    }

    let from_signed = rcl2_same_width_union_abi::make_signed(-3);
    if rcl2_same_width_union_abi::read_unsigned(from_signed) != 0xffff_ffff_ffff_fffdu64 {
        std::process::exit(62);
    }

    let positive = rcl2_same_width_union_abi::make_signed(42);
    if rcl2_same_width_union_abi::read_signed(positive) != 42 {
        std::process::exit(63);
    }

    let high_bit = rcl2_same_width_union_abi::make_unsigned(1u64 << 63);
    if rcl2_same_width_union_abi::read_signed(high_bit) != i64::MIN {
        std::process::exit(64);
    }
}
"#;

    assert_backend_library_links_and_runs(
        "same_width_integer_union_abi",
        lib_src,
        bin_src,
        "rcl2_same_width_union_abi",
    );
}

#[test]
fn mixed_width_integer_union_abi_links_and_runs_with_rust_semantics() {
    let lib_src = r#"
#![crate_type = "lib"]

#[repr(C)]
pub union Slot {
    pub wide: u64,
    pub low: u32,
}

#[repr(C)]
pub union NarrowFirst {
    pub low: u32,
    pub wide: u64,
}

#[inline(never)]
#[no_mangle]
pub fn read_wide(slot: Slot) -> u64 {
    unsafe { slot.wide }
}

#[inline(never)]
#[no_mangle]
pub fn read_low(slot: Slot) -> u32 {
    unsafe { slot.low }
}

#[inline(never)]
#[no_mangle]
pub fn make_wide(value: u64) -> Slot {
    Slot { wide: value }
}

#[inline(never)]
#[no_mangle]
pub fn make_low(value: u32) -> Slot {
    Slot { low: value }
}

#[inline(never)]
#[no_mangle]
pub fn make_narrow_first_wide(value: u64) -> NarrowFirst {
    NarrowFirst { wide: value }
}

#[inline(never)]
#[no_mangle]
pub fn make_narrow_first_low(value: u32) -> NarrowFirst {
    NarrowFirst { low: value }
}

#[inline(never)]
#[no_mangle]
pub fn read_narrow_first_wide(slot: NarrowFirst) -> u64 {
    unsafe { slot.wide }
}

#[inline(never)]
#[no_mangle]
pub fn read_narrow_first_low(slot: NarrowFirst) -> u32 {
    unsafe { slot.low }
}

#[inline(never)]
#[no_mangle]
pub fn merge_low_parts(left: Slot, right: Slot) -> Slot {
    let high = unsafe { left.low } as u64;
    let low = unsafe { right.low } as u64;
    Slot { wide: (high << 32) | low }
}
"#;

    let bin_src = r#"
extern crate rcl2_mixed_width_integer_union_abi;

fn main() {
    let wide = rcl2_mixed_width_integer_union_abi::make_wide(0x1122_3344_aabb_ccddu64);
    if rcl2_mixed_width_integer_union_abi::read_wide(wide) != 0x1122_3344_aabb_ccddu64 {
        std::process::exit(81);
    }

    let low = rcl2_mixed_width_integer_union_abi::make_wide(0x1122_3344_aabb_ccddu64);
    if rcl2_mixed_width_integer_union_abi::read_low(low) != 0xaabb_ccddu32 {
        std::process::exit(82);
    }

    let merged = rcl2_mixed_width_integer_union_abi::merge_low_parts(
        rcl2_mixed_width_integer_union_abi::make_wide(0xffff_ffff_0123_4567u64),
        rcl2_mixed_width_integer_union_abi::make_wide(0x1111_2222_89ab_cdefu64),
    );
    if rcl2_mixed_width_integer_union_abi::read_wide(merged) != 0x0123_4567_89ab_cdefu64 {
        std::process::exit(83);
    }

    let zero_low = rcl2_mixed_width_integer_union_abi::make_wide(0xffff_ffff_0000_0000u64);
    if rcl2_mixed_width_integer_union_abi::read_low(zero_low) != 0 {
        std::process::exit(84);
    }

    let low_active = rcl2_mixed_width_integer_union_abi::make_low(0x89ab_cdefu32);
    if rcl2_mixed_width_integer_union_abi::read_low(low_active) != 0x89ab_cdefu32 {
        std::process::exit(85);
    }

    let narrow_first_wide =
        rcl2_mixed_width_integer_union_abi::make_narrow_first_wide(0x0123_4567_89ab_cdefu64);
    if rcl2_mixed_width_integer_union_abi::read_narrow_first_wide(narrow_first_wide)
        != 0x0123_4567_89ab_cdefu64
    {
        std::process::exit(86);
    }

    let narrow_first_low =
        rcl2_mixed_width_integer_union_abi::make_narrow_first_wide(0xffff_ffff_0123_4567u64);
    if rcl2_mixed_width_integer_union_abi::read_narrow_first_low(narrow_first_low)
        != 0x0123_4567u32
    {
        std::process::exit(87);
    }

    let narrow_first_low_active =
        rcl2_mixed_width_integer_union_abi::make_narrow_first_low(0xaabb_ccddu32);
    if rcl2_mixed_width_integer_union_abi::read_narrow_first_low(narrow_first_low_active)
        != 0xaabb_ccddu32
    {
        std::process::exit(88);
    }
}
"#;

    assert_backend_library_links_and_runs(
        "mixed_width_integer_union_abi",
        lib_src,
        bin_src,
        "rcl2_mixed_width_integer_union_abi",
    );
}

#[test]
fn signed_mixed_width_integer_union_abi_links_and_runs_with_rust_semantics() {
    let lib_src = r#"
#![crate_type = "lib"]

#[repr(C)]
pub union SignedSlot {
    pub wide: i64,
    pub low: i16,
}

#[repr(C)]
pub union SignedNarrowFirst {
    pub low: i16,
    pub wide: i64,
}

#[inline(never)]
#[no_mangle]
pub fn make_signed_wide(value: i64) -> SignedSlot {
    SignedSlot { wide: value }
}

#[inline(never)]
#[no_mangle]
pub fn make_signed_low(value: i16) -> SignedSlot {
    SignedSlot { low: value }
}

#[inline(never)]
#[no_mangle]
pub fn read_signed_wide(slot: SignedSlot) -> i64 {
    unsafe { slot.wide }
}

#[inline(never)]
#[no_mangle]
pub fn read_signed_low(slot: SignedSlot) -> i16 {
    unsafe { slot.low }
}

#[inline(never)]
#[no_mangle]
pub fn make_signed_narrow_first_wide(value: i64) -> SignedNarrowFirst {
    SignedNarrowFirst { wide: value }
}

#[inline(never)]
#[no_mangle]
pub fn make_signed_narrow_first_low(value: i16) -> SignedNarrowFirst {
    SignedNarrowFirst { low: value }
}

#[inline(never)]
#[no_mangle]
pub fn read_signed_narrow_first_wide(slot: SignedNarrowFirst) -> i64 {
    unsafe { slot.wide }
}

#[inline(never)]
#[no_mangle]
pub fn read_signed_narrow_first_low(slot: SignedNarrowFirst) -> i16 {
    unsafe { slot.low }
}
"#;

    let bin_src = r#"
extern crate rcl2_signed_mixed_width_union_abi;

fn main() {
    let wide = rcl2_signed_mixed_width_union_abi::make_signed_wide(-0x0123_4567_89abi64);
    if rcl2_signed_mixed_width_union_abi::read_signed_wide(wide) != -0x0123_4567_89abi64 {
        std::process::exit(91);
    }

    let low_from_wide = rcl2_signed_mixed_width_union_abi::make_signed_wide(-2i64);
    if rcl2_signed_mixed_width_union_abi::read_signed_low(low_from_wide) != -2i16 {
        std::process::exit(92);
    }

    let low_active = rcl2_signed_mixed_width_union_abi::make_signed_low(-1234i16);
    if rcl2_signed_mixed_width_union_abi::read_signed_low(low_active) != -1234i16 {
        std::process::exit(93);
    }

    let narrow_first_wide =
        rcl2_signed_mixed_width_union_abi::make_signed_narrow_first_wide(-0x0102_0304i64);
    if rcl2_signed_mixed_width_union_abi::read_signed_narrow_first_wide(narrow_first_wide)
        != -0x0102_0304i64
    {
        std::process::exit(94);
    }

    let narrow_first_low_from_wide =
        rcl2_signed_mixed_width_union_abi::make_signed_narrow_first_wide(-3i64);
    if rcl2_signed_mixed_width_union_abi::read_signed_narrow_first_low(
        narrow_first_low_from_wide,
    ) != -3i16
    {
        std::process::exit(95);
    }

    let narrow_first_low_active =
        rcl2_signed_mixed_width_union_abi::make_signed_narrow_first_low(-2222i16);
    if rcl2_signed_mixed_width_union_abi::read_signed_narrow_first_low(
        narrow_first_low_active,
    ) != -2222i16
    {
        std::process::exit(96);
    }
}
"#;

    assert_backend_library_links_and_runs(
        "signed_mixed_width_integer_union_abi",
        lib_src,
        bin_src,
        "rcl2_signed_mixed_width_union_abi",
    );
}

#[test]
fn smaller_mixed_width_integer_union_abi_links_and_runs_with_rust_semantics() {
    let lib_src = r#"
#![crate_type = "lib"]

#[repr(C)]
pub union SmallSlot {
    pub wide: u32,
    pub low: u16,
}

#[repr(C)]
pub union ByteNarrowFirst {
    pub low: u8,
    pub wide: u32,
}

#[inline(never)]
#[no_mangle]
pub fn make_small_wide(value: u32) -> SmallSlot {
    SmallSlot { wide: value }
}

#[inline(never)]
#[no_mangle]
pub fn make_small_low(value: u16) -> SmallSlot {
    SmallSlot { low: value }
}

#[inline(never)]
#[no_mangle]
pub fn read_small_wide(slot: SmallSlot) -> u32 {
    unsafe { slot.wide }
}

#[inline(never)]
#[no_mangle]
pub fn read_small_low(slot: SmallSlot) -> u16 {
    unsafe { slot.low }
}

#[inline(never)]
#[no_mangle]
pub fn make_byte_narrow_first_wide(value: u32) -> ByteNarrowFirst {
    ByteNarrowFirst { wide: value }
}

#[inline(never)]
#[no_mangle]
pub fn make_byte_narrow_first_low(value: u8) -> ByteNarrowFirst {
    ByteNarrowFirst { low: value }
}

#[inline(never)]
#[no_mangle]
pub fn read_byte_narrow_first_wide(slot: ByteNarrowFirst) -> u32 {
    unsafe { slot.wide }
}

#[inline(never)]
#[no_mangle]
pub fn read_byte_narrow_first_low(slot: ByteNarrowFirst) -> u8 {
    unsafe { slot.low }
}
"#;

    let bin_src = r#"
extern crate rcl2_smaller_mixed_width_union_abi;

fn main() {
    let wide = rcl2_smaller_mixed_width_union_abi::make_small_wide(0x89ab_cdefu32);
    if rcl2_smaller_mixed_width_union_abi::read_small_wide(wide) != 0x89ab_cdefu32 {
        std::process::exit(101);
    }

    let low_from_wide = rcl2_smaller_mixed_width_union_abi::make_small_wide(0x0123_cdefu32);
    if rcl2_smaller_mixed_width_union_abi::read_small_low(low_from_wide) != 0xcdefu16 {
        std::process::exit(102);
    }

    let low_active = rcl2_smaller_mixed_width_union_abi::make_small_low(0xbeefu16);
    if rcl2_smaller_mixed_width_union_abi::read_small_low(low_active) != 0xbeefu16 {
        std::process::exit(103);
    }

    let narrow_first_wide =
        rcl2_smaller_mixed_width_union_abi::make_byte_narrow_first_wide(0x1020_30f0u32);
    if rcl2_smaller_mixed_width_union_abi::read_byte_narrow_first_wide(narrow_first_wide)
        != 0x1020_30f0u32
    {
        std::process::exit(104);
    }

    let narrow_first_low_from_wide =
        rcl2_smaller_mixed_width_union_abi::make_byte_narrow_first_wide(0x1020_30f0u32);
    if rcl2_smaller_mixed_width_union_abi::read_byte_narrow_first_low(
        narrow_first_low_from_wide,
    ) != 0xf0u8
    {
        std::process::exit(105);
    }

    let narrow_first_low_active =
        rcl2_smaller_mixed_width_union_abi::make_byte_narrow_first_low(0xabu8);
    if rcl2_smaller_mixed_width_union_abi::read_byte_narrow_first_low(
        narrow_first_low_active,
    ) != 0xabu8
    {
        std::process::exit(106);
    }
}
"#;

    assert_backend_library_links_and_runs(
        "smaller_mixed_width_integer_union_abi",
        lib_src,
        bin_src,
        "rcl2_smaller_mixed_width_union_abi",
    );
}

#[test]
fn same_width_integer_union_projection_runs_with_rust_semantics() {
    let src = r#"
#![no_main]

union Slot {
    unsigned: u64,
    signed: i64,
}

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    let from_unsigned = Slot {
        unsigned: 0xffff_ffff_ffff_fffeu64,
    };
    let signed_alias = unsafe { from_unsigned.signed };
    if signed_alias != -2 {
        return 21;
    }

    let from_signed = Slot { signed: -3 };
    let unsigned_alias = unsafe { from_signed.unsigned };
    if unsigned_alias != 0xffff_ffff_ffff_fffdu64 {
        return 22;
    }

    let copied = from_signed;
    let copied_alias = unsafe { copied.unsigned };
    if copied_alias != unsigned_alias {
        return 23;
    }

    0
}
"#;

    assert_backend_source_exits_success("same_width_integer_union_projection", src);
}

#[test]
fn read_only_reference_parameter_abi_compiles_library() {
    let src = r#"
#![crate_type = "lib"]

#[no_mangle]
pub fn read_ref(value: &u64) -> u64 {
    let copied = value;
    *copied
}
"#;

    assert_backend_source_compiles("reference_parameter_abi", src);
}

#[test]
fn mutable_reference_parameter_abi_compiles_library() {
    let src = r#"
#![crate_type = "lib"]

#[no_mangle]
pub fn bump_ref(value: &mut u64) -> u64 {
    *value = *value + 1;
    *value
}
"#;

    assert_backend_source_compiles("mutable_reference_parameter_abi", src);
}

#[test]
fn scalar_reference_parameter_abi_links_and_runs_with_rust_semantics() {
    let lib_src = r#"
#![crate_type = "lib"]

#[inline(never)]
#[no_mangle]
pub fn read_ref(value: &u64) -> u64 {
    let copied = value;
    *copied
}

#[inline(never)]
#[no_mangle]
pub fn bump_ref(value: &mut u64) -> u64 {
    *value = *value + 1;
    *value
}
"#;

    let bin_src = r#"
extern crate rcl2_ref_param_abi;

fn main() {
    let readonly = 41u64;
    if rcl2_ref_param_abi::read_ref(&readonly) != 41 {
        std::process::exit(51);
    }

    let mut writable = 8u64;
    if rcl2_ref_param_abi::bump_ref(&mut writable) != 9 {
        std::process::exit(52);
    }
    if writable != 9 {
        std::process::exit(53);
    }

    if rcl2_ref_param_abi::read_ref(&writable) != 9 {
        std::process::exit(54);
    }
    if rcl2_ref_param_abi::bump_ref(&mut writable) != 10 {
        std::process::exit(55);
    }
    if writable != 10 {
        std::process::exit(56);
    }
}
"#;

    assert_backend_library_links_and_runs(
        "scalar_reference_parameter_abi",
        lib_src,
        bin_src,
        "rcl2_ref_param_abi",
    );
}

#[test]
fn scalar_reference_call_arguments_run_with_backend_compiled_caller() {
    let lib_src = r#"
#![crate_type = "lib"]

#[inline(never)]
#[no_mangle]
pub extern "C" fn read_ref(value: &u64) -> u64 {
    let copied = value;
    *copied
}

#[inline(never)]
#[no_mangle]
pub extern "C" fn bump_ref(value: &mut u64) -> u64 {
    *value = *value + 1;
    *value
}

#[inline(never)]
#[no_mangle]
pub extern "C" fn write_one_return_two(value: &mut u64) -> u64 {
    *value = 1;
    2
}

#[inline(never)]
#[no_mangle]
pub extern "C" fn write_value(value: &mut u64, replacement: u64) -> u64 {
    *value = replacement;
    replacement ^ 3
}
"#;

    let bin_src = r#"
#![no_main]

extern crate rcl2_ref_call_args;

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    let readonly = 41u64;
    if rcl2_ref_call_args::read_ref(&readonly) != 41 {
        return 91;
    }

    let mut writable = 8u64;
    if rcl2_ref_call_args::bump_ref(&mut writable) != 9 {
        return 92;
    }
    if writable != 9 {
        return 93;
    }
    if rcl2_ref_call_args::read_ref(&writable) != 9 {
        return 94;
    }

    let observed = rcl2_ref_call_args::write_value(&mut writable, 21);
    if observed != (21 ^ 3) {
        return 95;
    }
    if writable != 21 {
        return 96;
    }

    let mut overwritten = 99u64;
    overwritten = rcl2_ref_call_args::write_one_return_two(&mut overwritten);
    if overwritten != 2 {
        return 97;
    }

    0
}
"#;

    assert_backend_library_and_backend_caller_link_and_run(
        "scalar_reference_call_args",
        lib_src,
        bin_src,
        "rcl2_ref_call_args",
    );
}

#[test]
fn tuple_reference_parameter_abi_links_and_runs_with_rust_semantics() {
    let lib_src = r#"
#![crate_type = "lib"]

#[inline(never)]
pub fn read_pair(value: &(u64, u64)) -> u64 {
    let copied = value;
    copied.0 ^ copied.1
}

#[inline(never)]
pub fn write_pair(value: &mut (u64, u64), left: u64, right: u64) -> u64 {
    *value = (left ^ 3, right ^ 5);
    value.0 ^ value.1
}
"#;

    let bin_src = r#"
extern crate rcl2_tuple_ref_param_abi;

fn main() {
    let pair = (0x10u64, 0x03u64);
    if rcl2_tuple_ref_param_abi::read_pair(&pair) != 0x13 {
        std::process::exit(101);
    }

    let mut writable = (7u64, 11u64);
    let observed = rcl2_tuple_ref_param_abi::write_pair(&mut writable, 8, 30);
    if writable != (11, 27) {
        std::process::exit(102);
    }
    if observed != (11 ^ 27) {
        std::process::exit(103);
    }

    if rcl2_tuple_ref_param_abi::read_pair(&writable) != (11 ^ 27) {
        std::process::exit(104);
    }
}
"#;

    assert_backend_library_links_and_runs(
        "tuple_reference_parameter_abi",
        lib_src,
        bin_src,
        "rcl2_tuple_ref_param_abi",
    );
}

#[test]
fn struct_reference_parameter_abi_links_and_runs_with_rust_semantics() {
    let lib_src = r#"
#![crate_type = "lib"]

#[repr(C)]
pub struct Pair {
    pub left: u64,
    pub right: u64,
}

#[inline(never)]
pub fn read_pair(value: &Pair) -> u64 {
    let copied = value;
    copied.left ^ copied.right
}

#[inline(never)]
pub fn write_pair(value: &mut Pair, left: u64, right: u64) -> u64 {
    *value = Pair {
        left: left ^ 3,
        right: right ^ 5,
    };
    value.left ^ value.right
}
"#;

    let bin_src = r#"
extern crate rcl2_struct_ref_param_abi;

use rcl2_struct_ref_param_abi::Pair;

fn main() {
    let pair = Pair {
        left: 0x10u64,
        right: 0x03u64,
    };
    if rcl2_struct_ref_param_abi::read_pair(&pair) != 0x13 {
        std::process::exit(121);
    }

    let mut writable = Pair { left: 7, right: 11 };
    let observed = rcl2_struct_ref_param_abi::write_pair(&mut writable, 8, 30);
    if writable.left != 11 {
        std::process::exit(122);
    }
    if writable.right != 27 {
        std::process::exit(123);
    }
    if observed != (11 ^ 27) {
        std::process::exit(124);
    }

    if rcl2_struct_ref_param_abi::read_pair(&writable) != (11 ^ 27) {
        std::process::exit(125);
    }
}
"#;

    assert_backend_library_links_and_runs(
        "struct_reference_parameter_abi",
        lib_src,
        bin_src,
        "rcl2_struct_ref_param_abi",
    );
}

#[test]
fn array_reference_parameter_abi_links_and_runs_with_rust_semantics() {
    let lib_src = r#"
#![crate_type = "lib"]

#[inline(never)]
pub fn read_array(value: &[u64; 2]) -> u64 {
    let copied = value;
    copied[0] ^ copied[1]
}

#[inline(never)]
pub fn write_array(value: &mut [u64; 2], left: u64, right: u64) -> u64 {
    *value = [left ^ 3, right ^ 5];
    value[0] ^ value[1]
}
"#;

    let bin_src = r#"
extern crate rcl2_array_ref_param_abi;

fn main() {
    let array = [0x10u64, 0x03u64];
    if rcl2_array_ref_param_abi::read_array(&array) != 0x13 {
        std::process::exit(141);
    }

    let mut writable = [7u64, 11u64];
    let observed = rcl2_array_ref_param_abi::write_array(&mut writable, 8, 30);
    if writable != [11, 27] {
        std::process::exit(142);
    }
    if observed != (11 ^ 27) {
        std::process::exit(143);
    }

    if rcl2_array_ref_param_abi::read_array(&writable) != (11 ^ 27) {
        std::process::exit(144);
    }
}
"#;

    assert_backend_library_links_and_runs(
        "array_reference_parameter_abi",
        lib_src,
        bin_src,
        "rcl2_array_ref_param_abi",
    );
}

#[test]
fn nested_array_reference_parameter_abi_links_and_runs_with_rust_semantics() {
    let lib_src = r#"
#![crate_type = "lib"]

#[inline(never)]
pub fn read_nested_array(value: &[(u64, u64); 2]) -> u64 {
    let copied = value;
    copied[0].0 ^ copied[0].1 ^ copied[1].0 ^ copied[1].1
}

#[inline(never)]
pub fn write_nested_array_fields(value: &mut [(u64, u64); 2], left: u64, right: u64) -> u64 {
    value[0].0 = left ^ 3;
    value[0].1 = right ^ 5;
    value[1].0 = value[0].0 + 7;
    value[1].1 = value[0].1 + 11;
    value[0].0 ^ value[0].1 ^ value[1].0 ^ value[1].1
}
"#;

    let bin_src = r#"
extern crate rcl2_nested_array_ref_param_abi;

fn main() {
    let array = [(0x10u64, 0x03u64), (0x05u64, 0x30u64)];
    if rcl2_nested_array_ref_param_abi::read_nested_array(&array) != (0x10 ^ 0x03 ^ 0x05 ^ 0x30) {
        std::process::exit(181);
    }

    let mut writable = [(7u64, 11u64), (13u64, 17u64)];
    let observed = rcl2_nested_array_ref_param_abi::write_nested_array_fields(&mut writable, 8, 30);
    if writable != [(11, 27), (18, 38)] {
        std::process::exit(182);
    }
    if observed != (11 ^ 27 ^ 18 ^ 38) {
        std::process::exit(183);
    }

    if rcl2_nested_array_ref_param_abi::read_nested_array(&writable) != (11 ^ 27 ^ 18 ^ 38) {
        std::process::exit(184);
    }
}
"#;

    assert_backend_library_links_and_runs(
        "nested_array_reference_parameter_abi",
        lib_src,
        bin_src,
        "rcl2_nested_array_ref_param_abi",
    );
}

#[test]
fn nested_array_reference_whole_store_links_and_runs_with_rust_semantics() {
    let lib_src = r#"
#![crate_type = "lib"]

#[inline(never)]
pub fn write_nested_array_whole(value: &mut [(u64, u64); 2]) -> u64 {
    *value = [(1, 2), (3, 4)];
    value[0].0 ^ value[0].1 ^ value[1].0 ^ value[1].1
}
"#;

    let bin_src = r#"
extern crate rcl2_nested_array_whole_store;

fn main() {
    let mut array = [(7u64, 11u64), (13u64, 17u64)];
    let observed = rcl2_nested_array_whole_store::write_nested_array_whole(&mut array);
    if array != [(1, 2), (3, 4)] {
        std::process::exit(185);
    }
    if observed != (1 ^ 2 ^ 3 ^ 4) {
        std::process::exit(186);
    }
}
"#;

    assert_backend_library_links_and_runs(
        "nested_array_reference_whole_store",
        lib_src,
        bin_src,
        "rcl2_nested_array_whole_store",
    );
}

#[test]
fn recursive_nested_array_reference_whole_store_links_and_runs_with_rust_semantics() {
    let lib_src = r#"
#![crate_type = "lib"]

#[inline(never)]
pub fn write_recursive_nested_array_whole(value: &mut [(u64, (u64, u64)); 2]) -> u64 {
    *value = [(1, (2, 3)), (4, (5, 6))];
    0x1191
}
"#;

    let bin_src = r#"
extern crate rcl2_recursive_nested_array_whole_store;

fn main() {
    let mut array = [(7u64, (11u64, 13u64)), (17u64, (19u64, 23u64))];
    let observed =
        rcl2_recursive_nested_array_whole_store::write_recursive_nested_array_whole(&mut array);
    if array != [(1, (2, 3)), (4, (5, 6))] {
        std::process::exit(187);
    }
    if observed != 0x1191 {
        std::process::exit(188);
    }
}
"#;

    assert_backend_library_links_and_runs(
        "recursive_nested_array_reference_whole_store",
        lib_src,
        bin_src,
        "rcl2_recursive_nested_array_whole_store",
    );
}

#[test]
fn single_variant_enum_reference_parameter_abi_links_and_runs_with_rust_semantics() {
    let lib_src = r#"
#![crate_type = "lib"]

#[derive(Clone, Copy)]
pub enum Pair {
    Only { left: u64, right: u64 },
}

#[inline(never)]
pub fn read_pair(value: &Pair) -> u64 {
    match *value {
        Pair::Only { left, right } => left ^ right,
    }
}

#[inline(never)]
pub fn write_pair(value: &mut Pair, left: u64, right: u64) -> u64 {
    *value = Pair::Only {
        left: left ^ 3,
        right: right ^ 5,
    };
    match *value {
        Pair::Only { left, right } => left ^ right,
    }
}
"#;

    let bin_src = r#"
extern crate rcl2_enum_ref_param_abi;

use rcl2_enum_ref_param_abi::Pair;

fn main() {
    let pair = Pair::Only {
        left: 0x10u64,
        right: 0x03u64,
    };
    if rcl2_enum_ref_param_abi::read_pair(&pair) != 0x13 {
        std::process::exit(161);
    }

    let mut writable = Pair::Only { left: 7, right: 11 };
    let observed = rcl2_enum_ref_param_abi::write_pair(&mut writable, 8, 30);
    match writable {
        Pair::Only { left, right } => {
            if left != 11 {
                std::process::exit(162);
            }
            if right != 27 {
                std::process::exit(163);
            }
        }
    }
    if observed != (11 ^ 27) {
        std::process::exit(164);
    }

    if rcl2_enum_ref_param_abi::read_pair(&writable) != (11 ^ 27) {
        std::process::exit(165);
    }
}
"#;

    assert_backend_library_links_and_runs(
        "enum_reference_parameter_abi",
        lib_src,
        bin_src,
        "rcl2_enum_ref_param_abi",
    );
}

#[test]
fn tuple_reference_call_arguments_run_with_backend_compiled_caller() {
    let lib_src = r#"
#![crate_type = "lib"]

#[inline(never)]
pub extern "C" fn read_pair(value: &(u64, u64)) -> u64 {
    value.0 ^ value.1
}

#[inline(never)]
pub extern "C" fn write_pair(value: &mut (u64, u64), left: u64, right: u64) -> u64 {
    *value = (left ^ 3, right ^ 5);
    value.0 ^ value.1
}
"#;

    let bin_src = r#"
#![no_main]

extern crate rcl2_tuple_ref_call_args;

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    let pair = (0x10u64, 0x03u64);
    if rcl2_tuple_ref_call_args::read_pair(&pair) != 19 {
        return 111;
    }

    let mut writable = (7u64, 11u64);
    let observed = rcl2_tuple_ref_call_args::write_pair(&mut writable, 8, 30);
    if observed != 16 {
        return 112;
    }
    if writable.0 != 11 {
        return 113;
    }
    if writable.1 != 27 {
        return 114;
    }
    if rcl2_tuple_ref_call_args::read_pair(&writable) != 16 {
        return 115;
    }

    let copied = &writable;
    if rcl2_tuple_ref_call_args::read_pair(copied) != 16 {
        return 116;
    }

    0
}
"#;

    assert_backend_library_and_backend_caller_link_and_run(
        "tuple_reference_call_args",
        lib_src,
        bin_src,
        "rcl2_tuple_ref_call_args",
    );
}

#[test]
fn struct_reference_call_arguments_run_with_backend_compiled_caller() {
    let lib_src = r#"
#![crate_type = "lib"]

#[repr(C)]
pub struct Pair {
    pub left: u64,
    pub right: u64,
}

#[inline(never)]
pub extern "C" fn read_pair(value: &Pair) -> u64 {
    value.left ^ value.right
}

#[inline(never)]
pub extern "C" fn write_pair(value: &mut Pair, left: u64, right: u64) -> u64 {
    *value = Pair {
        left: left ^ 3,
        right: right ^ 5,
    };
    value.left ^ value.right
}
"#;

    let bin_src = r#"
#![no_main]

extern crate rcl2_struct_ref_call_args;

use rcl2_struct_ref_call_args::Pair;

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    let pair = Pair {
        left: 0x10u64,
        right: 0x03u64,
    };
    if rcl2_struct_ref_call_args::read_pair(&pair) != 19 {
        return 131;
    }

    let mut writable = Pair { left: 7, right: 11 };
    let observed = rcl2_struct_ref_call_args::write_pair(&mut writable, 8, 30);
    if observed != 16 {
        return 132;
    }
    if writable.left != 11 {
        return 133;
    }
    if writable.right != 27 {
        return 134;
    }
    if rcl2_struct_ref_call_args::read_pair(&writable) != 16 {
        return 135;
    }

    let copied = &writable;
    if rcl2_struct_ref_call_args::read_pair(copied) != 16 {
        return 136;
    }

    0
}
"#;

    assert_backend_library_and_backend_caller_link_and_run(
        "struct_reference_call_args",
        lib_src,
        bin_src,
        "rcl2_struct_ref_call_args",
    );
}

#[test]
fn array_reference_call_arguments_run_with_backend_compiled_caller() {
    let lib_src = r#"
#![crate_type = "lib"]

#[inline(never)]
pub extern "C" fn read_array(value: &[u64; 2]) -> u64 {
    value[0] ^ value[1]
}

#[inline(never)]
pub extern "C" fn write_array(value: &mut [u64; 2], left: u64, right: u64) -> u64 {
    *value = [left ^ 3, right ^ 5];
    value[0] ^ value[1]
}
"#;

    let bin_src = r#"
#![no_main]

extern crate rcl2_array_ref_call_args;

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    let array = [0x10u64, 0x03u64];
    if rcl2_array_ref_call_args::read_array(&array) != 19 {
        return 151;
    }

    let mut writable = [7u64, 11u64];
    let observed = rcl2_array_ref_call_args::write_array(&mut writable, 8, 30);
    if observed != 16 {
        return 152;
    }
    if writable[0] != 11 {
        return 153;
    }
    if writable[1] != 27 {
        return 154;
    }
    if rcl2_array_ref_call_args::read_array(&writable) != 16 {
        return 155;
    }

    let copied = &writable;
    if rcl2_array_ref_call_args::read_array(copied) != 16 {
        return 156;
    }

    0
}
"#;

    assert_backend_library_and_backend_caller_link_and_run(
        "array_reference_call_args",
        lib_src,
        bin_src,
        "rcl2_array_ref_call_args",
    );
}

#[test]
fn nested_array_reference_call_arguments_run_with_backend_compiled_caller() {
    let lib_src = r#"
#![crate_type = "lib"]

#[inline(never)]
pub extern "C" fn read_nested_array(value: &[(u64, u64); 2]) -> u64 {
    value[0].0 ^ value[0].1 ^ value[1].0 ^ value[1].1
}

#[inline(never)]
pub extern "C" fn write_nested_array_fields(value: &mut [(u64, u64); 2], left: u64, right: u64) -> u64 {
    value[0].0 = left ^ 3;
    value[0].1 = right ^ 5;
    value[1].0 = value[0].0 + 7;
    value[1].1 = value[0].1 + 11;
    value[0].0 ^ value[0].1 ^ value[1].0 ^ value[1].1
}
"#;

    let bin_src = r#"
#![no_main]

extern crate rcl2_nested_array_ref_call_args;

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    let array = [(0x10u64, 0x03u64), (0x05u64, 0x30u64)];
    if rcl2_nested_array_ref_call_args::read_nested_array(&array) != (0x10 ^ 0x03 ^ 0x05 ^ 0x30) {
        return 181;
    }

    let mut writable = [(7u64, 11u64), (13u64, 17u64)];
    let observed =
        rcl2_nested_array_ref_call_args::write_nested_array_fields(&mut writable, 8, 30);
    if observed != (11 ^ 27 ^ 18 ^ 38) {
        return 182;
    }
    if rcl2_nested_array_ref_call_args::read_nested_array(&writable) != (11 ^ 27 ^ 18 ^ 38) {
        return 183;
    }

    let copied = &writable;
    if rcl2_nested_array_ref_call_args::read_nested_array(copied) != (11 ^ 27 ^ 18 ^ 38) {
        return 184;
    }

    let copied_array = writable;
    if rcl2_nested_array_ref_call_args::read_nested_array(&copied_array) != (11 ^ 27 ^ 18 ^ 38) {
        return 185;
    }

    0
}
"#;

    assert_backend_library_and_backend_caller_link_and_run(
        "nested_array_reference_call_args",
        lib_src,
        bin_src,
        "rcl2_nested_array_ref_call_args",
    );
}

#[test]
fn single_variant_enum_reference_call_arguments_run_with_backend_compiled_caller() {
    let lib_src = r#"
#![crate_type = "lib"]

#[derive(Clone, Copy)]
pub enum Pair {
    Only { left: u64, right: u64 },
}

#[inline(never)]
pub extern "C" fn read_pair(value: &Pair) -> u64 {
    match *value {
        Pair::Only { left, right } => left ^ right,
    }
}

#[inline(never)]
pub extern "C" fn write_pair(value: &mut Pair, left: u64, right: u64) -> u64 {
    *value = Pair::Only {
        left: left ^ 3,
        right: right ^ 5,
    };
    match *value {
        Pair::Only { left, right } => left ^ right,
    }
}
"#;

    let bin_src = r#"
#![no_main]

extern crate rcl2_enum_ref_call_args;

use rcl2_enum_ref_call_args::Pair;

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    let pair = Pair::Only {
        left: 0x10u64,
        right: 0x03u64,
    };
    if rcl2_enum_ref_call_args::read_pair(&pair) != 19 {
        return 171;
    }

    let mut writable = Pair::Only { left: 7, right: 11 };
    let observed = rcl2_enum_ref_call_args::write_pair(&mut writable, 8, 30);
    if observed != 16 {
        return 172;
    }
    match writable {
        Pair::Only { left, right } => {
            if left != 11 {
                return 173;
            }
            if right != 27 {
                return 174;
            }
        }
    }
    if rcl2_enum_ref_call_args::read_pair(&writable) != 16 {
        return 175;
    }

    let copied = &writable;
    if rcl2_enum_ref_call_args::read_pair(copied) != 16 {
        return 176;
    }

    0
}
"#;

    assert_backend_library_and_backend_caller_link_and_run(
        "enum_reference_call_args",
        lib_src,
        bin_src,
        "rcl2_enum_ref_call_args",
    );
}

#[test]
fn c_like_enum_reassignment_runs_with_backend() {
    let src = r#"
#![no_main]

#[derive(Clone, Copy)]
enum State {
    Idle,
    Busy,
}

#[inline(never)]
fn choose(flag: bool) -> State {
    let mut state = State::Idle;
    if flag {
        state = State::Busy;
    }
    state
}

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    match choose(argc != 0) {
        State::Busy => 0,
        State::Idle => 181,
    }
}
"#;

    assert_backend_source_exits_success("c_like_enum_reassignment", src);
}
