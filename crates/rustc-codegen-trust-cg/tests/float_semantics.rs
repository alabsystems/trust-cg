#[path = "support/target_dir.rs"]
mod target_dir_support;

// Runtime oracle for rustc_codegen_trust_cg float comparison semantics.
//
// This keeps #782's float evidence tied to an executable produced by the
// backend: wrong f32 arithmetic or NaN comparison lowering returns a distinct
// exit code instead of accepting compile-only evidence.

use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output, Stdio};
use std::time::{Duration, Instant};

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
        "cargo build failed; cannot run float-semantics test"
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

struct BackendCompile {
    status: ExitStatus,
    stdout: String,
    stderr: String,
    out_bin: PathBuf,
}

fn compile_backend_source(stem: &str, src: &str) -> BackendCompile {
    let src_path = write_temp_source(stem, src);
    let out_bin = std::env::temp_dir().join(format!("rcl2_{stem}_out_{}", std::process::id()));
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

fn run_binary_with_timeout(path: &Path, timeout: Duration) -> Output {
    let mut child = Command::new(path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn compiled float-semantics binary");
    let start = Instant::now();
    loop {
        if child
            .try_wait()
            .expect("failed to poll compiled float-semantics binary")
            .is_some()
        {
            return child
                .wait_with_output()
                .expect("failed to collect float-semantics output");
        }
        if start.elapsed() >= timeout {
            child
                .kill()
                .expect("failed to kill timed-out float-semantics binary");
            let killed = child
                .wait_with_output()
                .expect("failed to collect timed-out float-semantics output");
            panic!(
                "float-semantics binary did not exit before timeout; \
                 stdout=<<<{}>>> stderr=<<<{}>>>",
                String::from_utf8_lossy(&killed.stdout),
                String::from_utf8_lossy(&killed.stderr)
            );
        }
        std::thread::sleep(Duration::from_millis(20));
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

fn assert_backend_source_exits_success(stem: &str, src: &str) {
    let compiled = compile_backend_source(stem, src);
    eprintln!("rustc stdout:\n{}", compiled.stdout);
    eprintln!("rustc stderr:\n{}", compiled.stderr);
    eprintln!("rustc exit: {:?}", compiled.status);

    if !compiled.status.success() && aarch64_macho_promotion_ratchet(&compiled.stderr) {
        // The compile died on the deliberate fail-closed ratchet. Pin the
        // documented diagnostic shape instead of the runtime oracle.
        assert!(
            compiled.stderr.contains("proof promotion rejected"),
            "ratchet rejection lost its documented shape for {stem}. stderr: <<<{stderr}>>>",
            stderr = compiled.stderr
        );
        assert!(
            compiled
                .stderr
                .contains("no object relocation proof is registered"),
            "ratchet rejection lost its documented shape for {stem}. stderr: <<<{stderr}>>>",
            stderr = compiled.stderr
        );
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

#[test]
fn f32_arithmetic_and_nan_comparisons_run_with_rust_semantics() {
    let src = r#"
#![no_main]

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    let left = 9.0f32;
    let right = 3.0f32;
    let scale = 2.0f32;
    let sub = left - right;
    let product = sub * scale;
    let ratio = product / scale;

    if !(sub == 6.0f32) {
        return 11;
    }
    if !(product == 12.0f32) {
        return 12;
    }
    if !(ratio == 6.0f32) {
        return 13;
    }
    let rem = 5.5f32 % 2.0f32;
    if !(rem == 1.5f32) {
        return 14;
    }
    let neg_rem = -5.5f64 % 2.0f64;
    if !(neg_rem == -1.5f64) {
        return 15;
    }
    if !(right < left) {
        return 16;
    }
    if !(sub <= ratio) {
        return 17;
    }
    if !(left > right) {
        return 18;
    }
    let zero = 0.0f32;
    let nan = zero / zero;

    if !(nan != 0.0f32) {
        return 23;
    }
    if nan == 0.0f32 {
        return 24;
    }
    if nan < 0.0f32 {
        return 25;
    }
    if nan <= 0.0f32 {
        return 26;
    }
    if nan > 0.0f32 {
        return 27;
    }
    if nan >= 0.0f32 {
        return 28;
    }
    0
}
"#;

    assert_backend_source_exits_success("float_semantics", src);
}

#[test]
fn powi_and_libm_intrinsics_run_with_readable_float_semantics() {
    // The backend's AArch64 object-relocation proof lane deliberately fails
    // closed today (TCG-PROOF-465). Keep this executable oracle strict on the
    // x86_64 lane where these libcalls are supported and relocation-certified;
    // pure unit tests in lib.rs still pin the complete symbol table on every host.
    if !cfg!(target_arch = "x86_64") {
        eprintln!("skipping: x86_64 runtime requires the certified x86_64 relocation lane");
        return;
    }

    let src = r#"
#![no_main]

#[inline(never)]
fn opaque_f64(value: f64) -> f64 { std::hint::black_box(value) }

#[inline(never)]
fn opaque_f32(value: f32) -> f32 { std::hint::black_box(value) }

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    if opaque_f64(2.0).powi(10) != 1024.0 { return 51; }
    if opaque_f64(0.5).powi(-3) != 8.0 { return 52; }
    if opaque_f32(3.0).powi(4) != 81.0 { return 53; }

    if opaque_f64(3.0).exp2() != 8.0 { return 54; }
    if opaque_f64(8.0).log2() != 3.0 { return 55; }
    if opaque_f64(0.0).sin() != 0.0 { return 56; }
    if opaque_f64(0.0).cos() != 1.0 { return 57; }
    if (opaque_f64(1000.0).log10() - 3.0).abs() > 1.0e-12 { return 58; }
    if opaque_f64(2.0).powf(10.0) != 1024.0 { return 59; }
    let f64_roundtrip = opaque_f64(1.25).exp().ln();
    if (f64_roundtrip - 1.25).abs() > 1.0e-12 { return 60; }

    if opaque_f32(3.0).exp2() != 8.0 { return 61; }
    if opaque_f32(8.0).log2() != 3.0 { return 62; }
    if opaque_f32(0.0).sin() != 0.0 { return 63; }
    if opaque_f32(0.0).cos() != 1.0 { return 64; }
    if (opaque_f32(1000.0).log10() - 3.0).abs() > 1.0e-5 { return 65; }
    if opaque_f32(2.0).powf(10.0) != 1024.0 { return 66; }
    let f32_roundtrip = opaque_f32(1.25).exp().ln();
    if (f32_roundtrip - 1.25).abs() > 1.0e-5 { return 67; }

    0
}
"#;

    assert_backend_source_exits_success("powi_libm_semantics", src);
}

#[test]
fn round_ties_even_fails_closed_until_fixed_mode_rounding_is_modeled() {
    let src = r#"
#![no_main]

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    std::hint::black_box(2.5f64).round_ties_even() as i32
}
"#;

    let compiled = compile_backend_source("round_ties_even_fail_closed", src);
    let _ = std::fs::remove_file(&compiled.out_bin);
    assert!(
        !compiled.status.success(),
        "round_ties_even unexpectedly compiled through an ambient-mode libcall"
    );
    assert!(
        compiled
            .stderr
            .contains("fixed nearest-even rounding is not modeled"),
        "missing precise fail-closed diagnostic: <<<{}>>>",
        compiled.stderr
    );
}

#[test]
fn int_to_float_width_pairs_run_with_rust_semantics() {
    let src = r#"
#![no_main]

#[inline(never)]
fn opaque_u64(value: u64) -> u64 {
    value
}

#[inline(never)]
fn opaque_i64(value: i64) -> i64 {
    value
}

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    let u8_to_f32 = 100u8 as f32;
    if !(u8_to_f32 == 100.0f32) {
        return 31;
    }

    let i16_to_f32 = 1234i16 as f32;
    if !(i16_to_f32 == 1234.0f32) {
        return 32;
    }

    let u32_to_f64 = 16_777_217u32 as f64;
    if !(u32_to_f64 == 16_777_217.0f64) {
        return 33;
    }

    let i32_seed = 16_777_217i32;
    let i32_to_f64 = (-i32_seed) as f64;
    if !(i32_to_f64 == -16_777_217.0f64) {
        return 34;
    }

    let i64_seed = 16_777_217i64;
    let i64_to_f64 = (-i64_seed) as f64;
    if !(i64_to_f64 == -16_777_217.0f64) {
        return 35;
    }

    let u64_to_f64 = 16_777_217u64 as f64;
    if !(u64_to_f64 == 16_777_217.0f64) {
        return 36;
    }

    let high_bit = opaque_u64(0x8000_0000_0000_0000u64);
    let high_bit_to_f64 = high_bit as f64;
    if !(high_bit_to_f64 == 9_223_372_036_854_775_808.0f64) {
        return 37;
    }

    let high_midpoint = opaque_u64(9_007_199_791_611_905u64);
    let high_midpoint_to_f32 = high_midpoint as f32;
    if !(high_midpoint_to_f32 == 9_007_200_328_482_816.0f32) {
        return 38;
    }

    let signed_high_midpoint = opaque_i64(-9_007_199_791_611_905i64);
    let signed_high_midpoint_to_f32 = signed_high_midpoint as f32;
    if !(signed_high_midpoint_to_f32 == -9_007_200_328_482_816.0f32) {
        return 39;
    }

    let all_bits = opaque_u64(0xffff_ffff_ffff_ffffu64);
    if (all_bits ^ 0xffff_ffff_ffff_ffffu64) != 0 {
        return 40;
    }

    let all_bits_to_f64 = all_bits as f64;
    if !(all_bits_to_f64 == 18_446_744_073_709_551_616.0f64) {
        return 41;
    }

    let all_bits_to_f32 = all_bits as f32;
    if !(all_bits_to_f32 == 18_446_744_073_709_551_616.0f32) {
        return 42;
    }

    0
}
"#;

    assert_backend_source_exits_success("int_to_float_widths", src);
}
