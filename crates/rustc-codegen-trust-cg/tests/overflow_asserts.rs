#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Runtime regressions for rustc_codegen_trust_cg debug arithmetic assertions.
//
// Debug arithmetic asserts must not be erased into unchecked arithmetic. These
// oracles compile small programs with `-C overflow-checks=yes` and require the
// produced binaries to either execute the supported integer path or terminate
// unsuccessfully when a dynamic arithmetic precondition fails.

use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output, Stdio};
use std::time::{Duration, Instant};

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
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
    let output = toolchain_support::rustc_command()
        .arg(&backend_arg)
        .args(["-C", "overflow-checks=yes"])
        .arg("-o")
        .arg(&out_bin)
        .arg(&src_path)
        .output()
        .expect("failed to spawn trustc");

    let _ = std::fs::remove_file(&src_path);

    BackendCompile {
        status: output.status,
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        out_bin,
    }
}

fn run_binary_with_timeout(path: &Path, timeout: Duration) -> Option<Output> {
    let mut child = Command::new(path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn compiled overflow-asserts binary");
    let start = Instant::now();
    loop {
        if child
            .try_wait()
            .expect("failed to poll compiled overflow-asserts binary")
            .is_some()
        {
            return Some(
                child
                    .wait_with_output()
                    .expect("failed to collect overflow-asserts output"),
            );
        }
        if start.elapsed() >= timeout {
            child
                .kill()
                .expect("failed to kill timed-out overflow-asserts binary");
            let _ = child
                .wait_with_output()
                .expect("failed to collect timed-out overflow-asserts output");
            return None;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

fn assert_no_backend_load_failure(stderr: &str) {
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
            !stderr.contains(marker),
            "rustc failed to load our backend dylib \
             (matched marker: {marker:?}). stderr: <<<{stderr}>>>"
        );
    }
}

/// Compile the oracle in the default (certificates-on) lane. A refusal of any
/// kind fails here: on aarch64-apple-darwin the object-relocation and
/// opcode-inventory proof-promotion refusals (`[TCG-PROOF-465]`) used to return
/// `None`, and every runtime oracle in this file then passed without running
/// (ledger L06-P10).
fn assert_backend_source_compiles(stem: &str, src: &str) -> BackendCompile {
    let compiled = compile_backend_source(stem, src);
    eprintln!("{stem} rustc stdout:\n{}", compiled.stdout);
    eprintln!("{stem} rustc stderr:\n{}", compiled.stderr);
    eprintln!("{stem} rustc exit: {:?}", compiled.status);

    assert!(
        compiled.status.success(),
        "{stem}: rustc failed to compile arithmetic oracle. stderr was: <<<{stderr}>>>",
        stderr = compiled.stderr
    );
    assert!(
        compiled.out_bin.exists(),
        "{stem}: rustc succeeded but did not produce {:?}",
        compiled.out_bin
    );
    assert_no_backend_load_failure(&compiled.stderr);
    compiled
}

fn assert_backend_source_exits_success(stem: &str, src: &str) {
    let compiled = assert_backend_source_compiles(stem, src);
    // 10s (not 1s): the oracle binary computes instantly, but a freshly-written
    // Mach-O's first exec pays dynamic-linker/Gatekeeper cold-start overhead that
    // can exceed 1s when the test machine is under build/run contention, causing a
    // spurious "timed out" failure even though the binary exits 0. The generous
    // bound only guards against a genuine hang and never weakens the exit-code
    // assertions below.
    let run = run_binary_with_timeout(&compiled.out_bin, Duration::from_secs(10));
    let _ = std::fs::remove_file(&compiled.out_bin);
    let Some(run) = run else {
        panic!("{stem}: arithmetic oracle timed out");
    };

    let run_stdout = String::from_utf8_lossy(&run.stdout);
    let run_stderr = String::from_utf8_lossy(&run.stderr);
    assert!(
        run.status.success(),
        "{stem}: arithmetic oracle failed; stdout=<<<{}>>> stderr=<<<{}>>>",
        run_stdout,
        run_stderr
    );
    assert_eq!(
        run.status.code(),
        Some(0),
        "{stem}: arithmetic oracle exited with a nonzero success-code convention"
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::On,
    );
}

fn assert_backend_source_traps(stem: &str, src: &str, forbidden_success_code: i32) {
    let compiled = assert_backend_source_compiles(stem, src);
    // 10s (not 1s): a trapping binary aborts essentially instantly, but the bound
    // must tolerate cold-start exec overhead under contention so a slow first exec
    // is not mistaken for the binary still running.
    let run = run_binary_with_timeout(&compiled.out_bin, Duration::from_secs(10));
    let _ = std::fs::remove_file(&compiled.out_bin);

    // Killed at the bound, the binary produced no exit status: no trap was
    // observed, and a miscompile that hangs is not a trap. That fails, as it
    // does in `assert_backend_source_exits_success`, and is never recorded as
    // a native run.
    let Some(run) = run else {
        panic!("{stem}: arithmetic oracle timed out after 10s; no trap was observed");
    };
    let run_stdout = String::from_utf8_lossy(&run.stdout);
    let run_stderr = String::from_utf8_lossy(&run.stderr);
    assert!(
        !run.status.success(),
        "{stem}: arithmetic oracle reached the post-assert success path; \
         stdout=<<<{}>>> stderr=<<<{}>>>",
        run_stdout,
        run_stderr
    );
    assert_ne!(
        run.status.code(),
        Some(forbidden_success_code),
        "{stem}: arithmetic oracle followed the unchecked arithmetic path"
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::On,
    );
}

#[test]
fn debug_overflow_assert_traps_instead_of_wrapping() {
    let src = r#"
#![no_main]

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let one = (argc as u64) | 1;
    let wrapped = 18_446_744_073_709_551_615u64 + one;
    if wrapped == 18_446_744_073_709_551_615u64 {
        return 0;
    }
    42
}
"#;

    assert_backend_source_traps("overflow_asserts", src, 42);
}

#[test]
fn integer_div_rem_runtime_oracle_exits_success() {
    let src = r#"
#![no_main]

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let signed_divisor = (argc as i64) | 1;
    let signed_numerator = -49i64 * signed_divisor;
    let signed_quotient = signed_numerator / signed_divisor;
    let signed_remainder = signed_numerator % signed_divisor;

    let unsigned_divisor = (argc as u64) | 1;
    let unsigned_numerator = 250u64 * unsigned_divisor;
    let unsigned_quotient = unsigned_numerator / unsigned_divisor;
    let unsigned_remainder = unsigned_numerator % unsigned_divisor;

    if signed_quotient == -49
        && signed_remainder == 0
        && unsigned_quotient == 250
        && unsigned_remainder == 0
    {
        0
    } else {
        77
    }
}
"#;

    assert_backend_source_exits_success("integer_div_rem", src);
}

#[test]
fn integer_shift_runtime_oracle_exits_success() {
    let src = r#"
#![no_main]

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let shift = (argc as u32) & 7;
    let unsigned_left = 3u64 << shift;
    let unsigned_right = 128u64 >> shift;
    let signed_right = -64i64 >> shift;

    if unsigned_left == 6
        && unsigned_right == 64
        && signed_right == -32
    {
        0
    } else {
        88
    }
}
"#;

    assert_backend_source_exits_success("integer_shift", src);
}

#[test]
fn extern_c_narrow_integer_direct_abi_success() {
    let src = r#"
#![no_main]

#[no_mangle]
pub extern "C" fn add_u8(x: u8, y: u8) -> u8 {
    x.wrapping_add(y)
}

#[no_mangle]
pub extern "C" fn add_i8(x: i8, y: i8) -> i8 {
    x.wrapping_add(y)
}

#[no_mangle]
pub extern "C" fn add_u16(x: u16, y: u16) -> u16 {
    x.wrapping_add(y)
}

#[no_mangle]
pub extern "C" fn add_i16(x: i16, y: i16) -> i16 {
    x.wrapping_add(y)
}

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    if add_u8(250, 5) != 255 {
        return 1;
    }
    if add_i8(-100, 7) != -93 {
        return 2;
    }
    if add_u16(65000, 123) != 65123 {
        return 3;
    }
    if add_i16(-30000, 1234) != -28766 {
        return 4;
    }
    0
}
"#;

    assert_backend_source_exits_success("extern_c_narrow_integer_direct_abi", src);
}

#[test]
fn extern_c_bool_direct_abi_success() {
    let src = r#"
#![no_main]

#[no_mangle]
pub extern "C" fn not_bool(flag: bool) -> bool {
    !flag
}

#[no_mangle]
pub extern "C" fn bool_gate(flag: bool, value: u8) -> u8 {
    if flag {
        value.wrapping_add(1)
    } else {
        value.wrapping_sub(1)
    }
}

#[no_mangle]
pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    if not_bool(false) != true {
        return 1;
    }
    if not_bool(true) != false {
        return 2;
    }
    if bool_gate(true, 41) != 42 {
        return 3;
    }
    if bool_gate(false, 41) != 40 {
        return 4;
    }
    0
}
"#;

    assert_backend_source_exits_success("extern_c_bool_direct_abi", src);
}

#[test]
fn division_by_zero_assert_traps() {
    let src = r#"
#![no_main]

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let divisor = (argc as i64) - (argc as i64);
    let _unchecked_path = 123i64 / divisor;
    42
}
"#;

    assert_backend_source_traps("division_by_zero", src, 42);
}

#[test]
fn remainder_by_zero_assert_traps() {
    let src = r#"
#![no_main]

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let divisor = (argc as u64) - (argc as u64);
    let _unchecked_path = 123u64 % divisor;
    42
}
"#;

    assert_backend_source_traps("remainder_by_zero", src, 42);
}

#[test]
fn shift_left_out_of_range_assert_traps() {
    let src = r#"
#![no_main]

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let too_large = (argc as u32) + 63;
    let _unchecked_path = 1u64 << too_large;
    42
}
"#;

    assert_backend_source_traps("shift_left_out_of_range", src, 42);
}

#[test]
fn shift_right_out_of_range_assert_traps() {
    let src = r#"
#![no_main]

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let too_large = (argc as u32) + 63;
    let _unchecked_path = -1i64 >> too_large;
    42
}
"#;

    assert_backend_source_traps("shift_right_out_of_range", src, 42);
}
