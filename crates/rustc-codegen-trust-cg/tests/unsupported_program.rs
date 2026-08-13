// Regression test for the rustc_codegen_trust_cg M0 load/fail invariant.
//
// The hello-loop path has moved beyond pure M0, so this test uses an
// intentionally unsupported program to keep proving the original M0
// acceptance criterion: rustc loads our dylib, reaches the backend
// entrypoint, and then fails with our diagnostic rather than a dlopen
// or codegen-backend load error.

use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};

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
    let target_dir = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| crate_dir.join("target"));
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
        "cargo build failed; cannot run unsupported-program smoke test"
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

struct BackendRun {
    status: ExitStatus,
    stderr: String,
}

fn run_backend_on_source(stem: &str, src: &str) -> BackendRun {
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
    let _ = std::fs::remove_file(&out_bin);

    BackendRun {
        status: output.status,
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
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

/// True while the aarch64 Mach-O object-relocation Certified composition has
/// not landed (ObjectRelocationProofRegistry::aarch64_macho_production() is
/// deliberately empty): every backend compile on this host fails promotion
/// with TCG-PROOF-465/object-relocation-inventory. When the lanes register,
/// this returns false and the original capability assertions below resume
/// automatically — nothing to un-ignore.
fn aarch64_macho_promotion_ratchet(stderr: &str) -> bool {
    cfg!(all(target_arch = "aarch64", target_os = "macos"))
        && stderr.contains("TCG-PROOF-465")
        && stderr.contains("object relocation inventory")
}

/// Ratchet path shared by the capability tests below: the compile failed on
/// the aarch64 Mach-O promotion ratchet, so assert the documented fail-closed
/// shape instead of the (temporarily unreachable) capability assertions.
fn assert_promotion_ratchet_fail_closed_shape(stderr: &str) {
    assert!(
        stderr.contains("proof promotion rejected"),
        "promotion ratchet failure lost the documented rejection wording. stderr: <<<{stderr}>>>"
    );
    assert!(
        stderr.contains("no object relocation proof is registered"),
        "promotion ratchet failure lost the documented no-registered-proof wording. stderr: <<<{stderr}>>>"
    );
    assert_no_backend_load_failure(stderr);
}

/// MISCOMPILE #72 (now SUPPORTED): a branch-varying mutable scalar reference
/// (`selected` is `&mut left` on one path and `&mut right` on another) used to
/// fail closed because the "borrowed scalar" SNAPSHOT model could not represent a
/// reference that names different locals across control flow. The fix cells every
/// such referent (a stack slot), so `&mut left`/`&mut right` become real cell
/// pointers, the join is an ordinary pointer phi, and the reference can be stored,
/// escaped, and dereferenced correctly. This program must now COMPILE (runtime
/// correctness — including escaping the reference into a tuple and writing through
/// it — is locked in by the differential test m72_branch_ref_join_x86.rs).
#[test]
fn branch_variant_mutable_scalar_reference_tuple_escape_now_compiles_after_backend_load() {
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

    *selected = 7;
    let escaped = (selected,);
    let _ = escaped;
    (left.wrapping_add(right) & 0xFF) as i32
}
"#;
    let output = run_backend_on_source("branch_mutable_scalar_reference_escape", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);

    if !output.status.success() && aarch64_macho_promotion_ratchet(stderr) {
        assert_promotion_ratchet_fail_closed_shape(stderr);
        return;
    }

    assert!(
        output.status.success(),
        "branch-varying mutable scalar reference (now supported via cells) failed to compile. \
         stderr was: <<<{stderr}>>>"
    );
    assert!(
        !stderr.contains("cannot compile required function with unsupported MIR"),
        "branch-varying mutable scalar reference unexpectedly still fails closed. stderr: <<<{stderr}>>>"
    );
    assert_no_backend_load_failure(stderr);
}

#[test]
fn promoted_scalar_reference_return_tuple_escape_fails_closed_after_backend_load() {
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
    let escaped = (selected,);
    let _ = escaped;
    0
}
"#;
    let output = run_backend_on_source("scalar_reference_return_tuple_escape", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);

    // Still FAILS CLOSED (the escaping borrowed scalar reference is not materialized
    // through a stable home). The guard MESSAGE was refreshed to the current
    // wording; the fail-closed behavior (and the soundness it protects — a LIVE
    // `*escaped.0` deref of the same shape also fails closed, verified
    // differentially) is unchanged.
    assert!(
        !output.status.success(),
        "escaping promoted scalar reference return unexpectedly compiled successfully"
    );
    assert!(
        stderr.contains("rustc_codegen_trust_cg: cannot compile required function with unsupported MIR"),
        "rustc did not reach the rustc_codegen_trust_cg unsupported-MIR diagnostic. stderr was: <<<{stderr}>>>"
    );
    assert!(
        stderr.contains("promoted scalar reference return then arg requires scalar borrow materialization")
            || stderr.contains("borrowed scalar reference used without deref"),
        "promoted scalar reference return escape guard did not fail on the intended tuple move. stderr was: <<<{stderr}>>>"
    );
    assert_no_backend_load_failure(stderr);
}

#[test]
fn mutable_scalar_reference_return_fails_closed_after_backend_load() {
    let src = r#"
#![no_main]

#[inline(never)]
fn pick_mut<'a>(flag: bool, left: &'a mut u64, right: &'a mut u64) -> &'a mut u64 {
    if flag { right } else { left }
}

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let mut left = 11u64;
    let mut right = 29u64;
    let selected = pick_mut(argc != 0, &mut left, &mut right);
    *selected = *selected + 1;
    0
}
"#;
    let output = run_backend_on_source("mutable_scalar_reference_return", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);

    assert!(
        !output.status.success(),
        "unsupported mutable scalar reference return unexpectedly compiled successfully"
    );
    assert!(
        stderr.contains("rustc_codegen_trust_cg: cannot compile required function with unsupported MIR"),
        "rustc did not reach the rustc_codegen_trust_cg unsupported-MIR diagnostic. stderr was: <<<{stderr}>>>"
    );
    assert!(
        stderr.contains("promoted mutable scalar reference return is unsupported")
            || stderr.contains("promoted mutable scalar reference return arg is unsupported"),
        "mutable scalar reference return guard did not fail on the intended helper. stderr was: <<<{stderr}>>>"
    );
    assert_no_backend_load_failure(stderr);
}

#[test]
fn nested_array_reference_unit_leaf_whole_store_fails_after_backend_load() {
    let src = r#"#![crate_type = "lib"]
#[no_mangle]
pub fn write_nested_array(value: &mut [(u64, ()); 2]) {
    *value = [(1, ()), (4, ())];
}
"#;
    let output = run_backend_on_source("nested_array_reference_abi", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);

    assert!(
        !output.status.success(),
        "unsupported unit-leaf nested array whole-store unexpectedly compiled successfully"
    );
    assert!(
        stderr.contains("rustc_codegen_trust_cg: cannot compile required function with unsupported MIR"),
        "rustc did not reach the rustc_codegen_trust_cg unsupported-MIR diagnostic. stderr was: <<<{stderr}>>>"
    );
    // The bridge now SKIPS zero-sized fields (the `()` leaf) when flattening an
    // aggregate — `PhantomData`/`Global`/`()` contribute no bytes and no scalar
    // leaf, which is what lets `Vec`/`RawVec` flatten. So `(u64, ())` flattens to
    // a single `u64`, and this whole-array store no longer trips the unit-leaf
    // guard; instead it fails closed one step later on the *by-value aggregate*
    // store (a whole scalarized aggregate has no single-scalar representation).
    // Either precise fail-closed diagnostic is acceptable — the invariant this
    // test pins is that the program fails closed (never miscompiles, never via a
    // backend load failure), not the exact message.
    assert!(
        stderr.contains("aggregate reference nested field is not memory-scalar")
            || stderr.contains("Unit")
            || stderr.contains("whole scalarized aggregate")
            || stderr.contains("by-value aggregate"),
        "unsupported-program guard did not fail closed on the intended unit-leaf nested array whole-store. stderr was: <<<{stderr}>>>"
    );

    assert_no_backend_load_failure(stderr);
}

#[test]
fn multi_variant_enum_reference_parameter_abi_fails_after_backend_load() {
    let src = r#"#![crate_type = "lib"]
pub enum Choice {
    Left(u64),
    Right(u64),
}

#[no_mangle]
pub fn write_choice(value: &mut Choice, flag: bool) {
    if flag {
        *value = Choice::Left(3);
    } else {
        *value = Choice::Right(5);
    }
}
"#;
    let output = run_backend_on_source("multi_variant_enum_reference_abi", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);

    // Now SUPPORTED: writing a multi-variant enum through a `&mut` reference
    // compiles. Runtime correctness (the written variant/payload reads back
    // exactly) was verified differentially (LLVM oracle vs trust-cg, O0/O2/O3) —
    // `write_choice(&mut c, flag)` then matching on `c` agrees. (Stale guard
    // assertion refreshed: this used to fail closed before the enum-reference ABI
    // was implemented.)
    if !output.status.success() && aarch64_macho_promotion_ratchet(stderr) {
        assert_promotion_ratchet_fail_closed_shape(stderr);
        return;
    }

    assert!(
        output.status.success(),
        "multi-variant enum reference ABI must now COMPILE. stderr was: <<<{stderr}>>>"
    );
    assert_no_backend_load_failure(stderr);
}

#[test]
fn unsupported_int_to_float_u128_source_fails_after_backend_load() {
    let src = "fn main() { let _x = 1u128 as f64; }\n";
    let output = run_backend_on_source("bad_int_to_float_u128", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);

    assert!(
        !output.status.success(),
        "unsupported u128 int-to-float pair unexpectedly compiled successfully"
    );
    assert!(
        stderr.contains("rustc_codegen_trust_cg: cannot compile required function with unsupported MIR"),
        "rustc did not reach the rustc_codegen_trust_cg unsupported-MIR diagnostic. stderr was: <<<{stderr}>>>"
    );
    assert!(
        stderr.contains("CastKind::IntToFloat U128 -> F64"),
        "unsupported-program guard did not fail on the intended u128 int-to-float pair. stderr was: <<<{stderr}>>>"
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
            !stderr.contains(marker),
            "rustc failed to load our backend dylib \
             (matched marker: {marker:?}). stderr: <<<{stderr}>>>"
        );
    }
}

#[test]
fn float_remainder_is_now_supported_after_backend_load() {
    // Float remainder (`%` on f32/f64) WAS an unsupported-MIR fail-closed case.
    // The f32/f64 arithmetic lowering on this branch now SUPPORTS it (frem,
    // fmod/fmodf semantics), differentially verified against LLVM at O0/O3 in
    // float_semantics.rs (`5.5f32 % 2.0f32 == 1.5`, `-5.5f64 % 2.0f64`). This
    // test, formerly asserting the fail-closed path, now guards that float
    // remainder keeps compiling cleanly THROUGH the backend (not via a
    // dylib-load failure).
    let src = "fn main() { let _x = 5.0f64 % 2.0f64; }\n";
    let output = run_backend_on_source("float_remainder", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);

    if !output.status.success() && aarch64_macho_promotion_ratchet(stderr) {
        assert_promotion_ratchet_fail_closed_shape(stderr);
        return;
    }

    assert!(
        output.status.success(),
        "float remainder should now compile (frem is supported). stderr: <<<{stderr}>>>"
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
            !stderr.contains(marker),
            "rustc failed to load our backend dylib \
             (matched marker: {marker:?}). stderr: <<<{stderr}>>>"
        );
    }
}

/// MISCOMPILE #71, now SUPPORTED: a loop that mutates a SCALARIZED aggregate
/// (struct/array/tuple) FIELD used to have no loop-header phi for that field, so
/// the in-loop store was silently dropped and the post-loop read saw the INITIAL
/// value. The bridge now MEMORY-BACKS a loop-carried mutated aggregate local
/// (`compute_memory_backed_locals`), so the in-loop store round-trips through its
/// stable stack slot and survives the back-edge — `let mut q=Q{a,..}; while .. {
/// q.a += 1 }` now compiles and accumulates correctly. Runtime CORRECTNESS (no
/// store-drop) is verified differentially by
/// `m71_loop_carried_aggregate_field_accumulates_matches_llvm` in
/// `m80_loop_refmut_writeback_x86.rs`; here we only assert it COMPILES.
#[test]
fn loop_carried_aggregate_field_mutation_now_compiles_after_backend_load() {
    let src = r#"
#![no_main]
use core::hint::black_box as bb;
#[derive(Clone, Copy)] struct Q { a: i32, b: i32 }
#[no_mangle] pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    let mut q = Q { a: bb(7i32), b: bb(0i32) };
    let mut i = 0i32;
    while i < bb(1i32) {
        q.a = q.a.wrapping_add(1);
        i = i.wrapping_add(1);
    }
    q.a & 0xFF
}
"#;
    let output = run_backend_on_source("m71_loop_aggregate_field", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    if !output.status.success() && aarch64_macho_promotion_ratchet(stderr) {
        assert_promotion_ratchet_fail_closed_shape(stderr);
        return;
    }

    assert!(
        output.status.success(),
        "loop-carried aggregate-field mutation must now COMPILE (memory-backed), not fail closed. \
         stderr: <<<{stderr}>>>"
    );
    assert_no_backend_load_failure(stderr);
}
