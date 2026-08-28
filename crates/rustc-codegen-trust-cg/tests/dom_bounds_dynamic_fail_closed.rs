//! Dynamic dominating-bounds identity is deliberately fail-closed.
//!
//! The retired lane compared source-place spellings but did not prove the
//! exact statement interval in the guard/assert endpoint blocks and did not
//! carry provenance for a raw/mutable alias created before that interval. Each
//! adversarial below shrinks a `Vec` after a dynamic guard but before indexing
//! at the old last element. Keeping the legacy check aborts; deleting it reads
//! still-allocated capacity and exits cleanly, a crisp silent-OOB canary.
//!
//! The constant-array control reaches the same OPT-6b recognizer without the
//! dynamic refusal. Its actual elimination remains licensed only by the AY +
//! independent-checker solver lane; solver absence therefore keeps the check
//! and is still a valid control outcome.

#[path = "support/target_dir.rs"]
mod target_dir_support;

use std::path::{Path, PathBuf};
use std::process::Command;

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

fn dylib_name() -> String {
    format!(
        "{}rustc_codegen_trust_cg{}",
        std::env::consts::DLL_PREFIX,
        std::env::consts::DLL_SUFFIX
    )
}

fn ensure_dylib_built() -> PathBuf {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let target_dir = target_dir_support::cargo_target_dir(crate_dir);
    let name = dylib_name();
    for candidate in [
        target_dir.join("release").join(&name),
        target_dir.join("debug").join(&name),
    ] {
        if candidate.exists() {
            return candidate;
        }
    }
    let status = Command::new("cargo")
        .arg(format!("+{}", pinned_toolchain()))
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke cargo build");
    assert!(status.success(), "cargo build failed; cannot run dynamic BCE pins");
    let built = target_dir.join("release").join(&name);
    assert!(built.exists(), "expected backend dylib at {built:?}");
    built
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("trust_cg_dyn_bce_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create dynamic BCE workdir");
    dir
}

enum Outcome {
    Exited(i32),
    Signalled,
}

fn compile_run_traced(stem: &str, source: &str, dylib: &Path) -> (Outcome, String) {
    let dir = workdir(stem);
    let source_path = dir.join("prog.rs");
    std::fs::write(&source_path, source).expect("write dynamic BCE source");
    let binary = dir.join("prog");
    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(dylib);
    let output = Command::new("rustup")
        .env("TCG_BCE_TRACE", "1")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args([
            "--crate-type",
            "bin",
            "-Cpanic=abort",
            "-Coverflow-checks=off",
            "-Ccodegen-units=1",
            "-Copt-level=2",
        ])
        .arg(&backend_arg)
        .arg("-o")
        .arg(&binary)
        .arg(&source_path)
        .output()
        .expect("spawn rustc for dynamic BCE canary");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(output.status.success(), "{stem}: backend compile failed: {stderr}");

    let run = Command::new(&binary).output().expect("run dynamic BCE canary");
    let outcome = match run.status.code() {
        Some(code) => Outcome::Exited(code),
        None => Outcome::Signalled,
    };
    let _ = std::fs::remove_dir_all(&dir);
    (outcome, stderr)
}

const CONSTANT_CONTROL: &str = r#"
use std::hint::black_box as bb;
fn main() {
    let mut a = [0u8; 64];
    let mut i = bb(0usize);
    while i < 64 { a[i] = 1; i += 1; }
    std::process::exit(a.iter().map(|&x| x as i32).sum::<i32>());
}
"#;

// This is the exact h1 shape the dynamic recognizer was introduced for. It
// must still be recognized, but recognition now terminates at the explicit
// authority refusal rather than deleting the bounds check by identity.
const DYNAMIC_RECOGNIZED_CONTROL: &str = r#"
use std::hint::black_box as bb;
fn main() {
    let n = bb(8usize);
    let mut v: Vec<u64> = Vec::new();
    let mut i = 0usize;
    while i < n { v.push((i + 1) as u64); i += 1; }
    let mut acc = 0u64;
    let mut k = 0usize;
    while k < v.len() { acc = acc.wrapping_add(v[k]); k += 1; }
    std::process::exit(acc as i32);
}
"#;

// The length write is deliberately sequenced after the guard value is formed
// but before its branch, targeting the old guard-endpoint scan exemption.
const GUARD_ENDPOINT_WRITE: &str = r#"
use std::hint::black_box as bb;
#[inline(always)] unsafe fn shrink(v: &mut Vec<u8>, n: usize) { unsafe { v.set_len(bb(n)); } }
fn main() {
    let mut v = vec![9u8; bb(8usize)];
    let i = bb(7usize);
    let guarded = i < v.len();
    unsafe { shrink(&mut v, i); }
    if guarded { bb(v[i]); }
    std::process::exit(0);
}
"#;

// The inlined shrink sits on the true-edge/check side, targeting the old
// assert-endpoint scan exemption.
const ASSERT_ENDPOINT_WRITE: &str = r#"
use std::hint::black_box as bb;
#[inline(always)] unsafe fn shrink(v: &mut Vec<u8>, n: usize) { unsafe { v.set_len(bb(n)); } }
fn main() {
    let mut v = vec![11u8; bb(8usize)];
    let i = bb(7usize);
    if i < v.len() {
        unsafe { shrink(&mut v, i); }
        bb(v[i]);
    }
    std::process::exit(0);
}
"#;

// The mutable alias is created before the guard. A scan limited to
// address-taking inside guard..use cannot establish its provenance. This uses
// a supported reference shape rather than `&raw`, which the bridge correctly
// rejects before bounds analysis.
const PREEXISTING_MUT_ALIAS: &str = r#"
use std::hint::black_box as bb;
fn main() {
    let mut v = vec![13u8; bb(8usize)];
    let alias: &mut Vec<u8> = &mut v;
    let i = bb(7usize);
    if i < alias.len() {
        unsafe { alias.set_len(bb(i)); }
        bb(alias[i]);
    }
    std::process::exit(0);
}
"#;

#[test]
fn dynamic_identity_refuses_endpoint_and_alias_hazards() {
    if !matches!(std::env::consts::ARCH, "aarch64" | "x86_64") {
        eprintln!("skipping: trust-cg host backend is not available for this architecture");
        return;
    }
    let dylib = ensure_dylib_built();

    let (outcome, stderr) = compile_run_traced("constant_control", CONSTANT_CONTROL, &dylib);
    assert!(matches!(outcome, Outcome::Exited(64)));
    assert!(
        stderr.contains("TCG-BCE-DOM fact: Const"),
        "constant control did not reach OPT-6b: {stderr}"
    );
    assert!(!stderr.contains("TCG-BCE-DYN refused"));

    let (outcome, stderr) =
        compile_run_traced("dynamic_recognized_control", DYNAMIC_RECOGNIZED_CONTROL, &dylib);
    assert!(matches!(outcome, Outcome::Exited(36)));
    assert!(
        stderr.contains("TCG-BCE-DOM fact: DynLocal"),
        "dynamic control did not reach OPT-6b: {stderr}"
    );
    assert!(
        stderr.contains(
            "TCG-BCE-DYN refused: statement-position interval and alias provenance are not certified"
        ),
        "recognized dynamic control did not exercise the authority refusal: {stderr}"
    );
    assert!(!stderr.contains("TCG-BCE-DOM fired"));

    for (stem, source) in [
        ("guard_endpoint_write", GUARD_ENDPOINT_WRITE),
        ("assert_endpoint_write", ASSERT_ENDPOINT_WRITE),
    ] {
        let (outcome, stderr) = compile_run_traced(stem, source, &dylib);
        // These high-level hazards may conservatively decline before producing
        // a fact because rustc can place the write/call in a non-endpoint MIR
        // block. Either trace is safe; the recognized control above pins the
        // actual dynamic authority boundary independently.
        assert!(
            stderr.contains("TCG-BCE-DYN refused")
                || stderr.contains("TCG-BCE-DOM bail: no dominating fact"),
            "{stem}: dynamic path neither refused nor conservatively declined: {stderr}"
        );
        assert!(!stderr.contains("TCG-BCE-DOM fired"), "{stem}: {stderr}");
        assert!(
            matches!(outcome, Outcome::Signalled),
            "{stem}: retained bounds check must abort after the Vec shrinks"
        );
    }

    let (outcome, stderr) =
        compile_run_traced("preexisting_mut_alias", PREEXISTING_MUT_ALIAS, &dylib);
    assert!(
        stderr.contains("TCG-BCE-DOM fact: DynLocal"),
        "preexisting alias did not reach the dynamic authority boundary: {stderr}"
    );
    assert!(
        stderr.contains(
            "TCG-BCE-DYN refused: statement-position interval and alias provenance are not certified"
        ),
        "preexisting alias was not rejected by the exact authority refusal: {stderr}"
    );
    assert!(!stderr.contains("TCG-BCE-DOM fired"), "{stderr}");
    assert!(
        matches!(outcome, Outcome::Signalled),
        "preexisting alias: retained bounds check must abort after the Vec shrinks"
    );
}
