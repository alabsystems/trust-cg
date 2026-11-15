//! Invalid operator budgets must produce rustc diagnostics before publication,
//! not backend panics or internal compiler errors.

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::path::PathBuf;
use std::process::Output;
use std::sync::atomic::{AtomicU64, Ordering};

/// The two positive-integer execution budgets, as KNOB keys.
///
/// They used to be the environment variables `TCG_PROOF_WALK_WORKERS` and
/// `TRUST_CG_MAX_PARALLELISM`. trustc refuses that whole prefix family as
/// untracked semantic/codegen controls, so they now arrive on the TRACKED
/// `-Ztrust-ir-cg-args` option and the diagnostic names the KNOB key — which is
/// what the operator typed and therefore what a fix has to mention.
const CONTROLS: [&str; 2] = ["proof-walk-workers", "max-parallelism"];

fn backend() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock after epoch")
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "trust-cg-bridge-budget-{}-{unique}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        std::fs::create_dir(&path).expect("create isolated fixture directory");
        std::fs::write(path.join("input.rs"), "pub fn answer() -> u64 { 42 }\n")
            .expect("write fixture source");
        Self(path)
    }

    /// Compile the fixture with both budgets set to a valid `1`, then `key`
    /// overridden to `value`.
    ///
    /// The overriding knob is listed LAST. The backend refuses a repeated knob
    /// outright (two spellings of one knob have no defined precedence), so the
    /// baseline pair is emitted only for the control that is NOT being
    /// overridden — otherwise every call would refuse for the wrong reason and
    /// this test would assert nothing.
    fn compile(&self, key: &str, value: &str) -> Output {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(backend());
        let mut knobs: Vec<String> = CONTROLS
            .iter()
            .filter(|control| **control != key)
            .map(|control| format!("{control}=1"))
            .collect();
        knobs.push(format!("{key}={value}"));
        let knobs: Vec<&str> = knobs.iter().map(String::as_str).collect();
        toolchain_support::rustc_command()
            .arg(backend_arg)
            .arg(toolchain_support::backend_knobs_arg(&knobs))
            .args(["--crate-type=lib", "--emit=metadata"])
            .arg(self.0.join("input.rs"))
            .arg("-o")
            .arg(self.0.join("output.rmeta"))
            .output()
            .expect("invoke pinned rustc with bridge")
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn assert_invalid_budget(key: &str, value: &str) {
    let fixture = Fixture::new();
    let output_path = fixture.0.join("output.rmeta");
    let preserved = b"existing artifact must survive budget rejection";
    std::fs::write(&output_path, preserved).expect("write existing output");
    let output = fixture.compile(key, value);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{key}={value:?}: {stderr}");
    assert!(
        stderr.contains("invalid Trust Codegen execution resource budget"),
        "{stderr}"
    );
    assert!(
        stderr.contains(key),
        "diagnostic must identify {key}: {stderr}"
    );
    assert!(!stderr.contains("panicked"), "{stderr}");
    assert!(!stderr.contains("internal compiler error"), "{stderr}");
    assert_eq!(std::fs::read(output_path).unwrap(), preserved);
}

#[test]
fn malformed_execution_budgets_are_diagnostics_and_preserve_output() {
    if toolchain_support::skip_without_backend_knobs("execution_budget") {
        return;
    }
    for key in CONTROLS {
        for value in [
            "",
            "0",
            "bad",
            "-1",
            "999999999999999999999999999999999999999",
        ] {
            assert_invalid_budget(key, value);
        }
    }
}

/// A non-Unicode budget must never reach the backend, and must never clobber an
/// existing artifact.
///
/// WHAT THIS USED TO ASSERT, and why it could not survive verbatim. It handed
/// the backend a non-Unicode `OsStr` through `TCG_PROOF_WALK_WORKERS` /
/// `TRUST_CG_MAX_PARALLELISM` and required a clean DIAGNOSTIC — specifically
/// `!stderr.contains("panicked")`. Those variables are now refused outright as
/// untracked semantic/codegen controls and the budgets arrive on
/// `-Ztrust-ir-cg-args`, which is command-line text.
///
/// A non-Unicode COMMAND-LINE ARGUMENT never reaches rustc's option parsing at
/// all: the driver decodes its own argv with `std::env::args()`, which panics by
/// contract on a non-Unicode argument. Measured on trustc 8b50cbcc5b, all three
/// of `-Ztrust-ir-cg-args=proof-walk-workers=\xff`, an unrelated
/// `-Cmetadata=\xff`, and a bare `\xff.rs` source path exit 101 with the same
/// `library/std/src/env.rs` panic. That is upstream driver behaviour for every
/// flag, not something the backend's budget parsing can observe or change, so
/// asserting "not a panic" here would be asserting a fact about rustc that is
/// false.
///
/// What is still true, still about this backend, and still worth pinning is
/// asserted below: the compile fails, the BACKEND's own budget diagnostic never
/// appears (it never ran), no ICE is reported, and the pre-existing output file
/// is byte-identical afterwards. The "malformed budget is a diagnostic, never a
/// panic" property itself is unchanged and still covered — by
/// `malformed_execution_budgets_are_diagnostics_and_preserve_output`, over every
/// malformed value the option CAN carry.
#[cfg(unix)]
#[test]
fn non_unicode_execution_budgets_never_reach_the_backend() {
    use std::os::unix::ffi::OsStrExt;
    if toolchain_support::skip_without_backend_knobs("execution_budget") {
        return;
    }
    for key in CONTROLS {
        let fixture = Fixture::new();
        let output_path = fixture.0.join("output.rmeta");
        let preserved = b"existing artifact must survive budget rejection";
        std::fs::write(&output_path, preserved).expect("write existing output");

        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(backend());
        let mut knob_arg = std::ffi::OsString::from(format!(
            "{}={key}=",
            toolchain_support::BACKEND_KNOBS_OPTION
        ));
        knob_arg.push(std::ffi::OsStr::from_bytes(b"\xff"));
        let output = toolchain_support::rustc_command()
            .arg(backend_arg)
            .arg(knob_arg)
            .args(["--crate-type=lib", "--emit=metadata"])
            .arg(fixture.0.join("input.rs"))
            .arg("-o")
            .arg(&output_path)
            .output()
            .expect("invoke pinned rustc with bridge");

        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !output.status.success(),
            "{key}: an unrepresentable budget must not produce a successful compile: {stderr}"
        );
        assert!(
            !stderr.contains("invalid Trust Codegen execution resource budget"),
            "{key}: the backend must never have run, so its budget diagnostic must be absent: \
             {stderr}"
        );
        assert!(!stderr.contains("internal compiler error"), "{stderr}");
        assert_eq!(std::fs::read(&output_path).unwrap(), preserved);
    }
}

#[test]
fn valid_execution_budgets_allow_metadata_output() {
    if toolchain_support::skip_without_backend_knobs("execution_budget") {
        return;
    }
    let fixture = Fixture::new();
    // `" 1 "` — the padded value this used to pass — cannot be spelled on the
    // option at all: `-Z` list values are whitespace-separated, so the padding
    // would split the knob into three items. The parser still trims (the
    // environment path shares it); what changed is that no caller can produce an
    // untrimmed value here.
    let output = fixture.compile(CONTROLS[0], "1");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        std::fs::metadata(fixture.0.join("output.rmeta"))
            .unwrap()
            .len()
            > 0
    );
}
