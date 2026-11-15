//! Toolchain selection shared by the bridge integration tests.
//!
//! Tests use the compiler that built the backend, recorded by `build.rs`.
//! This avoids loading a pack-built dylib into a different rustup-linked compiler.
//! Two things differ once the selected channel is `trust`
//! (the Trust toolchain) rather than a stock nightly:
//!
//!   * the compiler driver: `rustc` is only a compatibility alias in a Trust
//!     sysroot and its frontend policy may differ from the branded driver, so
//!     the tests invoke `trustc` there — and `rustc` on a stock channel;
//!   * the build tool: the toolchain's `cargo` IS Trust's `targo`, whose
//!     default lane verifies the crate and refuses to build an implicitly
//!     unverified artifact. The backend dylib is therefore built with
//!     `targo --unverified build`, the single human-visible opt-out (it prints
//!     an UNVERIFIED banner; nothing in these tests makes a proof claim).
//!
//! The Trust frontend also verifies every compiled crate by default and fails
//! closed on unproved obligations (`Trust strict verification failed …`).
//! These tests are codegen differentials, not verification runs, so
//! [`rustc_command`] passes the compiler's off-switch `-Ztrust-verify=off` on
//! the trust channel. It is applied HERE ONLY, and to every compile the tests
//! issue — the trust-cg side and the LLVM oracle side alike — so the
//! differential stays apples-to-apples. The backend itself never passes it.
//!
//! Every function keeps the stock-channel path intact for the day the pin
//! moves again: the `trust` branch is taken only when the channel IS `trust`.

use std::path::Path;
use std::process::Command;

include!(concat!(env!("OUT_DIR"), "/test_build_compiler.rs"));

/// The channel name under which `rust-toolchain.toml` pins the Trust toolchain.
pub const TRUST_CHANNEL: &str = "trust";

/// The channel pinned by this crate's `rust-toolchain.toml`.
#[allow(dead_code)]
pub fn pinned_toolchain() -> String {
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

/// Whether `channel` is the Trust toolchain (see the module doc).
pub fn is_trust_channel(channel: &str) -> bool {
    channel == TRUST_CHANNEL
}

/// The exact build compiler with no additional flags, for sysroot queries.
#[allow(dead_code)]
pub fn rustc_driver_command() -> Command {
    Command::new(BUILD_COMPILER)
}

/// The compiler invocation every test compile starts from:
/// The build compiler with `--edition=2021`, plus `-Ztrust-verify=off`
/// on the trust channel (see the module doc). Both the trust-cg compile and
/// the LLVM oracle compile of a differential MUST start from this one
/// constructor so the two sides see identical frontend policy.
#[allow(dead_code)]
pub fn rustc_command() -> Command {
    rustc_command_with_edition("2021")
}

/// Select one edition when constructing the shared differential command.
/// Appending a second edition to `rustc_command()` is rejected by rustc.
#[allow(dead_code)]
pub fn rustc_command_with_edition(edition: &str) -> Command {
    let mut cmd = rustc_driver_command();
    cmd.arg(format!("--edition={edition}"));
    if is_trust_channel(&pinned_toolchain()) {
        cmd.arg("-Ztrust-verify=off");
    }
    cmd
}

/// The command that builds this crate's backend dylib from `crate_dir` (the
/// `ensure_dylib_built` fallback; cargo/targo normally built it already as a
/// byproduct of running the tests): `rustup run <channel> cargo build` on a stock
/// channel, the build compiler pack's `targo --unverified build` on Trust.
#[allow(dead_code)]
pub fn backend_build_command(crate_dir: &Path, release: bool) -> Command {
    let channel = pinned_toolchain();
    let mut cmd = if is_trust_channel(&channel) {
        let compiler = Path::new(BUILD_COMPILER);
        let targo = compiler.parent().expect("compiler directory").join("targo");
        let mut cmd = Command::new(targo);
        cmd.args(["--unverified", "build"]);
        cmd
    } else {
        let mut cmd = Command::new("rustup");
        cmd.args(["run", channel.as_str(), "cargo", "build"]);
        cmd
    };
    if release {
        cmd.arg("--release");
    }
    cmd.current_dir(crate_dir).env("RUSTC", BUILD_COMPILER);
    cmd
}

/// Whether the `rust-std` for `target` is available to the pinned channel.
///
/// On a stock channel this is rustup's own answer (`rustup target list
/// --installed --toolchain <channel>`). rustup REJECTS that query for a
/// linked custom toolchain (`invalid toolchain name: 'trust'`), which used to
/// make every test skip as "rust-std not installed" — even for the host
/// target the sysroot ships. On the trust channel the sysroot is therefore
/// asked directly: `<driver --print sysroot>/lib/rustlib/<target>/lib` is the
/// directory rustc itself loads the target's `std` from.
#[allow(dead_code)]
pub fn target_std_available(target: &str) -> bool {
    let channel = pinned_toolchain();
    if !is_trust_channel(&channel) {
        let output = Command::new("rustup")
            .args(["target", "list", "--installed", "--toolchain"])
            .arg(&channel)
            .output();
        return match output {
            Ok(output) => String::from_utf8_lossy(&output.stdout)
                .lines()
                .any(|line| line.trim() == target),
            Err(_) => false,
        };
    }
    let Ok(output) = rustc_driver_command().args(["--print", "sysroot"]).output() else {
        return false;
    };
    if !output.status.success() {
        return false;
    }
    let sysroot = String::from_utf8_lossy(&output.stdout).trim().to_owned();
    Path::new(&sysroot)
        .join("lib")
        .join("rustlib")
        .join(target)
        .join("lib")
        .is_dir()
}

/// The tracked option that carries this backend's operator knobs.
///
/// The backend used to take them as `TCG_*` / `TRUST_CG_*` environment
/// variables. trustc refuses that whole prefix family as untracked
/// semantic/codegen controls — an environment variable is not in the crate hash,
/// so a knob that changes emitted code or the evidence attached to it would make
/// incremental reuse and provenance lie — and names this option as the
/// replacement. Tests therefore pass knobs HERE, never in the child's
/// environment.
#[allow(dead_code)]
pub const BACKEND_KNOBS_OPTION: &str = "-Ztrust-ir-cg-args";

/// Build the `-Ztrust-ir-cg-args=...` argument for `knobs`.
///
/// The option is a whitespace-separated list of `key` / `key=value` items, so a
/// knob value containing whitespace cannot be spelled; no knob these tests use
/// takes one.
#[allow(dead_code)]
pub fn backend_knobs_arg(knobs: &[&str]) -> String {
    assert!(
        !knobs.is_empty(),
        "backend_knobs_arg with no knobs would pass an empty value, which rustc rejects"
    );
    for knob in knobs {
        assert!(
            !knob.chars().any(char::is_whitespace),
            "knob {knob:?} contains whitespace; the option is whitespace-separated"
        );
    }
    format!("{BACKEND_KNOBS_OPTION}={}", knobs.join(" "))
}

/// Does the build compiler carry [`BACKEND_KNOBS_OPTION`]?
///
/// `-Z help` is the compiler's own list of unstable options, so this asks the
/// compiler rather than inferring from a version. A test that needs a knob must
/// SKIP when the answer is `false`: the option is a Trust addition, and on a
/// compiler without it the knob cannot be expressed at all — reporting a failure
/// would blame the test for the toolchain.
#[allow(dead_code)]
pub fn backend_knobs_supported() -> bool {
    use std::sync::OnceLock;
    static SUPPORTED: OnceLock<bool> = OnceLock::new();
    *SUPPORTED.get_or_init(|| {
        let Ok(output) = rustc_driver_command().arg("-Zhelp").output() else {
            return false;
        };
        if !output.status.success() {
            return false;
        }
        // `-Z help` prints one `name=val -- description` row per option.
        let listing = String::from_utf8_lossy(&output.stdout);
        listing.contains(&format!(
            "{}=",
            BACKEND_KNOBS_OPTION.trim_start_matches("-Z")
        ))
    })
}

/// Skip honestly when the build compiler has no [`BACKEND_KNOBS_OPTION`].
///
/// Returns `true` when the caller must `return` immediately, after printing the
/// reason. An unexpressible knob is a toolchain fact, not a defect in the code
/// under test, and a silent pass would hide that the assertion never ran.
#[allow(dead_code)]
pub fn skip_without_backend_knobs(test: &str) -> bool {
    if backend_knobs_supported() {
        return false;
    }
    eprintln!(
        "{test}: SKIPPED — this build compiler has no `{BACKEND_KNOBS_OPTION}`, so the backend \
         knob this test needs cannot be expressed (the knobs' former `TCG_*` environment \
         variables are refused outright). Build against a compiler that lists \
         `{}=` in `trustc -Z help`.",
        BACKEND_KNOBS_OPTION.trim_start_matches("-Z")
    );
    true
}
