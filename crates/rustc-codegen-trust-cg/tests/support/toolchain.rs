//! Toolchain selection shared by the bridge integration tests.
//!
//! Tests use the compiler that built the backend, recorded by `build.rs`.
//! This avoids loading a pack-built dylib into a different rustup-linked compiler.
//! The pinned channel is `trust` (the Trust toolchain; the retired stock nightly
//! lane is gone): `rustc` is only a compatibility alias in a Trust sysroot and
//! its frontend policy may differ from the branded driver, so the tests invoke
//! `trustc`.
//! The tests never build the backend themselves: each loads the library Cargo
//! built for its own test build (`support/backend_artifact.rs`). On the trust
//! channel that build is `targo --unverified`, whose UNVERIFIED banner is the
//! human-visible opt-out; nothing in these tests makes a proof claim.
//!
//! The Trust frontend also verifies every compiled crate by default and fails
//! closed on unproved obligations (`Trust strict verification failed …`).
//! These tests are codegen differentials, not verification runs, so
//! [`rustc_command`] passes the compiler's off-switch `-Ztrust-verify=off`.
//! It is applied HERE ONLY, and to every compile the tests issue — the
//! trust-cg side and the LLVM oracle side alike — so the differential stays
//! apples-to-apples. The backend itself never passes it.

use std::path::Path;
use std::process::Command;

include!(concat!(env!("OUT_DIR"), "/test_build_compiler.rs"));

/// Whether an undefined symbol of a standalone-linked test object is one of
/// `core`'s DIVERGING runtime helpers, which the differential tests replace with
/// an `abort()` stub so the object links without `libcore` (the fixtures are
/// chosen so these paths never execute).
///
/// Two families: everything spelled `panic` (`core::panicking::panic*`,
/// `panic_bounds_check`, `panic_const::*`, `rust_begin_unwind`), and the
/// `*_fail` / `*_failed` helpers (`slice_index_fail`,
/// `slice_start_index_len_fail`, `unwrap_failed`, `expect_failed`,
/// `assert_failed`, `str_index_overflow_fail`). The second family is what
/// `library/core` since 2026-09 routes every range-index check through
/// (`slice::index::into_slice_range` -> `slice_index_fail`), so a `panic`-only
/// filter left the LLVM oracle of an ordinary `copy_within` fixture unlinkable
/// on the current Trust `core`. A stub that a fixture DID reach would abort the
/// run — a loud signal on either side, never a silently wrong value.
#[allow(dead_code)]
pub fn is_abort_stub_symbol(sym: &str) -> bool {
    sym.contains("panic") || sym.contains("_fail")
}

/// Write `<dir>/abort_stubs.c`: one `abort()` body for every
/// [`is_abort_stub_symbol`] symbol that `objects` reference but none of them
/// define, and return its path for the `cc` link of a C driver.
///
/// A fixture that links backend objects into a C program without `libcore`
/// needs it once those objects call the panic runtime. Under `-Cpanic=abort` a
/// reachable panic edge (an `Assert` failure, an `.unwrap()` on `None`) is a call
/// to `core::panicking::panic` that runs the panic hook and then aborts — exactly
/// as LLVM's objects call `panic_bounds_check` / `panic_const_*` — not an inline
/// libc `abort()` that skipped the hook. These fixtures never take such an edge;
/// a stub that IS reached aborts, which is the loud outcome the old inline
/// `abort()` gave.
#[allow(dead_code)]
pub fn write_abort_stubs<P: AsRef<Path>>(dir: &Path, objects: &[P]) -> std::path::PathBuf {
    let symbols = |args: &[&str]| -> std::collections::BTreeSet<String> {
        let mut out = std::collections::BTreeSet::new();
        for object in objects {
            let listing = Command::new("nm")
                .args(args)
                .arg(object.as_ref())
                .output()
                .expect("run nm over a backend object");
            for line in String::from_utf8_lossy(&listing.stdout).lines() {
                if let Some(symbol) = line.split_whitespace().last() {
                    out.insert(symbol.to_owned());
                }
            }
        }
        out
    };
    let undefined = symbols(&["-u"]);
    let defined = symbols(&["-g", "-U"]);
    let mut stubs = String::from("#include <stdlib.h>\n");
    for symbol in undefined.difference(&defined) {
        if !is_abort_stub_symbol(symbol) {
            continue;
        }
        let c_name = symbol.strip_prefix('_').unwrap_or(symbol);
        stubs.push_str(&format!(
            "void {c_name}(void) __asm__(\"{symbol}\"); void {c_name}(void) {{ abort(); }}\n"
        ));
    }
    let path = dir.join("abort_stubs.c");
    std::fs::write(&path, stubs).expect("write abort_stubs.c");
    path
}

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

/// The variables a bridge runner sets for the TEST process only
/// (`scripts/check_linux_aarch64_bridge.py` binds its backend snapshot through
/// them). They are not compiler inputs, and trustc refuses every `TCG_*`
/// variable in its environment — `--print sysroot` and every compile alike — so
/// a compiler child that inherited them would fail before doing any work.
#[allow(dead_code)]
pub const RUNNER_TEST_ONLY_ENV: [&str; 2] = ["TCG_TEST_BACKEND_PATH", "TCG_TEST_BACKEND_SHA256"];

/// The exact build compiler with no additional flags, for sysroot queries.
/// Every compiler child starts here, so none inherits [`RUNNER_TEST_ONLY_ENV`].
#[allow(dead_code)]
pub fn rustc_driver_command() -> Command {
    let mut command = Command::new(BUILD_COMPILER);
    for name in RUNNER_TEST_ONLY_ENV {
        command.env_remove(name);
    }
    command
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
    require_trust_channel();
    let mut cmd = rustc_driver_command();
    cmd.arg(format!("--edition={edition}"));
    cmd.arg("-Ztrust-verify=off");
    cmd
}

/// The bridge pins exactly `channel = "trust"` (scripts/trust_toolchain.py and
/// the release gate refuse anything else), so a test finding another channel
/// fails loudly instead of taking a stock path.
fn require_trust_channel() {
    let channel = pinned_toolchain();
    assert!(
        is_trust_channel(&channel),
        "crates/rustc-codegen-trust-cg/rust-toolchain.toml must pin channel = \"{TRUST_CHANNEL}\", \
         found {channel:?}; there is no stock-channel test path"
    );
}

/// Whether the `rust-std` for `target` is available to the pinned channel.
///
/// The Trust sysroot is asked directly: `<driver --print sysroot>/lib/rustlib/
/// <target>/lib` is the directory rustc itself loads the target's `std` from
/// (rustup rejects a target query for a linked custom toolchain:
/// `invalid toolchain name: 'trust'`). The installed Darwin Trust package ships
/// no `x86_64-apple-darwin` std today, so the x86 tests skip there.
#[allow(dead_code)]
pub fn target_std_available(target: &str) -> bool {
    require_trust_channel();
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

/// The line prefix [`backend_knobs_arg`] prints for every knob list it builds.
#[allow(dead_code)]
pub const BACKEND_KNOBS_TRACE: &str = "TCG_BRIDGE_BACKEND_KNOBS";

/// Build the `-Ztrust-ir-cg-args=...` argument for `knobs`.
///
/// The option is a whitespace-separated list of `key` / `key=value` items, so a
/// knob value containing whitespace cannot be spelled; no knob these tests use
/// takes one.
///
/// Each call also prints `TCG_BRIDGE_BACKEND_KNOBS knobs=<the list>` to the
/// calling test's captured output. `scripts/check_darwin_aarch64_bridge.py`
/// compares it with the test's positive-evidence marker: a test that builds a
/// `no-proof-certs` argument must say `certs=off`, so a certificates-on claim
/// cannot silently turn into a proofs-off compile.
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
    println!("{BACKEND_KNOBS_TRACE} knobs={}", knobs.join(" "));
    format!("{BACKEND_KNOBS_OPTION}={}", knobs.join(" "))
}

/// Does the build compiler carry [`BACKEND_KNOBS_OPTION`]?
///
/// `-Z help` is the compiler's own list of unstable options, so this asks the
/// compiler rather than inferring from a version. The option is a Trust
/// addition, and on a compiler without it the knob cannot be expressed at all.
/// On most hosts a test that needs a knob SKIPS when the answer is `false`
/// ([`skip_without_backend_knobs`]). On aarch64-apple-darwin the tests that
/// `scripts/check_darwin_aarch64_bridge.py` requires FAIL instead
/// (`support/darwin_native_prerequisites.rs`, and the host-scoped check in
/// `unsupported_program.rs`): that runner's preflight already refuses a
/// compiler without the option, so a `false` there is a defect of the host or
/// package, and a skip would be a pass without running (ledger L06-P10).
#[allow(dead_code)]
pub fn backend_knobs_supported() -> bool {
    use std::sync::OnceLock;
    static SUPPORTED: OnceLock<bool> = OnceLock::new();
    *SUPPORTED.get_or_init(|| {
        // `rustc_driver_command` drops the runner's test-only
        // `TCG_TEST_BACKEND_*` pair; an inherited one would make trustc refuse
        // and the probe misreport the option as missing.
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
