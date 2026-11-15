// trust-cg-verify build script: RECORD the AY identity of the building toolchain.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The verifier may only start the `ay` whose BYTES are the ones recorded here
// (see `src/ay_identity.rs`). This script records, at build time, which
// compiler builds the crate and the content identity of the AY it ships:
//
//   TOOLCHAIN_AY_RECORD_SYSROOT     `$RUSTC --print sysroot`
//   TOOLCHAIN_AY_RECORD_SHA256      SHA-256 of `<sysroot>/bin/ay`'s bytes (the
//                                   identity admission compares)
//   TOOLCHAIN_AY_RECORD_COMMIT      `build.commit` of that binary's `--version`
//   TOOLCHAIN_AY_RECORD_VERSION     `build.version` of the same banner
//   TOOLCHAIN_AY_RECORD_INCREMENT   `build.increment` of the same banner
//   TOOLCHAIN_AY_RECORD_UNRECORDED  why nothing was recorded (empty when recorded)
//
// It also records the verifier's own source identity (not the toolchain's):
//
//   VERIFIER_SOURCE_SHA256          SHA-256 of this crate's and
//                                   trust-cg-process-env's sources
//                                   (`src/verifier_source_digest.rs`); empty
//                                   when an input could not be read
//
// When the sysroot is a local OVERLAY toolchain (an installed pack with a newer
// AY and Clean put in by `scripts/assemble_trust_overlay.py`), its manifest
// `<sysroot>/overlay.json` must name exactly the bytes of `bin/ay` AND
// `bin/clean`; otherwise nothing is recorded. The overlay is recorded as:
//
//   TOOLCHAIN_AY_RECORD_OVERLAY               `valid`, `invalid`, or empty (no overlay)
//   TOOLCHAIN_AY_RECORD_OVERLAY_SHA256        SHA-256 of the manifest's bytes
//   TOOLCHAIN_AY_RECORD_OVERLAY_CLEAN_SHA256  SHA-256 of `<sysroot>/bin/clean` (the
//                                             only checker such a build accepts)
//   TOOLCHAIN_AY_RECORD_OVERLAY_CLEAN_COMMIT  the manifest's Clean source commit (a
//                                             label: Clean reports no commit itself)
//
// The banner fields are labels for diagnostics and verdict provenance; they
// are bound to the recorded bytes because the file is digested before AND
// after its banner is read, and a file that changed in between is refused.
//
// `TOOLCHAIN_AY_EXPECTED_SYSROOT`, when set, names the sysroot the caller
// selected. It forces a re-record whenever it changes and must equal the
// compiler's sysroot, or nothing is recorded.
// With an explicit HOST sysroot, a different expectation must instead match
// the actual metadata compilation context. Bootstrap and runtime sysroots
// may differ; neither an unrelated expectation nor a failed query is accepted.
//
// `TOOLCHAIN_AY_RECORD_HOST_SYSROOT`, when set, names the sysroot whose
// compiler will HOST this crate, and its `bin/ay` is recorded instead of the
// build compiler's. Trust's bootstrap sets it when it compiles the compiler:
// the stage-N+1 compiler is compiled BY stage N, so `$RUSTC --print sysroot`
// is stage N's sysroot, whose `bin/ay` is the battery the stage N-1 compiler
// built. The assembled compiler hosts this crate in stage N+1's sysroot and
// names THAT sysroot's `bin/ay` (`ay_identity`, rule 2), so recording stage
// N's made every assembled compiler refuse the AY it ships
// (`TCG-AY-IDENTITY-MISMATCH`, measured 2026-10-01) and put a binary of the
// previous stage's compiler into the compiler's bytes, which a diverse
// double compile then saw as a dependence on the bootstrap seed. A relative
// path, or a sysroot that ships no AY, records nothing.
//
// The names deliberately avoid the `TRUST_` prefix (authenticated Targo refuses
// it as build-script authority) and `TCG_`/`TRUST_CG_` (trustc refuses a
// compile whose environment carries those untracked codegen controls).
//
// Nothing here is a fallback: an unrecorded identity makes every runtime AY
// selection refuse with a named error. The banner is read by the SAME parser
// the library uses.

use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

#[path = "src/ay_identity_banner.rs"]
#[allow(dead_code)]
mod banner;

#[path = "src/toolchain_overlay_manifest.rs"]
mod overlay_manifest;

#[path = "src/verifier_source_digest.rs"]
mod verifier_source_digest;

#[path = "build_support/expected_sysroot.rs"]
mod expected_sysroot;

const PROBE_TIMEOUT: Duration = Duration::from_secs(60);

/// The sysroot a caller (`scripts/trust_cargo.sh`) selected; see `main`.
const EXPECTED_SYSROOT_ENV: &str = "TOOLCHAIN_AY_EXPECTED_SYSROOT";

/// The sysroot of the compiler that will host this crate (Trust's bootstrap,
/// building the compiler); see the header and `recorded_sysroot`.
const HOST_SYSROOT_ENV: &str = "TOOLCHAIN_AY_RECORD_HOST_SYSROOT";

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=build_support/expected_sysroot.rs");
    println!("cargo:rerun-if-changed=src/ay_identity_banner.rs");
    println!("cargo:rerun-if-changed=src/toolchain_overlay_manifest.rs");
    println!("cargo:rerun-if-env-changed=RUSTC");
    println!("cargo:rerun-if-env-changed=CARGO_ENCODED_RUSTFLAGS");
    println!("cargo:rerun-if-env-changed=RUSTFLAGS");
    // Cargo's fingerprint keys the compiler by its version text, not its path,
    // so a second sysroot with a byte-identical `trustc` (an overlay toolchain
    // cloned from the same pack) would reuse the FIRST sysroot's record. A
    // caller that selects a toolchain names it here; the value only forces a
    // re-record and is checked against what the compiler reports (a mismatch
    // records nothing). It never selects or admits anything.
    println!("cargo:rerun-if-env-changed={EXPECTED_SYSROOT_ENV}");
    // The hosting sysroot decides WHICH `bin/ay` is recorded, so a change of it
    // must re-record.
    println!("cargo:rerun-if-env-changed={HOST_SYSROOT_ENV}");

    let record = record_toolchain_ay();
    let (sysroot, mut identity, mut unrecorded) = match record {
        Ok((sysroot, identity)) => (sysroot, Some(identity), String::new()),
        Err((sysroot, reason)) => (sysroot, None, reason),
    };
    if let Some(expected) = std::env::var_os(EXPECTED_SYSROOT_ENV)
        && !expected.is_empty()
    {
        let hosting = std::env::var_os(HOST_SYSROOT_ENV).is_some_and(|host| !host.is_empty());
        let matched = expected_sysroot::matches(
            Path::new(&expected),
            Path::new(&sysroot),
            hosting,
            compilation_sysroot,
        );
        if matched != Ok(true) {
            identity = None;
            let reason = format!(
                "{EXPECTED_SYSROOT_ENV} names {}, but the recorded sysroot {sysroot:?} and authenticated compilation context do not match: {matched:?}",
                Path::new(&expected).display()
            );
            unrecorded = if unrecorded.is_empty() {
                reason
            } else {
                format!("{unrecorded}; {reason}")
            };
        }
    }
    let overlay = record_overlay(&sysroot, identity.as_ref());
    if let Some(Err(reason)) = &overlay {
        identity = None;
        unrecorded = if unrecorded.is_empty() {
            reason.clone()
        } else {
            format!("{unrecorded}; {reason}")
        };
    }
    let overlay_status = match &overlay {
        None => "",
        Some(Ok(_)) => "valid",
        Some(Err(_)) => "invalid",
    };
    let overlay = overlay.and_then(Result::ok);
    emit("TOOLCHAIN_AY_RECORD_OVERLAY", overlay_status);
    emit(
        "TOOLCHAIN_AY_RECORD_OVERLAY_SHA256",
        overlay.as_ref().map_or("", |o| o.manifest_sha256.as_str()),
    );
    emit(
        "TOOLCHAIN_AY_RECORD_OVERLAY_CLEAN_SHA256",
        overlay.as_ref().map_or("", |o| o.clean_sha256.as_str()),
    );
    emit(
        "TOOLCHAIN_AY_RECORD_OVERLAY_CLEAN_COMMIT",
        overlay.as_ref().map_or("", |o| o.clean_commit.as_str()),
    );
    emit("TOOLCHAIN_AY_RECORD_SYSROOT", &sysroot);
    emit(
        "TOOLCHAIN_AY_RECORD_SHA256",
        identity.as_ref().map_or("", |(sha256, _)| sha256.as_str()),
    );
    emit(
        "TOOLCHAIN_AY_RECORD_COMMIT",
        identity.as_ref().map_or("", |(_, build)| build.commit()),
    );
    emit(
        "TOOLCHAIN_AY_RECORD_VERSION",
        identity.as_ref().map_or("", |(_, build)| build.version()),
    );
    emit(
        "TOOLCHAIN_AY_RECORD_INCREMENT",
        identity.as_ref().map_or("", |(_, build)| build.increment()),
    );
    emit("TOOLCHAIN_AY_RECORD_UNRECORDED", &unrecorded);
    record_verifier_source_identity();
}

/// Record `VERIFIER_SOURCE_SHA256`, the verifier's source identity
/// (`src/verifier_source_digest.rs`), and re-run whenever one of its inputs
/// changes. An input that cannot be read records the empty identity, which
/// disables the source-bound negative memo rather than letting its entries
/// cross builds.
fn record_verifier_source_identity() {
    let manifest_dir = PathBuf::from(
        std::env::var_os("CARGO_MANIFEST_DIR").expect("cargo sets CARGO_MANIFEST_DIR"),
    );
    for input in verifier_source_digest::INPUTS {
        let path = manifest_dir.join(input);
        if path.exists() {
            println!("cargo:rerun-if-changed={}", path.display());
        }
    }
    let identity = verifier_source_digest::digest(&manifest_dir).unwrap_or_else(|error| {
        println!("cargo:warning=no verifier source identity ({error}); the source-bound negative memo is off");
        String::new()
    });
    emit("VERIFIER_SOURCE_SHA256", &identity);
}

fn emit(key: &str, value: &str) {
    // `cargo:rustc-env` is line-oriented; a newline would silently truncate.
    let value = value.replace(['\n', '\r'], " ");
    println!("cargo:rustc-env={key}={value}");
}

type Recorded = (String, (String, banner::AyBuildIdentity));
type Unrecorded = (String, String);

/// Ask the selected compiler using the same encoded flags as compilation.
/// Unparsed shell flags and ambiguous query output keep the record disabled.
fn compilation_sysroot() -> Result<PathBuf, String> {
    let rustc = std::env::var_os("RUSTC").ok_or("cargo supplied no RUSTC")?;
    let mut command = Command::new(rustc);
    if let Some(flags) = std::env::var_os("CARGO_ENCODED_RUSTFLAGS") {
        let flags = flags
            .into_string()
            .map_err(|_| "non-UTF-8 CARGO_ENCODED_RUSTFLAGS")?;
        if !flags.is_empty() {
            command.args(flags.split(char::from(0x1f)));
        }
    } else if std::env::var_os("RUSTFLAGS").is_some_and(|flags| !flags.is_empty()) {
        return Err("bootstrap sysroot query requires encoded compiler flags".into());
    }
    command.args(["--print", "sysroot"]);
    let (output, _) = run_bounded(&mut command)?;
    let output = String::from_utf8(output).map_err(|_| "non-UTF-8 compiler sysroot")?;
    let mut lines = output.lines();
    let path = PathBuf::from(lines.next().ok_or("empty compiler sysroot")?);
    if lines.next().is_some() || !path.is_absolute() {
        return Err("compiler sysroot must be one absolute path".into());
    }
    Ok(path)
}

/// The sysroot whose `bin/ay` is recorded, and whether it is a HOSTING sysroot
/// the build named (`TOOLCHAIN_AY_RECORD_HOST_SYSROOT`) rather than the build
/// compiler's (`$RUSTC --print sysroot`).
fn recorded_sysroot() -> Result<(String, bool), Unrecorded> {
    if let Some(host) = std::env::var_os(HOST_SYSROOT_ENV)
        && !host.is_empty()
    {
        let host = PathBuf::from(host);
        if !host.is_absolute() {
            return Err((
                host.display().to_string(),
                format!(
                    "{HOST_SYSROOT_ENV} names {}, which is not absolute",
                    host.display()
                ),
            ));
        }
        return Ok((host.display().to_string(), true));
    }
    let Some(rustc) = std::env::var_os("RUSTC") else {
        return Err((
            String::new(),
            "cargo supplied no RUSTC to the build script".into(),
        ));
    };
    let (output, _) =
        run_bounded(Command::new(&rustc).args(["--print", "sysroot"])).map_err(|error| {
            (
                String::new(),
                format!(
                    "`{} --print sysroot` failed: {error}",
                    Path::new(&rustc).display()
                ),
            )
        })?;
    let sysroot = String::from_utf8_lossy(&output).trim().to_owned();
    if sysroot.is_empty() {
        return Err((
            sysroot,
            "the build compiler printed an empty sysroot".into(),
        ));
    }
    Ok((sysroot, false))
}

fn record_toolchain_ay() -> Result<Recorded, Unrecorded> {
    let (sysroot, hosting) = recorded_sysroot()?;
    let ay = PathBuf::from(&sysroot)
        .join("bin")
        .join(format!("ay{}", std::env::consts::EXE_SUFFIX));
    if !ay.is_file() {
        // Bootstrap installs a hosting sysroot's AY before it compiles a
        // compiler that ships, but a `check` sharing this record can run
        // first. Cargo keeps a missing path stale, so this re-records until
        // the AY exists instead of leaving a later build "unrecorded".
        if hosting {
            println!("cargo:rerun-if-changed={}", ay.display());
        }
        return Err((
            sysroot,
            format!(
                "the recorded sysroot ships no AY at {} (not a Trust toolchain with its solver)",
                ay.display()
            ),
        ));
    }
    // A rebuilt toolchain AY must re-record, or every later run would refuse it.
    // Emitted only for an existing file: cargo treats a missing path as always
    // stale and would rebuild this crate on every invocation.
    println!("cargo:rerun-if-changed={}", ay.display());
    let digest_before = sha256_file(&ay).map_err(|error| {
        (
            sysroot.clone(),
            format!("cannot digest {}: {error}", ay.display()),
        )
    })?;
    let (stdout, stderr) = run_bounded(Command::new(&ay).arg("--version")).map_err(|error| {
        (
            sysroot.clone(),
            format!("`{} --version` failed: {error}", ay.display()),
        )
    })?;
    let banner_text = format!(
        "{}\n{}",
        String::from_utf8_lossy(&stdout),
        String::from_utf8_lossy(&stderr)
    );
    let identity = banner::parse_ay_version_banner(&banner_text).map_err(|reason| {
        (
            sysroot.clone(),
            format!(
                "{} reports no usable build identity: {reason}",
                ay.display()
            ),
        )
    })?;
    let digest_after = sha256_file(&ay).map_err(|error| {
        (
            sysroot.clone(),
            format!("cannot re-digest {}: {error}", ay.display()),
        )
    })?;
    if digest_after != digest_before {
        return Err((
            sysroot,
            format!(
                "{} changed while its identity was being recorded (sha256 {digest_before} then \
                 {digest_after})",
                ay.display()
            ),
        ));
    }
    Ok((sysroot, (digest_before, identity)))
}

/// `None` when the sysroot is not an overlay. Otherwise the manifest must
/// name the recorded AY and the current bytes of `<sysroot>/bin/clean`
/// (`overlay_manifest::validate_overlay_manifest`, unit-tested in the
/// library); any disagreement records NOTHING.
fn record_overlay(
    sysroot: &str,
    identity: Option<&(String, banner::AyBuildIdentity)>,
) -> Option<Result<overlay_manifest::ValidatedOverlay, String>> {
    if sysroot.is_empty() {
        return None;
    }
    let manifest_path = Path::new(sysroot).join("overlay.json");
    if !manifest_path.is_file() {
        return None;
    }
    let clean = Path::new(sysroot)
        .join("bin")
        .join(format!("clean{}", std::env::consts::EXE_SUFFIX));
    println!("cargo:rerun-if-changed={}", manifest_path.display());
    if clean.is_file() {
        println!("cargo:rerun-if-changed={}", clean.display());
    }
    let refuse =
        |reason: String| format!("overlay toolchain {}: {reason}", manifest_path.display());
    let bytes = match std::fs::read(&manifest_path) {
        Ok(bytes) => bytes,
        Err(error) => return Some(Err(refuse(format!("cannot read the manifest: {error}")))),
    };
    let ay = identity.map(|(sha256, build)| overlay_manifest::RecordedAy {
        sha256,
        commit: build.commit(),
        increment: build.increment(),
        describe: build.describe(),
    });
    let clean_found = sha256_file(&clean).map_err(|error| format!("{}: {error}", clean.display()));
    Some(
        overlay_manifest::validate_overlay_manifest(
            &bytes,
            ay.as_ref(),
            clean_found.as_deref().map_err(String::as_str),
        )
        .map_err(refuse),
    )
}

/// Lowercase-hex SHA-256 of a file's bytes, streamed.
fn sha256_file(path: &Path) -> Result<String, std::io::Error> {
    use sha2::{Digest, Sha256};
    let mut file = std::fs::File::open(path)?;
    let mut hasher = Sha256::new();
    let mut buffer = vec![0u8; 1 << 20];
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Ok(format!("{:x}", hasher.finalize()))
}

/// Run to a successful exit within [`PROBE_TIMEOUT`]; returns (stdout, stderr).
fn run_bounded(command: &mut Command) -> Result<(Vec<u8>, Vec<u8>), String> {
    let mut child = command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("spawn: {error}"))?;
    let mut stdout = child.stdout.take().ok_or("stdout was not captured")?;
    let mut stderr = child.stderr.take().ok_or("stderr was not captured")?;
    let out = std::thread::spawn(move || {
        let mut bytes = Vec::new();
        stdout.read_to_end(&mut bytes).map(|_| bytes)
    });
    let err = std::thread::spawn(move || {
        let mut bytes = Vec::new();
        stderr.read_to_end(&mut bytes).map(|_| bytes)
    });
    let started = Instant::now();
    let status = loop {
        match child.try_wait().map_err(|error| format!("wait: {error}"))? {
            Some(status) => break status,
            None if started.elapsed() >= PROBE_TIMEOUT => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(format!("no exit within {}s", PROBE_TIMEOUT.as_secs()));
            }
            None => std::thread::sleep(Duration::from_millis(10)),
        }
    };
    let stdout = out
        .join()
        .map_err(|_| "stdout reader panicked".to_string())?
        .map_err(|error| format!("read stdout: {error}"))?;
    let stderr = err
        .join()
        .map_err(|_| "stderr reader panicked".to_string())?
        .map_err(|error| format!("read stderr: {error}"))?;
    if !status.success() {
        return Err(format!("exited with {status}"));
    }
    Ok((stdout, stderr))
}
