// trust-cg-codegen/tests/jit_map_jit_entitlement.rs - MAP_JIT under the hardened runtime
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The Apple Silicon JIT's `MAP_JIT` contract under the hardened runtime.
//!
//! Every AArch64 macOS JIT publication maps its code with `MAP_JIT`. A process
//! signed with the hardened runtime (`codesign --options runtime`) receives a
//! `MAP_JIT` mapping only when its signature carries the
//! `com.apple.security.cs.allow-jit` entitlement. These controls copy this
//! test binary, re-sign each copy ad hoc with `codesign`, and run the
//! probe test inside it through the production `Compiler::compile_module_to_jit`
//! path:
//!
//! - hardened runtime without the entitlement: the kernel refuses the mapping
//!   and the JIT returns `JitError::MapJitRefused` (a typed error naming the
//!   entitlement; the process exits normally rather than crashing);
//! - hardened runtime with the entitlement set to false: refused the same way;
//! - hardened runtime with the entitlement: the JIT publishes and runs code;
//! - an ad-hoc re-signature without the hardened runtime: publishes and runs.
//!
//! Each signed copy is also read by the independent signature verifier, so
//! the runtime flag and the bound entitlements are checked in the bytes the
//! kernel judged. The kernel's policy itself is trusted base, measured here on
//! macOS 26.6 (Apple M4 Max), not modeled.

#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

#[path = "common/rosetta.rs"]
mod process;

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::jit::{
    ALLOW_JIT_ENTITLEMENT, JitError, ProcessCodeSigningStatus, process_code_signing_status,
};
use trust_cg_codegen::macho::codesign::{AdHocSignature, CS_ADHOC, verify_ad_hoc_signature};
use trust_cg_codegen::{CompileError, Compiler, CompilerConfig};
use trust_ir::Ty;
use trust_ir_build::ModuleBuilder;

/// Resolved on PATH, as the Darwin floor records its identity.
const CODESIGN: &str = "codesign";
/// The probe's expected outcome in a re-signed child (`allowed`/`refused`).
const EXPECT_ENV: &str = "TCG_MAP_JIT_PROBE_EXPECT";
/// Whether the re-signed child must run under the hardened runtime (`1`/`0`).
const HARDENED_ENV: &str = "TCG_MAP_JIT_PROBE_HARDENED";
const PROBE_TEST: &str = "map_jit_probe_matches_the_process_signing_policy";
const REPORT_PREFIX: &str = "TCG_MAP_JIT_PROBE ";
const EINVAL: i32 = 22;
const EPERM: i32 = 1;

fn entitlements_plist(allow_jit: bool) -> String {
    format!(
        "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\
         <!DOCTYPE plist PUBLIC \"-//Apple//DTD PLIST 1.0//EN\" \
         \"http://www.apple.com/DTDs/PropertyList-1.0.dtd\">\n\
         <plist version=\"1.0\"><dict><key>{ALLOW_JIT_ENTITLEMENT}</key><{}/></dict></plist>\n",
        if allow_jit { "true" } else { "false" }
    )
}

/// `answer() -> i64 { 42 }`.
fn answer_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("tcg_map_jit_probe");
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("answer", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let answer = fb.iconst(Ty::I64, 42);
    fb.ret(vec![answer]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Compile `answer` through the production JIT path and call it.
fn jit_answer() -> Result<i64, Box<CompileError>> {
    let compiler =
        Compiler::new(CompilerConfig::for_host_jit()).with_codegen_license(permit_unlicensed());
    let result = compiler
        .compile_module_to_jit(&answer_module(), &HashMap::new())
        .map_err(Box::new)?;
    // SAFETY: `answer` was compiled from a `() -> i64` TrustIR signature.
    let answer: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("answer")
            .expect("published symbol resolves")
            .into_inner()
    };
    Ok(answer())
}

/// In this process (cargo's linker-signed test binary, no hardened runtime)
/// MAP_JIT is granted. Inside a re-signed copy the parent tests set
/// [`EXPECT_ENV`] and [`HARDENED_ENV`], and the probe asserts that outcome and
/// reports it on one line.
#[test]
fn map_jit_probe_matches_the_process_signing_policy() {
    let status = process_code_signing_status().expect("csops(CS_OPS_STATUS) answers");
    assert!(status.is_valid(), "{status}");
    let expectation = std::env::var(EXPECT_ENV).ok();
    let hardened = std::env::var(HARDENED_ENV).ok();
    let (expect_allowed, expect_hardened) = match (expectation.as_deref(), hardened.as_deref()) {
        (None, None) => (true, false),
        (Some("allowed"), Some(flag @ ("0" | "1"))) => (true, flag == "1"),
        (Some("refused"), Some("1")) => (false, true),
        other => panic!("unsupported probe configuration {other:?}"),
    };
    assert_eq!(status.hardened_runtime(), expect_hardened, "{status}");

    match (jit_answer().map_err(|error| *error), expect_allowed) {
        (Ok(value), true) => {
            assert_eq!(value, 42);
            println!(
                "{REPORT_PREFIX}outcome=allowed value={value} flags={:#010x}",
                status.flags
            );
        }
        (
            Err(CompileError::Jit(
                ref error @ JitError::MapJitRefused {
                    len,
                    code_signing,
                    ref source,
                },
            )),
            false,
        ) => {
            let errno = source.raw_os_error().expect("kernel errno");
            assert!(errno == EINVAL || errno == EPERM, "{error}");
            assert!(len > 0);
            assert_eq!(code_signing, Some(status));
            let message = error.to_string();
            assert!(message.contains(ALLOW_JIT_ENTITLEMENT), "{message}");
            assert!(message.contains("hardened runtime"), "{message}");
            println!(
                "{REPORT_PREFIX}outcome=refused errno={errno} len={len} flags={:#010x}",
                status.flags
            );
        }
        (outcome, _) => panic!(
            "MAP_JIT probe under {status} expected {}, got {outcome:?}",
            if expect_allowed {
                "success"
            } else {
                "MapJitRefused"
            }
        ),
    }
}

/// A copy of this test binary, re-signed ad hoc by `codesign` with `options`.
fn signed_copy(directory: &Path, name: &str, options: &[&str]) -> (PathBuf, AdHocSignature) {
    let copy = directory.join(name);
    fs::copy(std::env::current_exe().unwrap(), &copy).unwrap();
    let mut command = Command::new(CODESIGN);
    command
        .args(["--force", "--sign", "-"])
        .args(options)
        .arg(&copy);
    let result =
        process::command_output_with_timeout(&mut command, process::codegen_link_timeout())
            .expect("codesign starts");
    assert!(!result.timed_out, "codesign timed out");
    assert!(
        result.output.status.success(),
        "codesign {options:?}: {}",
        String::from_utf8_lossy(&result.output.stderr)
    );
    let signature = verify_ad_hoc_signature(&fs::read(&copy).unwrap())
        .unwrap_or_else(|error| panic!("{name}: {error}"));
    assert_ne!(signature.code_directory.flags & CS_ADHOC, 0);
    (copy, signature)
}

/// Run the probe inside `binary` and return its report line. The child must
/// exit 0 after running exactly the probe: a refusal is a typed error, never
/// a crash or a signal.
fn run_probe(binary: &Path, expect: &str, hardened: bool) -> String {
    let mut command = Command::new(binary);
    command
        .args(["--exact", PROBE_TEST, "--nocapture", "--test-threads=1"])
        .env(EXPECT_ENV, expect)
        .env(HARDENED_ENV, if hardened { "1" } else { "0" })
        .env_remove("RUST_TEST_NOCAPTURE");
    let result = process::command_output_with_timeout(&mut command, process::codegen_run_timeout())
        .expect("probe starts");
    assert!(!result.timed_out, "probe timed out");
    let stdout = String::from_utf8_lossy(&result.output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&result.output.stderr).into_owned();
    // libtest prints `test <name> ... ` before the probe's own line.
    let report: Vec<&str> = stdout
        .lines()
        .filter_map(|line| line.find(REPORT_PREFIX).map(|at| &line[at..]))
        .collect();
    assert!(
        result.output.status.success() && report.len() == 1,
        "probe in {} (expect {expect}, hardened {hardened}) ended with {:?}; report {report:?}; \
         stdout: {stdout}; stderr: {stderr}",
        binary.display(),
        result.output.status
    );
    assert!(
        stdout.contains("1 passed; 0 failed; 0 ignored"),
        "the probe did not run exactly once"
    );
    report[0].to_string()
}

fn write_entitlements(directory: &Path, allow_jit: bool) -> String {
    let path = directory.join(format!("allow-jit-{allow_jit}.plist"));
    fs::write(&path, entitlements_plist(allow_jit)).unwrap();
    path.to_str().unwrap().to_string()
}

fn hardened_flags(report: &str) -> ProcessCodeSigningStatus {
    let flags = report
        .split_whitespace()
        .find_map(|field| field.strip_prefix("flags=0x"))
        .and_then(|hex| u32::from_str_radix(hex, 16).ok())
        .unwrap_or_else(|| panic!("no flags in {report}"));
    ProcessCodeSigningStatus { flags }
}

#[test]
fn hardened_runtime_without_allow_jit_refuses_map_jit_as_a_typed_error() {
    let directory = tempfile::tempdir().unwrap();
    let (binary, signature) = signed_copy(
        directory.path(),
        "probe-hardened",
        &["--options", "runtime"],
    );
    assert!(signature.code_directory.has_hardened_runtime());
    assert_eq!(signature.entitlements_xml, None);
    let report = run_probe(&binary, "refused", true);
    assert!(report.contains("outcome=refused errno=22 "), "{report}");
    assert!(hardened_flags(&report).hardened_runtime(), "{report}");
}

#[test]
fn hardened_runtime_with_allow_jit_false_refuses_map_jit() {
    let directory = tempfile::tempdir().unwrap();
    let plist = write_entitlements(directory.path(), false);
    let (binary, signature) = signed_copy(
        directory.path(),
        "probe-hardened-false",
        &["--options", "runtime", "--entitlements", &plist],
    );
    assert!(signature.code_directory.has_hardened_runtime());
    let xml = signature.entitlements_xml.as_deref().unwrap();
    assert!(
        xml.contains(ALLOW_JIT_ENTITLEMENT) && xml.contains("<false/>"),
        "{xml}"
    );
    let report = run_probe(&binary, "refused", true);
    assert!(report.contains("outcome=refused errno=22 "), "{report}");
}

#[test]
fn hardened_runtime_with_allow_jit_publishes_and_runs_jit_code() {
    let directory = tempfile::tempdir().unwrap();
    let plist = write_entitlements(directory.path(), true);
    let (binary, signature) = signed_copy(
        directory.path(),
        "probe-hardened-allow-jit",
        &["--options", "runtime", "--entitlements", &plist],
    );
    assert!(signature.code_directory.has_hardened_runtime());
    assert!(signature.has_der_entitlements);
    let xml = signature.entitlements_xml.as_deref().unwrap();
    assert!(
        xml.contains(ALLOW_JIT_ENTITLEMENT) && xml.contains("<true/>"),
        "{xml}"
    );
    let report = run_probe(&binary, "allowed", true);
    assert!(report.contains("outcome=allowed value=42 "), "{report}");
    assert!(hardened_flags(&report).hardened_runtime(), "{report}");
}

#[test]
fn ad_hoc_resignature_without_hardened_runtime_publishes_and_runs_jit_code() {
    let directory = tempfile::tempdir().unwrap();
    let (binary, signature) = signed_copy(directory.path(), "probe-ad-hoc", &[]);
    assert!(!signature.code_directory.has_hardened_runtime());
    assert!(!signature.code_directory.is_linker_signed());
    let report = run_probe(&binary, "allowed", false);
    assert!(report.contains("outcome=allowed value=42 "), "{report}");
    assert!(!hardened_flags(&report).hardened_runtime(), "{report}");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
