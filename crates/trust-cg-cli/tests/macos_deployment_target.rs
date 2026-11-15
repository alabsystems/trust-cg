// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The CLI captures `MACOSX_DEPLOYMENT_TARGET` for an Apple target whose
//! triple names no macOS version, refuses a malformed value, and lets an
//! explicit `aarch64-apple-macos<version>` triple win. Objects record the
//! chosen version in `LC_BUILD_VERSION`; on an AArch64 macOS host the linked
//! executable does too, because the link driver passes the same
//! `-mmacosx-version-min`.
//!
//! Object checks run on every host (they compile only). Link-and-run checks
//! need an AArch64 macOS host.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use trust_cg_codegen::pipeline::encode_tmbc;
use trust_ir::{Module, Ty};
use trust_ir_build::ModuleBuilder;

const ENV: &str = "MACOSX_DEPLOYMENT_TARGET";

fn trust_cg(directory: &Path, args: &[&str], deployment: Option<&str>) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_trust-cg"));
    command.arg("--permit-unlicensed"); // Claim-less fixtures: refused by default since WS7.5 (DG-73).
    command.current_dir(directory).args(args);
    match deployment {
        Some(value) => command.env(ENV, value),
        None => command.env_remove(ENV),
    };
    command.output().expect("run trust-cg")
}

/// `i32 main() { return 7; }`.
fn main_module() -> Module {
    let mut mb = ModuleBuilder::new("tcg_cli_deploy");
    let ty = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("main", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let value = fb.iconst(Ty::I32, 7);
    fb.ret(vec![value]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn write_module(directory: &Path) -> PathBuf {
    let path = directory.join("a.tmbc");
    fs::write(&path, encode_tmbc(&main_module()).unwrap()).unwrap();
    path
}

/// `(platform, minos)` of a Mach-O image's `LC_BUILD_VERSION`.
fn build_version(image: &[u8]) -> Option<(u32, u32)> {
    let word = |offset: usize| {
        image
            .get(offset..offset + 4)
            .map(|bytes| u32::from_le_bytes(bytes.try_into().unwrap()))
    };
    if word(0)? != 0xFEED_FACF {
        return None;
    }
    let mut offset = 32usize;
    for _ in 0..word(16)? {
        let (command, size) = (word(offset)?, word(offset + 4)? as usize);
        if command == 0x32 {
            return Some((word(offset + 8)?, word(offset + 12)?));
        }
        offset += size;
    }
    None
}

fn compile_object(target: &str, deployment: Option<&str>) -> (Output, Option<Vec<u8>>) {
    let directory = tempfile::tempdir().unwrap();
    write_module(directory.path());
    let output = trust_cg(
        directory.path(),
        &["-c", "--target", target, "-o", "a.o", "a.tmbc"],
        deployment,
    );
    let object = fs::read(directory.path().join("a.o")).ok();
    (output, object)
}

#[test]
fn environment_deployment_target_reaches_the_object() {
    for (value, minos) in [
        ("12.0", 0x000C_0000),
        ("13.3.1", 0x000D_0301),
        ("15", 0x000F_0000),
    ] {
        let (output, object) = compile_object("aarch64-apple-darwin", Some(value));
        assert!(
            output.status.success(),
            "{value}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(build_version(&object.unwrap()), Some((1, minos)), "{value}");
    }
    // Unset: the historical 14.0.
    let (output, object) = compile_object("aarch64-apple-darwin", None);
    assert!(output.status.success());
    assert_eq!(build_version(&object.unwrap()), Some((1, 0x000E_0000)));
}

#[test]
fn explicit_triple_version_wins_over_the_environment() {
    let (output, object) = compile_object("aarch64-apple-macos13.0", Some("12.0"));
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(build_version(&object.unwrap()), Some((1, 0x000D_0000)));
}

#[test]
fn malformed_environment_deployment_target_is_refused_before_output() {
    for value in ["", "12.", "twelve", "10.15", "12.0.0.1"] {
        let (output, object) = compile_object("aarch64-apple-darwin", Some(value));
        assert!(!output.status.success(), "{value:?} must be refused");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("[TCG-MACHO-DEPLOYMENT]"),
            "{value:?}: {stderr}"
        );
        assert!(object.is_none(), "{value:?}: no object may be written");
    }
}

#[test]
fn non_apple_targets_ignore_the_environment() {
    let (output, object) = compile_object("aarch64-unknown-linux-gnu", Some("12."));
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(&object.unwrap()[..4], b"\x7fELF");
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn linked_executable_records_the_deployment_target_without_a_warning() {
    for (target, deployment, minos) in [
        ("aarch64-apple-macos12.0", None, 0x000C_0000),
        ("aarch64-apple-darwin", Some("13.0"), 0x000D_0000),
    ] {
        let directory = tempfile::tempdir().unwrap();
        write_module(directory.path());
        let output = trust_cg(
            directory.path(),
            &["--target", target, "-o", "prog", "a.tmbc"],
            deployment,
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{target}: {stderr}");
        assert!(
            !stderr.contains("was built for newer") && !stderr.contains("ld: warning"),
            "{target}: {stderr}"
        );
        let image = fs::read(directory.path().join("prog")).unwrap();
        assert_eq!(build_version(&image), Some((1, minos)), "{target}");
        let status = Command::new(directory.path().join("prog"))
            .status()
            .unwrap();
        assert_eq!(status.code(), Some(7), "{target}");
    }
}
