// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Mach-O objects record the target's macOS deployment target, and ld64 links
//! them at that deployment target without a version-mismatch warning.
//!
//! Every object is compiled through `Compiler` for
//! `aarch64-apple-macos<version>`, its `LC_BUILD_VERSION` is read both from
//! the bytes and with `otool -l`, and it is linked by the host `cc` (Apple
//! clang driving ld64) at the same `-mmacosx-version-min` next to a C driver
//! compiled for that version. The link must succeed with no
//! "was built for newer 'macOS' version" warning and the program must return
//! the expected value. A negative control links an unversioned (macOS 14.0)
//! object at 12.0 and requires ld64's warning, so the positive checks cannot
//! pass vacuously.
//!
//! The byte-level checks run on every host; linking and execution need an
//! AArch64 macOS host and are compiled out elsewhere.

use trust_cg_codegen::apple_deployment::AppleOsVersion;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_ir::{BinOp, Module, Ty};
use trust_ir_build::ModuleBuilder;

const LC_BUILD_VERSION: u32 = 0x32;
const PLATFORM_MACOS: u32 = 1;

/// `i64 tcg_deploy_mix(i64 a, i64 b) = a * 3 + b`.
fn mix_module() -> Module {
    let mut mb = ModuleBuilder::new("tcg_deploy");
    let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("tcg_deploy_mix", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let a = fb.add_block_param(entry, Ty::I64);
    let b = fb.add_block_param(entry, Ty::I64);
    let three = fb.iconst(Ty::I64, 3);
    let scaled = fb.binop(BinOp::Mul, Ty::I64, a, three);
    let sum = fb.binop(BinOp::Add, Ty::I64, scaled, b);
    fb.ret(vec![sum]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn compile_for(triple: &str) -> Vec<u8> {
    let spec = TargetSpec::parse(triple).unwrap_or_else(|error| panic!("{triple}: {error}"));
    let config = CompilerConfig {
        opt_level: OptLevel::O2,
        ..CompilerConfig::default()
    };
    Compiler::new_for_target_spec(config, spec)
        .with_codegen_license(permit_unlicensed())
        .compile(&mix_module())
        .unwrap_or_else(|error| panic!("{triple}: {error}"))
        .object_code
}

/// `(platform, minos, sdk)` of the object's single `LC_BUILD_VERSION`.
fn build_version(object: &[u8]) -> (u32, u32, u32) {
    let word = |offset: usize| u32::from_le_bytes(object[offset..offset + 4].try_into().unwrap());
    assert_eq!(word(0), 0xFEED_FACF, "64-bit Mach-O magic");
    let mut found = Vec::new();
    let mut offset = 32usize;
    for _ in 0..word(16) {
        let (command, size) = (word(offset), word(offset + 4) as usize);
        if command == LC_BUILD_VERSION {
            found.push((word(offset + 8), word(offset + 12), word(offset + 16)));
        }
        offset += size;
    }
    assert_eq!(found.len(), 1, "exactly one LC_BUILD_VERSION");
    found[0]
}

const VERSIONS: [&str; 6] = ["11.0", "12.0", "12.3", "13.3.1", "14.0", "15.0"];

#[test]
fn objects_record_the_triple_deployment_target() {
    for version in VERSIONS {
        let expected = AppleOsVersion::parse(version).unwrap();
        let object = compile_for(&format!("aarch64-apple-macos{version}"));
        let (platform, minos, sdk) = build_version(&object);
        assert_eq!(platform, PLATFORM_MACOS, "{version}");
        assert_eq!(minos, expected.macho_encoding(), "{version}");
        assert_eq!(
            sdk,
            expected
                .max(AppleOsVersion::DEFAULT_MACOS_MINIMUM)
                .macho_encoding(),
            "{version}"
        );
    }
    // No version in the triple: the historical 14.0.
    assert_eq!(
        build_version(&compile_for("aarch64-apple-darwin")),
        (PLATFORM_MACOS, 0x000E_0000, 0x000E_0000)
    );
}

#[test]
fn deployment_target_is_part_of_the_compile_policy() {
    use trust_cg_codegen::compile_policy::{CompilePolicy, CompilePolicyPartition};

    let config = CompilerConfig::default();
    let digest = |triple: &str| {
        CompilePolicy::from_compiler(TargetSpec::parse(triple).unwrap(), &config)
            .unwrap()
            .digest(CompilePolicyPartition::Artifact)
    };
    assert_ne!(
        digest("aarch64-apple-macos12.0"),
        digest("aarch64-apple-macos13.0")
    );
    assert_ne!(
        digest("aarch64-apple-macos12.0"),
        digest("aarch64-apple-darwin")
    );
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod native {
    use super::*;
    use std::path::Path;
    use std::process::Command;

    const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
int64_t tcg_deploy_mix(int64_t, int64_t);
int main(void) {
    int64_t got = tcg_deploy_mix(14, -2);
    printf("%lld\n", (long long)got);
    return got == 40 ? 0 : 1;
}
"#;

    const MISMATCH: &str = "was built for newer 'macOS' version";

    struct Linked {
        stderr: String,
        status_ok: bool,
        run_ok: Option<bool>,
    }

    fn link_and_run(directory: &Path, tag: &str, object: &[u8], link_version: &str) -> Linked {
        let object_path = directory.join(format!("{tag}.o"));
        let driver_path = directory.join("driver.c");
        let binary_path = directory.join(format!("{tag}.bin"));
        std::fs::write(&object_path, object).unwrap();
        std::fs::write(&driver_path, DRIVER).unwrap();
        let output = Command::new("cc")
            .arg(format!("-mmacosx-version-min={link_version}"))
            .arg("-O2")
            .arg(&driver_path)
            .arg(&object_path)
            .arg("-o")
            .arg(&binary_path)
            .env_remove("MACOSX_DEPLOYMENT_TARGET")
            .output()
            .expect("run the host cc");
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        let run_ok = output.status.success().then(|| {
            let run = Command::new(&binary_path)
                .output()
                .expect("run the linked binary");
            run.status.success() && String::from_utf8_lossy(&run.stdout).trim() == "40"
        });
        Linked {
            stderr,
            status_ok: output.status.success(),
            run_ok,
        }
    }

    fn otool_minos(directory: &Path, object: &[u8]) -> String {
        let path = directory.join("inspect.o");
        std::fs::write(&path, object).unwrap();
        let output = Command::new("otool")
            .arg("-l")
            .arg(&path)
            .output()
            .expect("run otool");
        assert!(output.status.success(), "otool -l failed");
        let text = String::from_utf8_lossy(&output.stdout).into_owned();
        let mut lines = text
            .lines()
            .skip_while(|line| !line.contains("LC_BUILD_VERSION"));
        lines
            .find_map(|line| line.trim().strip_prefix("minos ").map(str::to_owned))
            .expect("otool reports the LC_BUILD_VERSION minos")
    }

    #[test]
    fn ld64_links_each_deployment_target_without_a_version_warning() {
        let directory = tempfile::tempdir().unwrap();
        for version in VERSIONS {
            let object = compile_for(&format!("aarch64-apple-macos{version}"));
            let parsed = AppleOsVersion::parse(version).unwrap();
            // otool prints the minimum OS without a zero patch component.
            assert_eq!(otool_minos(directory.path(), &object), parsed.to_string());
            let linked = link_and_run(directory.path(), "deploy", &object, version);
            assert!(
                linked.status_ok,
                "{version}: link failed:\n{}",
                linked.stderr
            );
            assert!(
                !linked.stderr.contains(MISMATCH) && !linked.stderr.contains("ld: warning"),
                "{version}: ld64 warned:\n{}",
                linked.stderr
            );
            assert_eq!(linked.run_ok, Some(true), "{version}: wrong result");
        }
    }

    /// The pre-existing behavior this closes: an unversioned object claims
    /// macOS 14.0 and ld64 warns when the link targets 12.0.
    #[test]
    fn negative_control_default_object_warns_when_linked_for_an_older_target() {
        let directory = tempfile::tempdir().unwrap();
        let object = compile_for("aarch64-apple-darwin");
        let linked = link_and_run(directory.path(), "default", &object, "12.0");
        assert!(linked.status_ok, "link failed:\n{}", linked.stderr);
        assert!(
            linked.stderr.contains(MISMATCH),
            "ld64 must warn about the 14.0 object in a 12.0 link:\n{}",
            linked.stderr
        );
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
