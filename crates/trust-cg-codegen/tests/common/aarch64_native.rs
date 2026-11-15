// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native C differential helpers with explicit AArch64 OS/ABI selection.

use std::fs;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};

#[path = "rosetta.rs"]
pub mod process;

/// Whether this host can LINK AND RUN an AArch64 binary.
///
/// A pure `cfg!`, so it is false on every host where the native half of a
/// differential is impossible rather than merely unconfigured. A caller whose
/// test has host-independent work to do consults it FIRST and does not attempt
/// the native run, because [`link_run`]'s `SKIP:` marker is read by
/// `scripts/soundness_check.sh` as a runtime skip and fails the gate — correct
/// for a test that is nothing but the native run, wrong for one whose other
/// rows are its evidence on this host. On an AArch64 host this is true and
/// nothing is gated: a missing `cc` or a failed link still makes `link_run`
/// return `None`, and the caller's own count assertion still fails.
pub fn can_execute() -> bool {
    cfg!(all(
        target_arch = "aarch64",
        any(
            target_os = "macos",
            all(target_os = "linux", target_env = "gnu")
        )
    ))
}

pub fn compile(module: &trust_ir::Module, opt_level: OptLevel) -> Vec<u8> {
    try_compile(module, opt_level).expect("AArch64 differential fixture must compile")
}

/// The triple [`try_compile`] compiles for: the native AArch64 Linux GNU host,
/// else Darwin (the historical object-only coverage on non-native hosts).
fn compile_triple() -> &'static str {
    if cfg!(all(
        target_arch = "aarch64",
        target_os = "linux",
        target_env = "gnu"
    )) {
        "aarch64-unknown-linux-gnu"
    } else {
        "aarch64-apple-darwin"
    }
}

/// `module` pinned to the target [`try_compile`] compiles it for.
pub fn pinned(module: &trust_ir::Module) -> trust_ir::Module {
    let mut module = module.clone();
    let target_info = trust_ir::TargetInfo {
        triple: compile_triple().into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    };
    if let Some(existing) = &module.target_info {
        assert_eq!(existing, &target_info, "fixture targets a different ABI");
    }
    module.target_info = Some(target_info);
    module
}

pub fn try_compile(module: &trust_ir::Module, opt_level: OptLevel) -> Result<Vec<u8>, String> {
    let triple = compile_triple();
    let module = pinned(module);
    let result = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&module)
    .map_err(|error| format!("{error:?}"))?;
    assert!(!result.object_code.is_empty());
    if triple.ends_with("linux-gnu") {
        assert_eq!(&result.object_code[..4], b"\x7fELF");
        assert_eq!(
            u16::from_le_bytes([result.object_code[18], result.object_code[19]]),
            183
        );
    }
    Ok(result.object_code)
}

pub fn link_run(tag: &str, object: &[u8], driver: &str) -> Option<i32> {
    if !can_execute() {
        eprintln!("SKIP: native AArch64 Linux GNU or macOS is required");
        return None;
    }
    // Tests of one binary run on parallel threads and the clock can repeat a
    // reading, so a per-process sequence number keeps the directories apart.
    static NEXT_DIR: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let sequence = NEXT_DIR.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "trust-cg-native-{}-{stamp}-{sequence}",
        std::process::id()
    ));
    fs::create_dir(&dir).unwrap();
    let object_path = dir.join("module.o");
    let driver_path = dir.join("driver.c");
    let binary_path = dir.join("driver");
    fs::write(&object_path, object).unwrap();
    fs::write(&driver_path, driver).unwrap();
    // An optimized reference is essential: an O0 C callee can re-narrow its
    // arguments and accidentally mask a caller's extension/placement defect.
    let link = process::command_output_with_timeout(
        Command::new("cc")
            .arg("-O2")
            .arg(&driver_path)
            .arg(&object_path)
            .arg("-lm")
            .arg("-o")
            .arg(&binary_path),
        process::codegen_link_timeout(),
    )
    .expect("native C compiler is required");
    assert!(
        !link.timed_out && link.output.status.success(),
        "{tag}: link failed; files={dir:?}\n{}",
        String::from_utf8_lossy(&link.output.stderr)
    );
    let run = process::run_executable_with_timeout(&binary_path, process::codegen_run_timeout())
        .expect("run native differential fixture");
    assert!(!run.timed_out, "{tag}: execution timed out; files={dir:?}");
    if !run.output.status.success() {
        panic!(
            "{tag}: native mismatch {}; files={dir:?}\nstdout={}\nstderr={}",
            run.output.status,
            String::from_utf8_lossy(&run.output.stdout),
            String::from_utf8_lossy(&run.output.stderr)
        );
    }
    fs::remove_dir_all(&dir).unwrap();
    Some(0)
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused. It is the policy
/// [`try_compile`] states, so a caller judges trust-ir's admission of a
/// refused fixture under it.
pub fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
