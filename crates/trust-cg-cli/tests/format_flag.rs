// trust-cg-cli/tests/format_flag.rs - Integration tests for the --format flag (#414)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Per `designs/2026-04-16-trust_ir-transport-architecture.md` Layer 4 and
// issue #414, the CLI defaults to binary `.tmbc` input. JSON is retained
// only as `--format=json`. These tests exercise the CLI binary end-to-end
// for the three acceptance-criteria cases:
//
//   1. A `.tmbc` file with no flag compiles successfully (default).
//   2. A `.json` file without `--format=json` errors out with a message
//      naming the `--format=json` escape hatch.
//   3. A `.json` file with `--format=json` compiles successfully.
//
// A fourth test covers the legacy `--format=auto` mode for backcompat.

use std::path::PathBuf;
use std::process::Command;

use trust_cg_codegen::pipeline::encode_tmbc;
use trust_ir::{Module as TrustIrModule, Ty};
use trust_ir_build::ModuleBuilder;

const ELFCLASS64: u8 = 2;
const ELFDATA2LSB: u8 = 1;
const ET_REL: u16 = 1;
const EM_X86_64: u16 = 0x3E;
const IMAGE_FILE_MACHINE_AMD64: u16 = 0x8664;
const MH_MAGIC_64: u32 = 0xFEED_FACF;
const CPU_TYPE_X86_64: u32 = 0x0100_0007;
const MH_OBJECT: u32 = 1;

/// Build a minimal `fn return_42() -> i64 { 42 }` trust_ir module.
fn make_test_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("cli_format_flag_test");
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("_return_42", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let r = fb.iconst(Ty::I64, 42);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

/// Create a fresh, empty scratch directory under the OS temp dir.
///
/// Uses `process::id` + a test-name suffix so parallel `cargo test`
/// invocations do not collide.
fn scratch_dir(test_name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_cli_format_{}_{}",
        test_name,
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

/// Path to the compiled `trust-cg` binary for this test run.
fn trust_cg_bin() -> PathBuf {
    // `CARGO_BIN_EXE_<name>` is injected by cargo for integration tests
    // of packages that declare `[[bin]]`s.
    PathBuf::from(env!("CARGO_BIN_EXE_trust-cg"))
}

fn read_u16(bytes: &[u8], offset: usize) -> u16 {
    u16::from_le_bytes([bytes[offset], bytes[offset + 1]])
}

fn read_u32(bytes: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes([
        bytes[offset],
        bytes[offset + 1],
        bytes[offset + 2],
        bytes[offset + 3],
    ])
}

fn assert_elf64_x86_64_relocatable(bytes: &[u8]) {
    assert!(bytes.len() >= 64, "ELF object too small: {}", bytes.len());
    assert_eq!(&bytes[0..4], b"\x7FELF", "ELF magic");
    assert_eq!(bytes[4], ELFCLASS64, "ELF class");
    assert_eq!(bytes[5], ELFDATA2LSB, "ELF data encoding");
    assert_eq!(read_u16(bytes, 16), ET_REL, "ELF type");
    assert_eq!(read_u16(bytes, 18), EM_X86_64, "ELF machine");
}

fn assert_coff_amd64_object(bytes: &[u8]) {
    assert!(
        bytes.len() >= 20,
        "COFF object too small for file header: {}",
        bytes.len()
    );
    assert_eq!(read_u16(bytes, 0), IMAGE_FILE_MACHINE_AMD64, "COFF machine");
    assert_ne!(read_u16(bytes, 2), 0, "COFF section count");
}

fn assert_macho64_x86_64_object(bytes: &[u8]) {
    assert!(
        bytes.len() >= 32,
        "Mach-O object too small for header: {}",
        bytes.len()
    );
    assert_eq!(read_u32(bytes, 0), MH_MAGIC_64, "Mach-O magic");
    assert_eq!(read_u32(bytes, 4), CPU_TYPE_X86_64, "Mach-O CPU type");
    assert_eq!(read_u32(bytes, 12), MH_OBJECT, "Mach-O file type");
}

// ---------------------------------------------------------------------------
// Case 1: binary default works with no flag.
// ---------------------------------------------------------------------------

#[test]
fn cli_binary_default_accepts_tmbc() {
    let dir = scratch_dir("binary_default");
    let tmbc_path = dir.join("module.tmbc");
    let out_path = dir.join("module.o");

    let module = make_test_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    let status = Command::new(trust_cg_bin())
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&status.stderr);
    assert!(
        status.status.success(),
        "binary-default tMBC compile should succeed. stderr: {}",
        stderr
    );
    assert!(
        out_path.exists(),
        "expected object file at {} after successful compile",
        out_path.display()
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
#[allow(clippy::type_complexity)] // Rows bind a target, output name, and format oracle.
fn cli_explicit_x86_targets_emit_requested_object_formats() {
    let dir = scratch_dir("explicit_x86_targets");
    let tmbc_path = dir.join("module.tmbc");
    let module = make_test_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    let cases: [(&str, &str, fn(&[u8])); 3] = [
        (
            "x86_64-pc-windows-msvc",
            "windows.obj",
            assert_coff_amd64_object,
        ),
        (
            "x86_64-unknown-linux-gnu",
            "linux.o",
            assert_elf64_x86_64_relocatable,
        ),
        (
            "x86_64-apple-darwin",
            "darwin.o",
            assert_macho64_x86_64_object,
        ),
    ];

    for (target, output_name, assert_object) in cases {
        let out_path = dir.join(output_name);
        let output = Command::new(trust_cg_bin())
            .arg("-c")
            .arg("--target")
            .arg(target)
            .arg("-o")
            .arg(&out_path)
            .arg(&tmbc_path)
            .output()
            .unwrap_or_else(|error| panic!("run trust-cg for target {target}: {error}"));

        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success(),
            "explicit target {target} should compile. stderr:\n{stderr}"
        );
        let bytes = std::fs::read(&out_path)
            .unwrap_or_else(|error| panic!("read output for {target}: {error}"));
        assert_object(&bytes);
    }

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Case 2: JSON file without --format=json errors clearly.
// ---------------------------------------------------------------------------

#[test]
fn cli_binary_default_rejects_json_with_hint() {
    let dir = scratch_dir("binary_rejects_json");
    let json_path = dir.join("module.json");
    let out_path = dir.join("module.o");

    let module = make_test_module();
    let json = serde_json::to_string_pretty(&module).expect("serialize JSON");
    std::fs::write(&json_path, json).expect("write json");

    let output = Command::new(trust_cg_bin())
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .arg(&json_path)
        .output()
        .expect("run trust-cg");

    assert!(
        !output.status.success(),
        "JSON without --format=json must fail under the new default"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("--format=json"),
        "error message must reference --format=json as the escape hatch.\n\
         actual stderr:\n{}",
        stderr
    );
    assert!(
        stderr.contains("tMBC") || stderr.contains("binary"),
        "error message must explain that binary is the new default.\n\
         actual stderr:\n{}",
        stderr
    );
    assert!(
        !out_path.exists(),
        "no object file should be produced on failed load; found {}",
        out_path.display()
    );

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Case 3: JSON file with --format=json works.
// ---------------------------------------------------------------------------

#[test]
fn cli_format_json_accepts_json_input() {
    let dir = scratch_dir("format_json");
    let json_path = dir.join("module.json");
    let out_path = dir.join("module.o");

    let module = make_test_module();
    let json = serde_json::to_string_pretty(&module).expect("serialize JSON");
    std::fs::write(&json_path, json).expect("write json");

    let output = Command::new(trust_cg_bin())
        .arg("--format=json")
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .arg(&json_path)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "--format=json with a JSON file should succeed. stderr: {}",
        stderr
    );
    assert!(
        out_path.exists(),
        "expected object file at {} after successful JSON compile",
        out_path.display()
    );

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Case 4 (bonus): --format=auto restores legacy extension/magic sniffing.
// ---------------------------------------------------------------------------

#[test]
fn cli_format_auto_accepts_both() {
    let dir = scratch_dir("format_auto");
    let json_path = dir.join("module.json");
    let tmbc_path = dir.join("module.tmbc");
    let out_json = dir.join("json.o");
    let out_tmbc = dir.join("tmbc.o");

    let module = make_test_module();
    std::fs::write(
        &json_path,
        serde_json::to_string_pretty(&module).expect("serialize JSON"),
    )
    .expect("write json");
    std::fs::write(&tmbc_path, encode_tmbc(&module).expect("encode tMBC")).expect("write tmbc");

    // JSON via --format=auto.
    let out_j = Command::new(trust_cg_bin())
        .arg("--format=auto")
        .arg("-c")
        .arg("-o")
        .arg(&out_json)
        .arg(&json_path)
        .output()
        .expect("run trust-cg (auto, json)");
    assert!(
        out_j.status.success(),
        "--format=auto should accept .json files. stderr: {}",
        String::from_utf8_lossy(&out_j.stderr)
    );

    // .tmbc via --format=auto.
    let out_b = Command::new(trust_cg_bin())
        .arg("--format=auto")
        .arg("-c")
        .arg("-o")
        .arg(&out_tmbc)
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg (auto, tmbc)");
    assert!(
        out_b.status.success(),
        "--format=auto should accept .tmbc files. stderr: {}",
        String::from_utf8_lossy(&out_b.stderr)
    );

    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Case 5 (bonus): deprecated --input-json still works and emits a warning.
// ---------------------------------------------------------------------------

#[test]
fn cli_input_json_is_deprecated_alias() {
    let dir = scratch_dir("input_json_alias");
    let json_path = dir.join("module.json");
    let out_path = dir.join("module.o");

    let module = make_test_module();
    std::fs::write(
        &json_path,
        serde_json::to_string_pretty(&module).expect("serialize JSON"),
    )
    .expect("write json");

    let output = Command::new(trust_cg_bin())
        .arg("--input-json")
        .arg(&json_path)
        .arg("-c")
        .arg("-o")
        .arg(&out_path)
        .output()
        .expect("run trust-cg (--input-json)");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "--input-json must still work as a deprecated alias. stderr: {}",
        stderr
    );
    assert!(
        stderr.contains("deprecated") && stderr.contains("--format=json"),
        "deprecation warning should mention --format=json. stderr: {}",
        stderr
    );

    let _ = std::fs::remove_dir_all(&dir);
}
