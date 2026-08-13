// trust-cg-codegen integration test: Mach-O object file writer
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Verifies that the MachOWriter produces valid Mach-O .o files
// that macOS system tools (otool, nm) can parse.

use trust_cg_codegen::macho::constants::*;
use trust_cg_codegen::macho::{MachOWriter, Relocation};

use std::io::{ErrorKind, Write};
use std::process::Command;

/// Write bytes to a temp file and return the path.
fn write_temp_o(bytes: &[u8], name: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir();
    let path = dir.join(format!("trust_cg_test_{}.o", name));
    let mut f = std::fs::File::create(&path).expect("failed to create temp file");
    f.write_all(bytes).expect("failed to write temp file");
    path
}

fn command_text(output: &std::process::Output) -> String {
    format!(
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

fn tool_lacks_macho_support(output: &std::process::Output) -> bool {
    let text = command_text(output).to_lowercase();
    text.contains("file format not recognized")
        || text.contains("unknown file type")
        || text.contains("unsupported file format")
        || text.contains("unsupported object file")
        || text.contains("not a mach-o file")
        || text.contains("invalid bfd target")
}

fn skip_macho_tool_test(reason: impl std::fmt::Display) {
    eprintln!("SKIP: Mach-O external tool inspection unavailable: {reason}");
}

/// Run otool -l or a compatible Mach-O load-command inspector and return stdout.
fn run_macho_load_commands(path: &std::path::Path) -> Option<String> {
    let output = match Command::new("otool")
        .args(["-l", path.to_str().unwrap()])
        .output()
    {
        Ok(output) => output,
        Err(err) if err.kind() == ErrorKind::NotFound => {
            return run_llvm_objdump_load_commands(path);
        }
        Err(err) => panic!("failed to run otool -l: {err}"),
    };
    assert!(
        output.status.success(),
        "otool -l failed: {}",
        command_text(&output)
    );
    Some(String::from_utf8_lossy(&output.stdout).to_string())
}

fn run_llvm_objdump_load_commands(path: &std::path::Path) -> Option<String> {
    let output = match Command::new("llvm-objdump")
        .args(["--macho", "--private-headers", path.to_str().unwrap()])
        .output()
    {
        Ok(output) => output,
        Err(err) if err.kind() == ErrorKind::NotFound => {
            skip_macho_tool_test("otool and llvm-objdump are not installed");
            return None;
        }
        Err(err) => panic!("failed to run llvm-objdump --macho --private-headers: {err}"),
    };

    if output.status.success() {
        return Some(String::from_utf8_lossy(&output.stdout).to_string());
    }

    if tool_lacks_macho_support(&output) {
        skip_macho_tool_test("llvm-objdump does not support Mach-O objects");
        return None;
    }

    panic!(
        "llvm-objdump --macho --private-headers failed: {}",
        command_text(&output)
    );
}

/// Run nm on a .o file and return stdout.
fn run_nm(path: &std::path::Path) -> Option<String> {
    let mut missing = Vec::new();
    let mut incompatible = Vec::new();

    for tool in ["nm", "llvm-nm"] {
        let output = match Command::new(tool).args([path.to_str().unwrap()]).output() {
            Ok(output) => output,
            Err(err) if err.kind() == ErrorKind::NotFound => {
                missing.push(tool);
                continue;
            }
            Err(err) => panic!("failed to run {tool}: {err}"),
        };

        if output.status.success() {
            return Some(String::from_utf8_lossy(&output.stdout).to_string());
        }

        if tool_lacks_macho_support(&output) {
            incompatible.push(tool);
            continue;
        }

        panic!("{tool} failed: {}", command_text(&output));
    }

    let missing = if missing.is_empty() {
        "none".to_string()
    } else {
        missing.join(", ")
    };
    let incompatible = if incompatible.is_empty() {
        "none".to_string()
    } else {
        incompatible.join(", ")
    };
    skip_macho_tool_test(format!(
        "no Mach-O-capable nm found (missing: {missing}; incompatible: {incompatible})"
    ));
    None
}

#[test]
fn test_minimal_text_section() {
    let mut writer = MachOWriter::new();

    // ARM64 NOP = 0xD503201F, 4 instructions
    let nop = 0xD503201Fu32;
    let mut code = Vec::new();
    for _ in 0..4 {
        code.extend_from_slice(&nop.to_le_bytes());
    }
    writer.add_text_section(&code);
    writer.add_symbol("_main", 1, 0, true).unwrap();

    let bytes = writer.write().unwrap();
    let path = write_temp_o(&bytes, "minimal_text");

    // Verify Mach-O magic
    assert_eq!(&bytes[0..4], &[0xCF, 0xFA, 0xED, 0xFE]);

    // Verify file type is MH_OBJECT
    let filetype = u32::from_le_bytes([bytes[12], bytes[13], bytes[14], bytes[15]]);
    assert_eq!(filetype, MH_OBJECT);

    if let Some(load_out) = run_macho_load_commands(&path) {
        // Verify load commands are present
        assert!(
            load_out.contains("LC_SEGMENT_64"),
            "Missing LC_SEGMENT_64 in Mach-O load command output"
        );
        assert!(
            load_out.contains("LC_BUILD_VERSION"),
            "Missing LC_BUILD_VERSION in Mach-O load command output"
        );
        assert!(
            load_out.contains("LC_SYMTAB"),
            "Missing LC_SYMTAB in Mach-O load command output"
        );
        assert!(
            load_out.contains("LC_DYSYMTAB"),
            "Missing LC_DYSYMTAB in Mach-O load command output"
        );

        // Verify sections
        assert!(load_out.contains("__text"), "Missing __text section");
        assert!(load_out.contains("__TEXT"), "Missing __TEXT segment");

        // Verify section attributes: pure instructions + some instructions
        assert!(
            load_out.contains("0x80000400")
                || (load_out.contains("PURE_INSTRUCTIONS")
                    && load_out.contains("SOME_INSTRUCTIONS")),
            "Missing expected section flags for __text (S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS)"
        );
    }

    // Verify symbol table via nm
    if let Some(nm_out) = run_nm(&path) {
        assert!(
            nm_out.contains("_main"),
            "Missing _main symbol in nm output"
        );
        assert!(
            nm_out.contains(" T "),
            "_main should be in text section (T)"
        );
    }

    // Clean up
    std::fs::remove_file(&path).ok();
}

#[test]
fn test_text_and_data_sections() {
    let mut writer = MachOWriter::new();

    // ARM64 RET = 0xD65F03C0
    let ret_instr = 0xD65F03C0u32;
    writer.add_text_section(&ret_instr.to_le_bytes());

    // Data section with some initialized data
    writer.add_data_section(&[0x48, 0x65, 0x6C, 0x6C, 0x6F, 0x00, 0x00, 0x00]);

    writer.add_symbol("_func", 1, 0, true).unwrap();
    writer.add_symbol("_hello", 2, 0, true).unwrap();

    let bytes = writer.write().unwrap();
    let path = write_temp_o(&bytes, "text_and_data");

    // Both sections present
    if let Some(load_out) = run_macho_load_commands(&path) {
        assert!(load_out.contains("__text"), "Missing __text");
        assert!(load_out.contains("__data"), "Missing __data");
        assert!(load_out.contains("__TEXT"), "Missing __TEXT segment");
        assert!(load_out.contains("__DATA"), "Missing __DATA segment");

        // nsects should be 2
        assert!(
            load_out.contains("nsects 2"),
            "Expected 2 sections in segment"
        );
    }

    // Both symbols visible
    if let Some(nm_out) = run_nm(&path) {
        assert!(nm_out.contains("_func"), "Missing _func symbol");
        assert!(nm_out.contains("_hello"), "Missing _hello symbol");
    }

    std::fs::remove_file(&path).ok();
}

#[test]
fn test_local_and_global_symbols() {
    let mut writer = MachOWriter::new();

    let nop = 0xD503201Fu32;
    let mut code = Vec::new();
    for _ in 0..8 {
        code.extend_from_slice(&nop.to_le_bytes());
    }
    writer.add_text_section(&code);

    // Add both local and global symbols
    writer.add_symbol("_local_helper", 1, 0, false).unwrap();
    writer.add_symbol("_main", 1, 16, true).unwrap();

    let bytes = writer.write().unwrap();
    let path = write_temp_o(&bytes, "symbols");

    // Verify dysymtab shows correct partitioning
    if let Some(load_out) = run_macho_load_commands(&path) {
        assert!(load_out.contains("nlocalsym 1"), "Expected 1 local symbol");
        assert!(
            load_out.contains("nextdefsym 1"),
            "Expected 1 external defined symbol"
        );
    }

    // _main should be global (T), _local_helper should be local (t)
    if let Some(nm_out) = run_nm(&path) {
        assert!(nm_out.contains("_main"), "Missing _main");
        assert!(nm_out.contains("_local_helper"), "Missing _local_helper");
    }

    std::fs::remove_file(&path).ok();
}

#[test]
fn test_relocation_entries() {
    let mut writer = MachOWriter::new();

    // BL instruction (will need relocation)
    let bl_instr = 0x94000000u32; // BL #0
    let mut code = Vec::new();
    code.extend_from_slice(&bl_instr.to_le_bytes());
    // Some NOPs after
    let nop = 0xD503201Fu32;
    for _ in 0..3 {
        code.extend_from_slice(&nop.to_le_bytes());
    }
    writer.add_text_section(&code);

    writer.add_symbol("_caller", 1, 0, true).unwrap();
    writer.add_symbol("_callee", 0, 0, true).unwrap(); // undefined external

    // Add a BRANCH26 relocation at offset 0 referencing symbol index 1 (_callee)
    writer
        .add_relocation(0, Relocation::branch26(0, 1))
        .unwrap();

    let bytes = writer.write().unwrap();
    let path = write_temp_o(&bytes, "reloc");

    if let Some(load_out) = run_macho_load_commands(&path) {
        // Section should have 1 relocation
        assert!(
            load_out.contains("nreloc 1"),
            "Expected 1 relocation entry, Mach-O load command output:\n{}",
            load_out
        );

        // reloff should be non-zero (use leading whitespace to avoid matching "extreloff 0")
        assert!(
            !load_out.contains("    reloff 0\n"),
            "reloff should not be 0 when there are relocations, Mach-O load command output:\n{}",
            load_out
        );
    }

    std::fs::remove_file(&path).ok();
}

#[test]
fn test_empty_object() {
    let writer = MachOWriter::new();
    let bytes = writer.write().unwrap();
    let path = write_temp_o(&bytes, "empty");

    // Even an empty object should be valid Mach-O
    assert_eq!(&bytes[0..4], &[0xCF, 0xFA, 0xED, 0xFE]);
    if let Some(load_out) = run_macho_load_commands(&path) {
        assert!(
            load_out.contains("LC_SEGMENT_64"),
            "Empty object should still have segment command"
        );
    }

    std::fs::remove_file(&path).ok();
}

#[test]
fn test_header_flags() {
    let mut writer = MachOWriter::new();
    writer.add_text_section(&[0x1F, 0x20, 0x03, 0xD5]);

    let bytes = writer.write().unwrap();

    // flags field is at offset 24 in the header
    let flags = u32::from_le_bytes([bytes[24], bytes[25], bytes[26], bytes[27]]);
    assert_eq!(
        flags, MH_SUBSECTIONS_VIA_SYMBOLS,
        "Header flags should be MH_SUBSECTIONS_VIA_SYMBOLS"
    );
}

#[test]
fn test_build_version_platform() {
    let mut writer = MachOWriter::new();
    writer.add_text_section(&[0x1F, 0x20, 0x03, 0xD5]);

    let bytes = writer.write().unwrap();
    let path = write_temp_o(&bytes, "build_version");

    if let Some(load_out) = run_macho_load_commands(&path) {
        assert!(
            load_out.contains("platform 1") || load_out.to_lowercase().contains("platform macos"),
            "Build version should target macOS (platform 1)"
        );
    }

    std::fs::remove_file(&path).ok();
}
