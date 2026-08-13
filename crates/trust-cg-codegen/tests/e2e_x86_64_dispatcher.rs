// trust-cg-codegen/tests/e2e_x86_64_dispatcher.rs - #340 x86-64 dispatcher wiring
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Verifies that `Compiler::compile` honors `config.target` and routes to
// the x86-64 backend (X86Pipeline) when `Target::X86_64` is selected.
//
// Part of #340 — x86-64 cross-platform support for ty.
//
// Prior to #340-A the dispatcher was hard-wired to the AArch64 path and
// the x86-64 pipeline was unreachable from the public Compiler API. These
// tests pin that behavior: for the same trust_ir input, AArch64 and x86-64
// dispatch must produce distinct object bytes. Host-default x86-64 public AOT
// is OS-aware, while Mach-O-specific checks request an explicit Darwin target.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

mod common;

use common::rosetta::{codegen_probe_timeout, codegen_run_timeout, run_executable_with_timeout};
use trust_cg_codegen::coff::IMAGE_FILE_MACHINE_AMD64;
use trust_cg_codegen::compiler::{CompilationResult, CompileError, Compiler, CompilerConfig};
use trust_cg_codegen::macho::constants as macho_consts;
use trust_cg_codegen::macho::linker::MachOParser;
use trust_cg_codegen::pipeline::{OptLevel, PipelineError};
use trust_cg_codegen::target::{Target, TargetSpec};

use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, FuncTyId,
    Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
};

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

/// Build a single-function `fn add(a: i64, b: i64) -> i64 { a + b }` module.
///
/// Shape mirrors `build_simple_add` in e2e_pipeline_integration.rs so the
/// trust_ir input is identical to the AArch64 golden path; only the dispatch
/// target changes between test variants.
fn build_add_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test_x86_dispatch");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "add", ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

/// Build a two-function caller/callee module:
///
/// `callee() -> i64 { 42 }`
/// `caller() -> i64 { callee() }`
fn build_caller_callee_const_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test_x86_call");

    let ft_void_i64 = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let mut callee = TrustIrFunction::new(FuncId::new(0), "callee", ft_void_i64, BlockId::new(0));
    callee.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(42),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    }];
    module.add_function(callee);

    let mut caller = TrustIrFunction::new(FuncId::new(1), "caller", ft_void_i64, BlockId::new(0));
    caller.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![],
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    }];
    module.add_function(caller);

    module
}

/// Mach-O 64-bit magic (little-endian): 0xFEEDFACF.
const MH_MAGIC_64: u32 = 0xFEEDFACF;
/// Mach-O CPU_TYPE_ARM64.
const CPU_TYPE_ARM64: u32 = 0x0100_000C;
/// Mach-O CPU_TYPE_X86_64.
const CPU_TYPE_X86_64: u32 = 0x0100_0007;

fn read_u16_le(bytes: &[u8], offset: usize) -> u16 {
    u16::from_le_bytes([bytes[offset], bytes[offset + 1]])
}

fn read_u32_le(bytes: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes([
        bytes[offset],
        bytes[offset + 1],
        bytes[offset + 2],
        bytes[offset + 3],
    ])
}

fn read_u64_le(bytes: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes([
        bytes[offset],
        bytes[offset + 1],
        bytes[offset + 2],
        bytes[offset + 3],
        bytes[offset + 4],
        bytes[offset + 5],
        bytes[offset + 6],
        bytes[offset + 7],
    ])
}

fn assert_x86_64_macho_object(bytes: &[u8], context: &str) {
    assert!(
        bytes.len() >= 32,
        "{context} Mach-O must have a full mach_header_64 (got {} bytes)",
        bytes.len()
    );
    let magic = read_u32_le(bytes, 0);
    assert_eq!(
        magic, MH_MAGIC_64,
        "{context} object should have Mach-O 64-bit magic; got 0x{:08X}",
        magic
    );
    let cpu_type = read_u32_le(bytes, 4);
    assert_eq!(
        cpu_type, CPU_TYPE_X86_64,
        "{context} dispatch must emit CPU_TYPE_X86_64 (0x{:08X}); got 0x{:08X}",
        CPU_TYPE_X86_64, cpu_type
    );
}

fn assert_x86_64_elf_object(bytes: &[u8], context: &str) {
    assert!(
        bytes.len() >= 20,
        "{context} ELF object too small for header sanity (got {} bytes)",
        bytes.len()
    );
    assert_eq!(
        &bytes[0..4],
        b"\x7FELF",
        "{context} should emit an ELF object"
    );
    assert_eq!(bytes[4], 2, "{context} ELF class should be 64-bit");
    assert_eq!(bytes[5], 1, "{context} ELF data encoding should be LSB");
    assert_eq!(
        read_u16_le(bytes, 16),
        1,
        "{context} ELF file type should be ET_REL"
    );
    assert_eq!(
        read_u16_le(bytes, 18),
        62,
        "{context} ELF machine should be EM_X86_64"
    );
    assert_ne!(
        read_u32_le(bytes, 0),
        MH_MAGIC_64,
        "{context} ELF path must not silently emit Mach-O"
    );
}

fn assert_x86_64_coff_object(bytes: &[u8], context: &str) {
    assert!(
        bytes.len() >= 20,
        "{context} COFF object too small for file header (got {} bytes)",
        bytes.len()
    );
    assert_eq!(
        read_u16_le(bytes, 0),
        IMAGE_FILE_MACHINE_AMD64,
        "{context} COFF machine should be IMAGE_FILE_MACHINE_AMD64"
    );
    assert!(
        read_u16_le(bytes, 2) > 0,
        "{context} COFF object should contain at least one section"
    );
    assert_ne!(
        &bytes[0..4],
        b"\x7FELF",
        "{context} Windows path must not silently emit ELF"
    );
    assert_ne!(
        read_u32_le(bytes, 0),
        MH_MAGIC_64,
        "{context} Windows path must not silently emit Mach-O"
    );
}

fn assert_windows_coff_unwind_fail_closed(err: CompileError) {
    match err {
        CompileError::Pipeline(PipelineError::TargetObjectUnsupported {
            target,
            format,
            reason,
        }) => {
            assert_eq!(target, "x86_64-pc-windows-msvc");
            assert_eq!(format, "COFF");
            assert!(
                reason.contains(".pdata/.xdata unwind metadata"),
                "Windows COFF fail-closed diagnostic should name missing unwind metadata, got {reason}"
            );
        }
        other => panic!("expected typed Windows COFF unwind rejection, got {other:?}"),
    }
}

fn expect_host_x86_64_public_aot_result(
    result: Result<CompilationResult, CompileError>,
) -> Option<CompilationResult> {
    match std::env::consts::OS {
        "linux" | "android" | "freebsd" | "netbsd" | "openbsd" | "dragonfly" => {
            let result = result.expect("x86 public AOT should compile to ELF on this host");
            assert_x86_64_elf_object(&result.object_code, "host x86-64 public AOT");
            Some(result)
        }
        "macos" => {
            let result = result.expect("x86 public AOT should compile to Mach-O on macOS");
            assert_x86_64_macho_object(&result.object_code, "host x86-64 public AOT");
            Some(result)
        }
        "windows" => match result {
            Ok(result) => {
                assert_x86_64_coff_object(&result.object_code, "host x86-64 public AOT");
                Some(result)
            }
            Err(err) => {
                assert_windows_coff_unwind_fail_closed(err);
                None
            }
        },
        other => match result {
            Err(CompileError::X86AotObjectFormatUnsupported {
                target_os,
                required_format,
                context,
            }) => {
                assert_eq!(target_os, other);
                assert_eq!(required_format, "native object format");
                assert!(
                    context.contains("no x86-64 AOT object emitter"),
                    "unsupported host diagnostic should explain the fail-closed object-format boundary, got {context}"
                );
                None
            }
            Err(err) => panic!(
                "unsupported host OS {other} should fail closed by object format, got {err:?}"
            ),
            Ok(result) => panic!(
                "unsupported host OS {other} should fail closed, emitted {} bytes",
                result.object_code.len()
            ),
        },
    }
}

fn x86_64_darwin_target_spec() -> TargetSpec {
    TargetSpec::parse("x86_64-apple-darwin").expect("parse x86_64-apple-darwin target spec")
}

fn x86_64_darwin_compiler(config: CompilerConfig) -> Compiler {
    Compiler::new_for_target_spec(config, x86_64_darwin_target_spec())
}

fn read_name16(bytes: &[u8], offset: usize) -> String {
    let raw = &bytes[offset..offset + 16];
    let end = raw.iter().position(|&b| b == 0).unwrap_or(raw.len());
    String::from_utf8_lossy(&raw[..end]).into_owned()
}

#[derive(Debug)]
struct RawMachORelocation {
    offset: u32,
    symbol_index: u32,
    pc_relative: bool,
    length: u8,
    is_extern: bool,
    type_val: u8,
}

fn decode_raw_relocation(bytes: &[u8], offset: usize) -> RawMachORelocation {
    let r_word0 = read_u32_le(bytes, offset);
    let r_word1 = read_u32_le(bytes, offset + 4);

    RawMachORelocation {
        offset: r_word0,
        symbol_index: r_word1 & 0x00FF_FFFF,
        pc_relative: (r_word1 >> 24) & 1 != 0,
        length: ((r_word1 >> 25) & 3) as u8,
        is_extern: (r_word1 >> 27) & 1 != 0,
        type_val: ((r_word1 >> 28) & 0xF) as u8,
    }
}

fn text_relocations(bytes: &[u8]) -> Vec<RawMachORelocation> {
    assert!(
        bytes.len() >= macho_consts::MACH_HEADER_64_SIZE as usize,
        "Mach-O object too small: {} bytes",
        bytes.len()
    );
    assert_eq!(read_u32_le(bytes, 0), macho_consts::MH_MAGIC_64);

    let ncmds = read_u32_le(bytes, 16) as usize;
    let sizeofcmds = read_u32_le(bytes, 20) as usize;
    let mut cmd_offset = macho_consts::MACH_HEADER_64_SIZE as usize;
    let commands_end = cmd_offset + sizeofcmds;

    for _ in 0..ncmds {
        assert!(
            cmd_offset + 8 <= bytes.len(),
            "load command header out of bounds at {cmd_offset:#x}"
        );
        assert!(
            cmd_offset + 8 <= commands_end,
            "load command header exceeds sizeofcmds at {cmd_offset:#x}"
        );
        let cmd = read_u32_le(bytes, cmd_offset);
        let cmdsize = read_u32_le(bytes, cmd_offset + 4) as usize;
        assert!(cmdsize >= 8, "load command has invalid size {cmdsize}");
        assert!(
            cmd_offset + cmdsize <= bytes.len(),
            "load command out of bounds at {cmd_offset:#x}, size {cmdsize:#x}"
        );

        if cmd == macho_consts::LC_SEGMENT_64 {
            let nsects = read_u32_le(bytes, cmd_offset + 64) as usize;
            let mut sec_offset = cmd_offset + macho_consts::SEGMENT_COMMAND_64_SIZE as usize;

            for _ in 0..nsects {
                assert!(
                    sec_offset + macho_consts::SECTION_64_SIZE as usize <= bytes.len(),
                    "section header out of bounds at {sec_offset:#x}"
                );
                let sectname = read_name16(bytes, sec_offset);
                let segname = read_name16(bytes, sec_offset + 16);
                if sectname == "__text" && segname == "__TEXT" {
                    let sec_size = read_u64_le(bytes, sec_offset + 40) as usize;
                    let sec_fileoff = read_u32_le(bytes, sec_offset + 48) as usize;
                    let sec_reloff = read_u32_le(bytes, sec_offset + 56) as usize;
                    let sec_nreloc = read_u32_le(bytes, sec_offset + 60) as usize;
                    assert!(
                        sec_fileoff + sec_size <= bytes.len(),
                        "__text contents out of bounds"
                    );
                    assert!(
                        sec_reloff + sec_nreloc * macho_consts::RELOCATION_INFO_SIZE as usize
                            <= bytes.len(),
                        "__text relocations out of bounds"
                    );

                    return (0..sec_nreloc)
                        .map(|i| {
                            decode_raw_relocation(
                                bytes,
                                sec_reloff + i * macho_consts::RELOCATION_INFO_SIZE as usize,
                            )
                        })
                        .collect();
                }

                sec_offset += macho_consts::SECTION_64_SIZE as usize;
            }
        }

        cmd_offset += cmdsize;
    }

    panic!("Mach-O object did not contain a __TEXT,__text section");
}

/// Target-agnostic raw read of the Mach-O header `cputype` field (offset 4).
///
/// `MachOParser` deliberately rejects any non-ARM64 object at the header
/// (`LinkerError::UnsupportedCpuType`) because its section-relocation decoding
/// is AArch64-specific (`decode_relocation`). For the x86-64 half of this
/// dual-target acceptance test we therefore read the (target-independent)
/// Mach-O structures by hand, exactly as `text_relocations` already does, so we
/// do not misroute an x86-64 object through the ARM64-only relocation decoder.
fn raw_cputype(bytes: &[u8]) -> u32 {
    assert!(
        bytes.len() >= macho_consts::MACH_HEADER_64_SIZE as usize,
        "Mach-O object too small: {} bytes",
        bytes.len()
    );
    assert_eq!(read_u32_le(bytes, 0), macho_consts::MH_MAGIC_64);
    read_u32_le(bytes, 4)
}

/// Target-agnostic raw read of the `__TEXT,__text` section's file bytes. The
/// section table layout is identical across CPU types; only relocation *type
/// values* differ, and those are not consulted here.
fn raw_text_section_data(bytes: &[u8]) -> Vec<u8> {
    assert_eq!(read_u32_le(bytes, 0), macho_consts::MH_MAGIC_64);
    let ncmds = read_u32_le(bytes, 16) as usize;
    let sizeofcmds = read_u32_le(bytes, 20) as usize;
    let mut cmd_offset = macho_consts::MACH_HEADER_64_SIZE as usize;
    let commands_end = cmd_offset + sizeofcmds;

    for _ in 0..ncmds {
        assert!(cmd_offset + 8 <= bytes.len() && cmd_offset + 8 <= commands_end);
        let cmd = read_u32_le(bytes, cmd_offset);
        let cmdsize = read_u32_le(bytes, cmd_offset + 4) as usize;
        assert!(cmdsize >= 8 && cmd_offset + cmdsize <= bytes.len());

        if cmd == macho_consts::LC_SEGMENT_64 {
            let nsects = read_u32_le(bytes, cmd_offset + 64) as usize;
            let mut sec_offset = cmd_offset + macho_consts::SEGMENT_COMMAND_64_SIZE as usize;
            for _ in 0..nsects {
                assert!(sec_offset + macho_consts::SECTION_64_SIZE as usize <= bytes.len());
                let sectname = read_name16(bytes, sec_offset);
                let segname = read_name16(bytes, sec_offset + 16);
                if sectname == "__text" && segname == "__TEXT" {
                    let sec_size = read_u64_le(bytes, sec_offset + 40) as usize;
                    let sec_fileoff = read_u32_le(bytes, sec_offset + 48) as usize;
                    assert!(
                        sec_fileoff + sec_size <= bytes.len(),
                        "__text contents out of bounds"
                    );
                    return bytes[sec_fileoff..sec_fileoff + sec_size].to_vec();
                }
                sec_offset += macho_consts::SECTION_64_SIZE as usize;
            }
        }
        cmd_offset += cmdsize;
    }
    panic!("Mach-O object did not contain a __TEXT,__text section");
}

/// Target-agnostic raw resolution of a symbol-table entry's name by index, via
/// the `LC_SYMTAB` command. The nlist_64 / string-table layout is identical
/// across CPU types.
fn raw_symbol_name(bytes: &[u8], symbol_index: u32) -> Option<String> {
    let ncmds = read_u32_le(bytes, 16) as usize;
    let mut cmd_offset = macho_consts::MACH_HEADER_64_SIZE as usize;
    for _ in 0..ncmds {
        let cmd = read_u32_le(bytes, cmd_offset);
        let cmdsize = read_u32_le(bytes, cmd_offset + 4) as usize;
        if cmd == macho_consts::LC_SYMTAB {
            let symoff = read_u32_le(bytes, cmd_offset + 8) as usize;
            let nsyms = read_u32_le(bytes, cmd_offset + 12) as usize;
            let stroff = read_u32_le(bytes, cmd_offset + 16) as usize;
            if symbol_index as usize >= nsyms {
                return None;
            }
            let nlist_off = symoff + symbol_index as usize * macho_consts::NLIST_64_SIZE as usize;
            assert!(nlist_off + macho_consts::NLIST_64_SIZE as usize <= bytes.len());
            let n_strx = read_u32_le(bytes, nlist_off) as usize;
            let name_off = stroff + n_strx;
            let end = bytes[name_off..]
                .iter()
                .position(|&b| b == 0)
                .map(|p| name_off + p)
                .unwrap_or(bytes.len());
            return Some(String::from_utf8_lossy(&bytes[name_off..end]).into_owned());
        }
        cmd_offset += cmdsize;
    }
    None
}

/// Cross-emit an arm64 Mach-O object on any host. The default target spec is
/// host-OS-aware (ELF on Linux), so Mach-O-shape assertions must request the
/// Darwin spec explicitly, exactly like the x86-64 half does.
fn compile_aarch64_darwin_module(module: &TrustIrModule) -> Vec<u8> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            target: Target::Aarch64,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("aarch64-apple-darwin").expect("parse aarch64-apple-darwin target spec"),
    )
    .compile(module)
    .unwrap_or_else(|err| panic!("aarch64 Darwin caller/callee compile failed: {err:?}"))
    .object_code
}

fn compile_x86_64_macho_module(module: &TrustIrModule) -> Vec<u8> {
    x86_64_darwin_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        target: Target::X86_64,
        ..CompilerConfig::default()
    })
    .compile(module)
    .unwrap_or_else(|err| panic!("x86_64 Darwin caller/callee compile failed: {err:?}"))
    .object_code
}

fn temp_test_dir(name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock before UNIX_EPOCH")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_e2e_x86_64_dispatcher_{}_{}_{}",
        name,
        std::process::id(),
        nanos
    ));
    fs::create_dir_all(&dir).expect("create temporary test directory");
    dir
}

fn link_x86_64(dir: &Path, driver_c: &Path, obj: &Path, output_name: &str) -> PathBuf {
    let binary = dir.join(output_name);
    let output = Command::new("cc")
        .args(if cfg!(target_os = "macos") {
            &["-arch", "x86_64"][..]
        } else {
            &[][..]
        })
        .args([
            "-o",
            binary.to_str().unwrap(),
            driver_c.to_str().unwrap(),
            obj.to_str().unwrap(),
        ])
        .output()
        .expect("run cc to link the x86-64 object");

    if !output.status.success() {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let nm = Command::new("nm")
            .arg(obj)
            .output()
            .map(|out| String::from_utf8_lossy(&out.stdout).into_owned())
            .unwrap_or_default();
        let reloc = Command::new("otool")
            .args(["-r", obj.to_str().unwrap()])
            .output()
            .map(|out| String::from_utf8_lossy(&out.stdout).into_owned())
            .unwrap_or_default();
        panic!(
            "cc link of the x86-64 object failed\nstdout:\n{stdout}\nstderr:\n{stderr}\nnm:\n{nm}\notool -r:\n{reloc}"
        );
    }

    binary
}

fn has_cc_x86_64_runtime() -> bool {
    if cfg!(target_arch = "aarch64") && std::env::var_os("TRUST_CG_RUN_ROSETTA_LINKRUN").is_none() {
        eprintln!(
            "SKIP: Rosetta x86_64 link/run disabled on aarch64 host; \
             set TRUST_CG_RUN_ROSETTA_LINKRUN=1 to opt in"
        );
        return false;
    }

    let dir = temp_test_dir("probe");
    let src = dir.join("probe.c");
    let binary = dir.join("probe");
    fs::write(&src, b"int main(void) { return 0; }\n").expect("write x86 probe source");

    let compiled = Command::new("cc")
        .args(if cfg!(target_os = "macos") {
            &["-arch", "x86_64"][..]
        } else {
            &[][..]
        })
        .args(["-o", binary.to_str().unwrap(), src.to_str().unwrap()])
        .output()
        .map(|out| out.status.success())
        .unwrap_or(false);
    if !compiled {
        let _ = fs::remove_dir_all(&dir);
        return false;
    }

    let runnable = run_executable_with_timeout(&binary, codegen_probe_timeout())
        .map(|result| !result.timed_out && result.output.status.success())
        .unwrap_or(false);
    let _ = fs::remove_dir_all(&dir);
    runnable
}

// ---------------------------------------------------------------------------
// Dispatcher tests
// ---------------------------------------------------------------------------

#[test]
fn dispatcher_x86_64_produces_host_native_object_or_l27_fail_closed() {
    // Sanity: compiling through the legacy Target::X86_64 dispatcher must use
    // the host-native object format. Windows currently accepts the L27
    // fail-closed COFF unwind diagnostic until public framed/non-leaf COFF
    // emission lands; once L27 lands this same test expects parseable COFF.
    let module = build_add_module();

    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        target: Target::X86_64,
        ..CompilerConfig::default()
    });

    let Some(result) = expect_host_x86_64_public_aot_result(compiler.compile(&module)) else {
        return;
    };

    // Metrics sanity: single function, non-empty code.
    assert_eq!(result.metrics.function_count, 1);
    assert!(
        result.metrics.code_size_bytes > 0,
        "x86-64 code size must be non-zero"
    );
    // code_size_bytes for x86 is the raw encoded code length, NOT
    // instruction_count * 4 (variable-length encoding).
    assert_ne!(
        result.metrics.code_size_bytes,
        result.metrics.instruction_count * 4,
        "x86-64 must not assume 4-byte fixed-width encoding; \
         code_size_bytes should come from the encoder"
    );
}

#[test]
fn dispatcher_aarch64_still_produces_arm64_host_native_object() {
    // Regression guard: the x86 dispatch must not break the AArch64 default.
    // The default target spec is HOST-OS-aware for AArch64 too (the pipeline
    // keys section/object emission on `target_triple_uses_elf`): Linux/BSD
    // hosts emit an aarch64 ELF relocatable, macOS emits an arm64 Mach-O.
    // Asserting Mach-O magic unconditionally was macOS-assumption test debt
    // (2026-07-31 x86-Linux battery).
    let module = build_add_module();

    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        target: Target::Aarch64,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile(&module)
        .expect("default AArch64 dispatcher should keep working");

    let obj = &result.object_code;
    match std::env::consts::OS {
        "linux" | "android" | "freebsd" | "netbsd" | "openbsd" | "dragonfly" => {
            assert_eq!(
                &obj[0..4],
                b"\x7FELF",
                "AArch64 dispatch on an ELF host must emit an ELF object"
            );
            assert_eq!(obj[4], 2, "AArch64 ELF class should be 64-bit");
            assert_eq!(
                read_u16_le(obj, 16),
                1,
                "AArch64 ELF file type should be ET_REL"
            );
            assert_eq!(
                read_u16_le(obj, 18),
                183,
                "AArch64 dispatch must emit e_machine EM_AARCH64"
            );
        }
        "macos" => {
            let magic = read_u32_le(obj, 0);
            assert_eq!(magic, MH_MAGIC_64);
            let cpu_type = read_u32_le(obj, 4);
            assert_eq!(
                cpu_type, CPU_TYPE_ARM64,
                "AArch64 dispatch must still emit CPU_TYPE_ARM64"
            );
        }
        other => panic!("no host-native AArch64 object-format expectation wired for OS {other}"),
    }
}

#[test]
fn dispatcher_x86_64_differs_from_aarch64() {
    // The core behavioral pin: same trust_ir input + different targets must
    // produce different object bytes. BOTH sides request Darwin explicitly
    // because this test compares Mach-O CPU types (the default spec emits
    // host-native ELF on Linux, where offset 4 is not a cputype field); the
    // host-native object-format expectations are covered above.
    let module = build_add_module();

    let x86_result = x86_64_darwin_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        target: Target::X86_64,
        ..CompilerConfig::default()
    })
    .compile(&module)
    .expect("x86_64 dispatch");

    let aarch64_obj = compile_aarch64_darwin_module(&module);

    assert_ne!(
        x86_result.object_code, aarch64_obj,
        "x86_64 and aarch64 object code must differ for the same trust_ir input"
    );
    // At minimum, the CPU type in the Mach-O header must differ.
    let x86_cpu = read_u32_le(&x86_result.object_code, 4);
    let arm_cpu = read_u32_le(&aarch64_obj, 4);
    assert_ne!(x86_cpu, arm_cpu, "CPU types must differ across targets");
}

#[test]
fn dispatcher_x86_64_multi_function_module_compiles() {
    // #464: multi-function x86-64 modules must compile end-to-end through
    // `X86Pipeline::compile_module`. Prior to #464 the dispatcher rejected
    // any module with more than one function. This test requests Darwin
    // explicitly so it can keep checking the Mach-O object contract while the
    // default Target::X86_64 path remains host-native.
    let mut module = build_add_module();

    // Add a second function (sub) reusing the same FuncTyId(0) since it
    // has identical signature (i64, i64) -> i64.
    let mut sub_func =
        TrustIrFunction::new(FuncId::new(1), "sub", FuncTyId::new(0), BlockId::new(0));
    sub_func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(sub_func);

    let compiler = x86_64_darwin_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        target: Target::X86_64,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile(&module)
        .expect("x86-64 dispatcher must compile multi-function modules (#464)");

    assert_x86_64_macho_object(&result.object_code, "multi-function x86-64 Darwin");

    // Metrics must reflect both functions, not just the first.
    assert_eq!(
        result.metrics.function_count, 2,
        "multi-function module must report function_count = 2"
    );
    assert!(
        result.metrics.code_size_bytes > 0,
        "multi-function module must have non-zero code size"
    );
    assert!(
        result.metrics.instruction_count > 0,
        "multi-function module must sum instruction counts across all functions"
    );

    // Both mangled symbol names must appear in the object's symbol table.
    // Mach-O writes symbols uncompressed into the string table, so a raw
    // byte-substring search is sufficient here (this mirrors how the
    // AArch64 multi-function tests verify symbol-table contents without
    // depending on a full Mach-O parser).
    let obj = &result.object_code;
    let has_add = obj.windows(4).any(|w| w == b"_add");
    let has_sub = obj.windows(4).any(|w| w == b"_sub");
    assert!(
        has_add && has_sub,
        "multi-function Mach-O must contain both `_add` and `_sub` symbol names \
         (has_add={}, has_sub={})",
        has_add,
        has_sub
    );
}

#[test]
fn dispatcher_x86_64_emit_proofs_returns_populated_certs() {
    // #465: the x86-64 dispatcher now wires proof certificates through the
    // public Compiler API (mirror of the AArch64 path). A trivial `add`
    // function must produce `Some(certs)` with `certs.len() > 0`.
    //
    // Historical: prior to #465 this test pinned the inverse behavior —
    // `CompileError::ProofsUnsupportedForTarget` — because the x86-64
    // MachFunction verifier did not yet exist. #465 wires
    // `trust_cg_verify::x86_64_function_verifier` through
    // `compile_x86_64`, replacing the typed-error early-return with real
    // proof generation. The verified-codegen invariant
    // (`result.proofs.is_some()` when `emit_proofs=true`) is now preserved
    // by successful generation, not by erroring out.
    //
    // Runs on a thread with enlarged stack because the verifier's
    // recursive SMT evaluation can overflow the default 8 MiB test
    // thread stack in debug builds (same pattern as
    // `test_compile_module_to_jit_with_proofs` for AArch64).
    let child = std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let module = build_add_module();

            let compiler = x86_64_darwin_compiler(CompilerConfig {
                opt_level: OptLevel::O0,
                target: Target::X86_64,
                emit_proofs: true,
                ..CompilerConfig::default()
            });

            let result = compiler
                .compile(&module)
                .expect("x86-64 + emit_proofs=true must now succeed (#465)");

            let certs = result
                .proofs
                .as_ref()
                .expect("proofs must be Some when emit_proofs=true on x86-64 (#465)");
            assert!(
                !certs.is_empty(),
                "x86-64 add module must produce >=1 proof certificate; got 0"
            );

            // The trivial `add` lowers through an x86-64 ADD instruction;
            // at least one cert must come from the x86-64 lowering proof
            // registry. The registry emits two name families: the static
            // control-flow lowering proofs (`x86_64: CALL ...`, in
            // `x86_64_lowering_proofs.rs`) and the per-instruction reconstructed
            // real-operand proofs (`RECONSTRUCTED x86_64 <Op> -> <Mach> ...`, in
            // `x86_64_function_verifier.rs`). A trivial `add` exercises ONLY the
            // reconstructed family (`RECONSTRUCTED x86_64 Iadd_64 -> AddRR
            // (real-operand)`) — it never hits CALL/RET/JMP, so the
            // `"x86_64:"`-only check was too narrow and matched none of the
            // genuinely x86-64-provenanced certs. Both prefixes denote the
            // x86-64 lowering registry; accept either. (Soundness is still
            // pinned by the `Some(proofs)` and non-empty checks above; this only
            // corrects the provenance string match.)
            let has_x86_cert = certs.iter().any(|c| {
                c.rule_name.starts_with("x86_64:")
                    || c.rule_name.starts_with("RECONSTRUCTED x86_64 ")
            });
            assert!(
                has_x86_cert,
                "expected at least one cert from the x86-64 lowering proof registry; \
                 got rule names: {:?}",
                certs
                    .iter()
                    .map(|c| c.rule_name.as_str())
                    .collect::<Vec<_>>()
            );
        })
        .expect("failed to spawn thread with larger stack");
    child.join().expect("test thread panicked");
}

#[test]
fn dispatcher_x86_64_emit_proofs_errors_variant_deprecated_for_x86() {
    // Documentation test pinning the #465 behavior change: the
    // `CompileError::ProofsUnsupportedForTarget` variant is still defined
    // (it fires for `Target::Riscv64`), but under the default `verify`
    // feature the x86-64 dispatcher must never return it. This guards
    // against a silent revert of #465 that leaves the variant reachable
    // for x86-64 without anyone noticing.
    //
    // Same stack-size dance as the populated-certs test above — the
    // verifier is recursive and debug builds overflow the default 8 MiB.
    let child = std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let module = build_add_module();

            let compiler = x86_64_darwin_compiler(CompilerConfig {
                opt_level: OptLevel::O0,
                target: Target::X86_64,
                emit_proofs: true,
                ..CompilerConfig::default()
            });

            match compiler.compile(&module) {
                Ok(_) => { /* expected */ }
                Err(CompileError::ProofsUnsupportedForTarget { target }) => panic!(
                    "#465 regression: x86-64 + emit_proofs=true should no longer \
                     return ProofsUnsupportedForTarget (got target={:?})",
                    target
                ),
                Err(other) => panic!("unexpected compile error: {other:?}"),
            }
        })
        .expect("failed to spawn thread with larger stack");
    child.join().expect("test thread panicked");
}

#[test]
fn dispatcher_x86_64_emit_proofs_false_still_compiles_cleanly() {
    // Negative control for the regression pin above: when the caller
    // explicitly leaves `emit_proofs=false` (the default), x86-64 dispatch
    // must still succeed. The error in
    // `dispatcher_x86_64_emit_proofs_errors_instead_of_silently_dropping`
    // is conditional on `emit_proofs=true`; the rest of the x86-64 path
    // must not regress.
    let module = build_add_module();

    let compiler = x86_64_darwin_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        target: Target::X86_64,
        emit_proofs: false,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile(&module)
        .expect("x86-64 dispatch with emit_proofs=false must still succeed");

    assert!(
        result.proofs.is_none(),
        "proofs must be None when emit_proofs=false"
    );
    assert_eq!(result.metrics.function_count, 1);
    assert!(result.metrics.code_size_bytes > 0);
}

#[test]
fn dispatcher_x86_64_cross_function_call_compiles() {
    // #464: a trust_ir module whose caller invokes a callee in the same module
    // must compile cleanly through the x86-64 dispatcher. The call site
    // becomes an `E8 dd dd dd dd` CALL rel32 whose 4-byte displacement is
    // patched by an `X86_64_RELOC_BRANCH` relocation in the explicit Darwin
    // Mach-O object. At MVP the placeholder displacement is zero; this test
    // verifies the object emits without error and carries both function
    // symbols.
    //
    // We intentionally leave detailed relocation decoding to the focused
    // dual-target test below. This test pins
    // the end-to-end dispatcher wiring: multi-function module + intra-
    // module CALL survives the full ISel -> encode -> Mach-O pipeline.
    let module = build_caller_callee_const_module();

    let compiler = x86_64_darwin_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        target: Target::X86_64,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile(&module)
        .expect("x86-64 dispatcher must compile caller + callee in one module (#464)");

    assert_x86_64_macho_object(&result.object_code, "caller/callee x86-64 Darwin");

    // Both functions must be in the symbol table.
    let obj = &result.object_code;
    let has_callee = obj.windows(7).any(|w| w == b"_callee");
    let has_caller = obj.windows(7).any(|w| w == b"_caller");
    assert!(
        has_callee && has_caller,
        "Mach-O must expose both `_callee` and `_caller` global symbols \
         (has_callee={}, has_caller={})",
        has_callee,
        has_caller
    );

    // Metrics.
    assert_eq!(result.metrics.function_count, 2);
    assert!(result.metrics.code_size_bytes > 0);
    // A call site encodes to 5 bytes (E8 dd dd dd dd) + return + prologue,
    // so the combined module must be larger than either function alone.
    assert!(
        result.metrics.code_size_bytes >= 10,
        "caller + callee should produce at least 10 bytes of code (got {})",
        result.metrics.code_size_bytes
    );
}

#[test]
fn dispatcher_x86_64_cross_function_call_links_and_runs() {
    // #464 written acceptance: the exact 2-function caller/callee module must
    // compile to one x86-64 object, link with a C driver, and run correctly.
    // On Apple Silicon this runs through Rosetta 2 via `cc -arch x86_64`; on a
    // native x86-64 ELF host (Linux) the HOST-NATIVE object links with plain
    // `cc` and executes directly — real-hardware coverage, not emulation.
    if !has_cc_x86_64_runtime() {
        eprintln!(
            "Skipping dispatcher_x86_64_cross_function_call_links_and_runs: \
             requires cc plus runnable x86-64 binaries"
        );
        return;
    }

    let module = build_caller_callee_const_module();
    // The object format must match what the HOST linker consumes: Mach-O on
    // macOS, host-native (ELF) elsewhere. Cross-emitting Mach-O on Linux and
    // handing it to GNU ld was macOS-assumption test debt ("file format not
    // recognized", 2026-07-31 x86-Linux battery).
    let obj = if cfg!(target_os = "macos") {
        compile_x86_64_macho_module(&module)
    } else {
        Compiler::new(CompilerConfig {
            opt_level: OptLevel::O0,
            target: Target::X86_64,
            ..CompilerConfig::default()
        })
        .compile(&module)
        .expect("host-native x86_64 caller/callee compile")
        .object_code
    };

    let dir = temp_test_dir("caller_callee_linkrun");
    let obj_path = dir.join("caller_callee.o");
    let driver_path = dir.join("driver.c");
    fs::write(&obj_path, &obj).expect("write x86-64 caller/callee object");
    fs::write(
        &driver_path,
        br#"
#include <stdio.h>

extern long caller(void);

int main(void) {
    long value = caller();
    printf("%ld\n", value);
    return value == 42 ? 0 : 1;
}
"#,
    )
    .expect("write C driver");

    let binary = link_x86_64(&dir, &driver_path, &obj_path, "caller_callee");
    let run = run_executable_with_timeout(&binary, codegen_run_timeout())
        .expect("run linked x86-64 caller/callee binary");
    let stdout = String::from_utf8_lossy(&run.output.stdout);
    let stderr = String::from_utf8_lossy(&run.output.stderr);
    let _ = fs::remove_dir_all(&dir);

    assert!(
        !run.timed_out,
        "caller/callee x86-64 binary timed out; stdout={stdout:?}, stderr={stderr:?}"
    );
    assert!(
        run.output.status.success(),
        "caller/callee x86-64 binary should exit 0; stdout={stdout:?}, stderr={stderr:?}"
    );
    assert_eq!(stdout.trim(), "42");
}

#[test]
fn dispatcher_dual_target_cross_function_call_relocations() {
    // #464 written acceptance: the same 2-function trust_ir must produce valid
    // AArch64 and x86-64 objects with an inter-function call relocation from
    // caller to callee.
    let module = build_caller_callee_const_module();
    // Both halves request the Darwin spec explicitly: this test's assertions
    // are Mach-O relocation shapes (`ARM64_RELOC_BRANCH26` / `X86_64_RELOC_BRANCH`),
    // and the default spec emits host-native ELF on Linux hosts. ELF call
    // relocations are covered by the ELF reparse gate and the link/run test.
    let aarch64_obj = compile_aarch64_darwin_module(&module);
    let x86_obj = compile_x86_64_macho_module(&module);

    let aarch64 = MachOParser::parse(&aarch64_obj).expect("parse AArch64 Mach-O");
    assert_eq!(aarch64.cputype, CPU_TYPE_ARM64);
    let aarch64_text = aarch64
        .sections
        .iter()
        .find(|section| section.segment == "__TEXT" && section.name == "__text")
        .expect("AArch64 object should contain __TEXT,__text");
    let aarch64_relocs = text_relocations(&aarch64_obj);
    let aarch64_branch = aarch64_relocs
        .iter()
        .find(|reloc| {
            reloc.type_val as u32 == macho_consts::ARM64_RELOC_BRANCH26
                && reloc.pc_relative
                && reloc.length == macho_consts::RELOC_LENGTH_LONG as u8
                && reloc.is_extern
                && aarch64
                    .symbols
                    .get(reloc.symbol_index as usize)
                    .is_some_and(|sym| sym.name == "_callee")
        })
        .unwrap_or_else(|| {
            panic!(
                "AArch64 object should have ARM64_RELOC_BRANCH26 to _callee; relocs={:?}, symbols={:?}",
                aarch64_relocs,
                aarch64
                    .symbols
                    .iter()
                    .map(|sym| sym.name.as_str())
                    .collect::<Vec<_>>()
            )
        });
    let branch_offset = aarch64_branch.offset as usize;
    assert!(
        branch_offset + 4 <= aarch64_text.data.len(),
        "AArch64 branch relocation offset out of __text bounds"
    );
    let branch_word = u32::from_le_bytes(
        aarch64_text.data[branch_offset..branch_offset + 4]
            .try_into()
            .expect("read AArch64 branch instruction"),
    );
    assert_eq!(
        branch_word & 0xFC00_0000,
        0x9400_0000,
        "AArch64 call relocation should point at a BL instruction"
    );

    // The x86-64 object is parsed with the target-agnostic raw Mach-O readers,
    // NOT `MachOParser`: that parser is AArch64-only by design (its
    // `decode_relocation` interprets relocation type values as ARM64 ones and
    // its header gate fail-closes on any other `cputype`). Reading the header
    // `cputype`, the `__TEXT,__text` bytes, and a symbol-table name by index is
    // CPU-type-independent, so these raw helpers give us the same structural
    // checks for the x86-64 half of this dual-target acceptance without
    // misrouting the object through the ARM64 relocation decoder. The
    // relocation type-value semantics that DO differ are handled by
    // `text_relocations` (a raw walker) just as on the AArch64 side above.
    let x86_cputype = raw_cputype(&x86_obj);
    assert_eq!(x86_cputype, CPU_TYPE_X86_64);
    let x86_text_data = raw_text_section_data(&x86_obj);
    let x86_relocs = text_relocations(&x86_obj);
    let x86_branch = x86_relocs
        .iter()
        .find(|reloc| {
            reloc.type_val as u32 == macho_consts::X86_64_RELOC_BRANCH
                && reloc.pc_relative
                && reloc.length == macho_consts::RELOC_LENGTH_LONG as u8
                && reloc.is_extern
                && raw_symbol_name(&x86_obj, reloc.symbol_index)
                    .as_deref()
                    == Some("_callee")
        })
        .unwrap_or_else(|| {
            panic!(
                "x86-64 object should have X86_64_RELOC_BRANCH to _callee; relocs={:?}, symbols={:?}",
                x86_relocs,
                x86_relocs
                    .iter()
                    .map(|reloc| raw_symbol_name(&x86_obj, reloc.symbol_index))
                    .collect::<Vec<_>>()
            )
        });
    let disp_offset = x86_branch.offset as usize;
    assert!(
        disp_offset > 0 && disp_offset + 4 <= x86_text_data.len(),
        "x86-64 CALL relocation displacement offset out of __text bounds"
    );
    assert_eq!(
        x86_text_data[disp_offset - 1],
        0xE8,
        "x86-64 branch relocation should target a CALL rel32 displacement"
    );
}
