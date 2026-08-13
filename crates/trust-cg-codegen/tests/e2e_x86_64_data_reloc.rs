// trust-cg-codegen/tests/e2e_x86_64_data_reloc.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// On-host AOT differential oracle for x86-64 DATA-SECTION RELOCATIONS: placing
// the run-time ADDRESS of a named symbol (function or data global) *inside a
// global-variable initializer*, which the linker fills in. This is the keystone
// that unblocks vtables (trait objects / `dyn`) and `static FNS: [fn(); N]`.
//
// Before this work, a global's initializer could only be raw bytes
// (`Constant::Aggregate` of `Constant::Int`). The new `Constant::SymbolAddr {
// symbol, addend }` element reserves one native pointer (8 bytes) in the
// global's data and records a data relocation:
//   - Mach-O: `X86_64_RELOC_UNSIGNED` (8-byte absolute pointer) at the slot,
//     referencing the symbol (defined-in-module or external).
//   - ELF: `R_X86_64_64` in `.rela.data` / `.rela.rodata` (shape-only on this
//     host; macOS links/runs the Mach-O path, which is what we verify here).
//
// Emitting a data relocation is OBJECT-ENCODING, not an ISel lowering rule, so
// there is no new SMT proof — correctness is established by LINK + RUN against
// clang. The trust_ir interpreter does not model symbol addresses, so this test
// is DIFFERENTIAL-ONLY (trust-cg vs clang). Host: x86-64 macOS.
//
// Coverage:
//   1. A global = a table of FUNCTION addresses [&fa, &fb, &fc] (a mini vtable);
//      a function loads slot `i` and CALLS through it (indirect call).
//   2. A global = a pointer to ANOTHER data global (`static long *p = &g;`); a
//      function loads the data pointer and dereferences it.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::elf::reloc::Elf64Rela;
use trust_cg_codegen::pipeline::{GlobalSymbolRef, ObjectGlobal, OptLevel};
use trust_cg_codegen::x86_64::{
    X86OutputFormat, X86Pipeline, X86PipelineConfig, build_x86_const_test_function,
};

use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction,
    Global, Inst, InstrNode, Linkage, Module as TrustIrModule, Ty, ValueId,
};

// =============================================================================
// Host gating + harness (mirrors e2e_x86_64_symbol_address.rs)
// =============================================================================

fn x86_64_oracle_enabled() -> bool {
    if !cfg!(target_arch = "x86_64") {
        eprintln!("SKIP: x86-64 data-reloc oracle requires an x86-64 host");
        return false;
    }
    if !has_cc() {
        eprintln!("SKIP: cc not available");
        return false;
    }
    true
}

fn has_cc() -> bool {
    Command::new("cc")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn make_test_dir(test_name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("trust_cg_x86_64_datareloc_{}", test_name));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    dir
}

fn cleanup(dir: &Path) {
    let _ = fs::remove_dir_all(dir);
}

fn compile_trust_ir_module_x86_64(module: &TrustIrModule) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        target: Target::X86_64,
        emit_proofs: false,
        trace_level: CompilerTraceLevel::None,
        emit_debug: false,
        parallel: false,
        cegis_superopt_budget_sec: None,
        enable_fsym_trust_ir_preflight: false,
        enable_jit_fast_regalloc: false,
        jit_validation_mode_override: None,
        panic_unwind: false,
    });
    let result = compiler
        .compile(module)
        .expect("x86-64 trust-cg compilation should succeed");
    assert!(
        !result.object_code.is_empty(),
        "trust-cg must produce non-empty object code"
    );
    result.object_code
}

/// Differential harness: link the trust-cg object (which DEFINES the entry
/// functions and the relocated globals) against the driver compiled in
/// `EXTERN_ONLY` mode; compare to the same driver compiled standalone by clang.
fn differential_test(
    test_name: &str,
    module: &TrustIrModule,
    c_source: &str,
) -> Result<(), String> {
    let dir = make_test_dir(test_name);

    let obj_bytes = compile_trust_ir_module_x86_64(module);
    let obj_path = dir.join("trust_cg.o");
    fs::write(&obj_path, &obj_bytes).map_err(|e| format!("write .o: {}", e))?;

    let driver_path = dir.join("driver.c");
    fs::write(&driver_path, c_source).map_err(|e| format!("write driver.c: {}", e))?;

    // trust-cg path: the driver declares the entry functions extern and links
    // against the trust-cg object that defines them + the relocated globals.
    let trust_cg_bin = dir.join("test_trust_cg");
    let trust_cg_link = Command::new("cc")
        .args(if cfg!(target_os = "macos") {
            &["-arch", "x86_64"][..]
        } else {
            &[][..]
        })
        .args([
            "-DEXTERN_ONLY",
            "-O0",
            "-o",
            trust_cg_bin.to_str().unwrap(),
            driver_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
        ])
        .output()
        .map_err(|e| format!("trust-cg link: {}", e))?;
    if !trust_cg_link.status.success() {
        let stderr = String::from_utf8_lossy(&trust_cg_link.stderr);
        let nm = Command::new("nm")
            .arg(obj_path.to_str().unwrap())
            .output()
            .ok();
        let nm_out = nm
            .map(|o| String::from_utf8_lossy(&o.stdout).to_string())
            .unwrap_or_default();
        let otool = Command::new("otool")
            .args(["-rv", obj_path.to_str().unwrap()])
            .output()
            .ok();
        let otool_out = otool
            .map(|o| String::from_utf8_lossy(&o.stdout).to_string())
            .unwrap_or_default();
        cleanup(&dir);
        return Err(format!(
            "trust-cg link failed: {}\nnm:\n{}\notool -rv:\n{}",
            stderr, nm_out, otool_out
        ));
    }

    let trust_cg_run = Command::new(&trust_cg_bin)
        .output()
        .map_err(|e| format!("run trust-cg binary: {}", e))?;
    let trust_cg_stdout = String::from_utf8_lossy(&trust_cg_run.stdout).to_string();
    let trust_cg_exit = trust_cg_run.status.code().unwrap_or(-1);

    // clang reference: same driver compiled standalone (clang provides its own
    // definitions of the entry functions / globals).
    let clang_bin = dir.join("test_clang");
    let clang_compile = Command::new("cc")
        .args(if cfg!(target_os = "macos") {
            &["-arch", "x86_64"][..]
        } else {
            &[][..]
        })
        .args([
            "-O0",
            "-o",
            clang_bin.to_str().unwrap(),
            driver_path.to_str().unwrap(),
        ])
        .output()
        .map_err(|e| format!("clang compile: {}", e))?;
    if !clang_compile.status.success() {
        let stderr = String::from_utf8_lossy(&clang_compile.stderr);
        cleanup(&dir);
        return Err(format!("clang reference compile failed: {}", stderr));
    }

    let clang_run = Command::new(&clang_bin)
        .output()
        .map_err(|e| format!("run clang binary: {}", e))?;
    let clang_stdout = String::from_utf8_lossy(&clang_run.stdout).to_string();
    let clang_exit = clang_run.status.code().unwrap_or(-1);

    eprintln!("=== x86-64 data-reloc differential: {} ===", test_name);
    eprintln!("  trust-cg stdout: {}", trust_cg_stdout.trim());
    eprintln!("  clang    stdout: {}", clang_stdout.trim());
    eprintln!(
        "  trust-cg exit={}  clang exit={}",
        trust_cg_exit, clang_exit
    );

    if trust_cg_stdout != clang_stdout {
        let otool = Command::new("otool")
            .args(["-tvr", obj_path.to_str().unwrap()])
            .output()
            .ok();
        let disasm = otool
            .map(|o| String::from_utf8_lossy(&o.stdout).to_string())
            .unwrap_or_default();
        cleanup(&dir);
        return Err(format!(
            "OUTPUT MISMATCH!\n  trust-cg: {}\n  clang:    {}\n  trust-cg disasm:\n{}",
            trust_cg_stdout.trim(),
            clang_stdout.trim(),
            disasm
        ));
    }
    if trust_cg_exit != clang_exit {
        cleanup(&dir);
        return Err(format!(
            "EXIT MISMATCH! trust-cg={} clang={}",
            trust_cg_exit, clang_exit
        ));
    }
    if clang_exit != 0 {
        cleanup(&dir);
        return Err(format!("both binaries exited non-zero ({})", clang_exit));
    }

    cleanup(&dir);
    Ok(())
}

/// Magic global-address stub recognized by the lower adapter:
///   bits[63:48] = 0xFADE, bits[47:32] = global index, bits[31:0] = byte offset.
/// With offset 0 it lowers to `Opcode::GlobalRef { name }` — the I64-typed
/// run-time address of `module.globals[index]`.
fn global_addr_stub(global_index: u64) -> i128 {
    ((0xFADE_u64 << 48) | ((global_index & 0xFFFF) << 32)) as i128
}

// =============================================================================
// trust_ir builders
// =============================================================================

/// Build a mini-vtable module:
///   static long (*VTBL[3])(long) = { fa, fb, fc };
///   long call_slot(long i, long x) { return VTBL[i](x); }
/// where fa(x)=x+100, fb(x)=x*3, fc(x)=-x. The VTBL global's initializer holds
/// three FUNCTION addresses as `Constant::SymbolAddr` elements — each emits an
/// X86_64_RELOC_UNSIGNED data relocation the linker fills in.
fn build_vtable_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("vtable_reloc");
    let unary_ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let call_ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    // fa(x) = x + 100
    let mut fa = TrustIrFunction::new(FuncId::new(0), "fa", unary_ft, BlockId::new(0));
    fa.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(100),
            })
            .with_result(ValueId::new(1)),
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
    module.add_function(fa);

    // fb(x) = x * 3
    let mut fb = TrustIrFunction::new(FuncId::new(1), "fb", unary_ft, BlockId::new(0));
    fb.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(3),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
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
    module.add_function(fb);

    // fc(x) = 0 - x
    let mut fc = TrustIrFunction::new(FuncId::new(2), "fc", unary_ft, BlockId::new(0));
    fc.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I64,
                lhs: ValueId::new(1),
                rhs: ValueId::new(0),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(fc);

    // The vtable: a table of three function addresses. Each slot is a
    // pointer-sized relocatable element. Global index 0 (referenced by the
    // FADE stub below).
    module.globals.push(Global {
        name: "VTBL".to_string(),
        ty: Ty::Ptr,
        mutable: false,
        initializer: Some(Constant::Aggregate(vec![
            Constant::symbol_addr("fa"),
            Constant::symbol_addr("fb"),
            Constant::symbol_addr("fc"),
        ])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });

    // call_slot(i, x) = VTBL[i](x)
    //   base = &VTBL
    //   off  = i * 8
    //   slot = base + off
    //   fp   = *slot
    //   r    = fp(x)
    let mut entry = TrustIrFunction::new(FuncId::new(3), "call_slot", call_ft, BlockId::new(0));
    entry.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            // base = &VTBL  (GlobalRef via FADE stub, global index 0)
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(global_addr_stub(0)),
            })
            .with_result(ValueId::new(2)),
            // eight = 8
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(8),
            })
            .with_result(ValueId::new(3)),
            // off = i * 8
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
            // slot = base + off
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(2),
                rhs: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
            // fp = *slot  (load the function pointer from the vtable slot)
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(5),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(6)),
            // r = fp(x)  (indirect call through the loaded function pointer)
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(6),
                sig: unary_ft,
                args: vec![ValueId::new(1)],
                calling_conv: trust_ir::CallingConv::C,
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(7)],
            }),
        ],
    }];
    module.add_function(entry);
    module
}

/// Build a data-pointer module:
///   static long G = 0x1234;
///   static long *PG = &G;
///   long deref_pg(void) { return *PG; }
/// `PG`'s initializer is a single `Constant::SymbolAddr("G")` — a data-global
/// pointer the linker fills in via X86_64_RELOC_UNSIGNED. `deref_pg` loads the
/// pointer (`*PG` yields the address of G) then dereferences it again.
fn build_data_pointer_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("data_ptr_reloc");

    // G = 0x1234 = 4660 (little-endian i64).
    // global index 0
    module.globals.push(Global {
        name: "G".to_string(),
        ty: Ty::I64,
        mutable: false,
        initializer: Some(Constant::Aggregate(vec![
            Constant::Int(0x34),
            Constant::Int(0x12),
            Constant::Int(0),
            Constant::Int(0),
            Constant::Int(0),
            Constant::Int(0),
            Constant::Int(0),
            Constant::Int(0),
        ])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });

    // PG = &G  (a single relocatable pointer element)
    // global index 1
    module.globals.push(Global {
        name: "PG".to_string(),
        ty: Ty::Ptr,
        mutable: false,
        initializer: Some(Constant::Aggregate(vec![Constant::symbol_addr("G")])),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    });

    let ret_ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    // deref_pg() = **(&PG)
    //   ppg = &PG       (GlobalRef to PG, global index 1)
    //   pg  = *ppg      (loads the relocated pointer = &G)
    //   v   = *pg       (loads G's value)
    let mut entry = TrustIrFunction::new(FuncId::new(0), "deref_pg", ret_ft, BlockId::new(0));
    entry.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            // ppg = &PG  (global index 1)
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(global_addr_stub(1)),
            })
            .with_result(ValueId::new(0)),
            // pg = *ppg  (the relocated &G)
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(1)),
            // v = *pg
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(1),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(entry);
    module
}

// =============================================================================
// Tests
// =============================================================================

#[test]
fn test_x86_64_vtable_of_function_addresses_indirect_call() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_vtable_module();
    // The C reference: a static table of function pointers (a mini vtable),
    // indexed and called through.
    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
static long fa(long x) { return x + 100; }
static long fb(long x) { return x * 3; }
static long fc(long x) { return 0 - x; }
static long (*VTBL[3])(long) = { fa, fb, fc };
long call_slot(long i, long x) {
    return VTBL[i](x);
}
#endif
#ifdef EXTERN_ONLY
extern long call_slot(long i, long x);
#endif

int main(void) {
    printf("s0(5)=%ld\n", call_slot(0, 5));
    printf("s1(5)=%ld\n", call_slot(1, 5));
    printf("s2(5)=%ld\n", call_slot(2, 5));
    printf("s0(-7)=%ld\n", call_slot(0, -7));
    printf("s1(-7)=%ld\n", call_slot(1, -7));
    printf("s2(-7)=%ld\n", call_slot(2, -7));
    return 0;
}
"#;
    let r = differential_test("vtable_fnptrs", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_data_global_pointer_in_initializer() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_data_pointer_module();
    // The C reference: a static pointer initialized to the address of another
    // static data global, dereferenced at run time.
    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
static long G = 0x1234;
static long *PG = &G;
long deref_pg(void) {
    return *PG;
}
#endif
#ifdef EXTERN_ONLY
extern long deref_pg(void);
#endif

int main(void) {
    printf("pg=%ld\n", deref_pg());
    return 0;
}
"#;
    let r = differential_test("data_pointer", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

// =============================================================================
// ELF shape verification (host-independent; ELF cannot link/run on macOS)
// =============================================================================
//
// The ELF data-relocation path mirrors the Mach-O path that the on-host oracle
// verifies at run time. Since ELF can't be linked/run here, we verify its
// STRUCTURE: a global with `symbol_refs` produces an `R_X86_64_64` (absolute
// 64-bit) relocation in `.rela.data` / `.rela.rodata`, with the recorded
// addend carried in the RELA's r_addend (ELF's explicit addend).

const ELF64_SHDR_SIZE: usize = 64;
const ELF64_RELA_SIZE: usize = 24;
const SHT_RELA: u32 = 4;
const R_X86_64_64: u32 = 1;

fn read_u16(bytes: &[u8], off: usize) -> u16 {
    u16::from_le_bytes([bytes[off], bytes[off + 1]])
}
fn read_u32(bytes: &[u8], off: usize) -> u32 {
    u32::from_le_bytes([bytes[off], bytes[off + 1], bytes[off + 2], bytes[off + 3]])
}
fn read_u64(bytes: &[u8], off: usize) -> u64 {
    let mut a = [0u8; 8];
    a.copy_from_slice(&bytes[off..off + 8]);
    u64::from_le_bytes(a)
}

/// Section header name for the section at index `i`.
fn elf_section_name(bytes: &[u8], i: usize) -> String {
    let sh_offset = read_u64(bytes, 40) as usize;
    let e_shstrndx = read_u16(bytes, 62) as usize;
    let shstrtab_shdr = sh_offset + e_shstrndx * ELF64_SHDR_SIZE;
    let shstrtab_offset = read_u64(bytes, shstrtab_shdr + 24) as usize;
    let shdr_off = sh_offset + i * ELF64_SHDR_SIZE;
    let sh_name = read_u32(bytes, shdr_off) as usize;
    let name_start = shstrtab_offset + sh_name;
    let name_end = bytes[name_start..]
        .iter()
        .position(|&b| b == 0)
        .map(|p| name_start + p)
        .unwrap_or(name_start);
    std::str::from_utf8(&bytes[name_start..name_end])
        .unwrap_or("")
        .to_string()
}

/// Collect every RELA entry from sections named `.rela.data` / `.rela.rodata`.
fn elf_data_relocations(bytes: &[u8]) -> Vec<(String, Elf64Rela)> {
    let sh_offset = read_u64(bytes, 40) as usize;
    let e_shnum = read_u16(bytes, 60) as usize;
    let mut out = Vec::new();
    for i in 0..e_shnum {
        let shdr_off = sh_offset + i * ELF64_SHDR_SIZE;
        let sh_type = read_u32(bytes, shdr_off + 4);
        if sh_type != SHT_RELA {
            continue;
        }
        let name = elf_section_name(bytes, i);
        if name != ".rela.data" && name != ".rela.rodata" {
            continue;
        }
        let off = read_u64(bytes, shdr_off + 24) as usize;
        let size = read_u64(bytes, shdr_off + 32) as usize;
        let count = size / ELF64_RELA_SIZE;
        for j in 0..count {
            let mut entry = [0u8; ELF64_RELA_SIZE];
            entry.copy_from_slice(
                &bytes[off + j * ELF64_RELA_SIZE..off + (j + 1) * ELF64_RELA_SIZE],
            );
            out.push((name.clone(), Elf64Rela::decode(&entry)));
        }
    }
    out
}

#[test]
fn test_x86_64_elf_data_relocations_shape() {
    // Build a vtable-like global with three function-address slots plus a
    // data-pointer slot carrying a non-zero addend, alongside a trivial
    // function, and emit an ELF object. The ELF path can't link/run on macOS,
    // so this asserts the STRUCTURE: four `R_X86_64_64` relocations land in a
    // `.rela.data` / `.rela.rodata`, at the right offsets, with the addend in
    // r_addend.
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        output_format: X86OutputFormat::Elf,
        emit_elf: true,
        ..X86PipelineConfig::default()
    });

    let vtable = ObjectGlobal {
        name: "VTBL".to_string(),
        // 4 pointer slots: fa, fb, fc, then &G + 16.
        data: vec![0u8; 32],
        mutable: false,
        is_external: true,
        symbol_refs: vec![
            GlobalSymbolRef {
                offset: 0,
                symbol: "fa".to_string(),
                addend: 0,
            },
            GlobalSymbolRef {
                offset: 8,
                symbol: "fb".to_string(),
                addend: 0,
            },
            GlobalSymbolRef {
                offset: 16,
                symbol: "fc".to_string(),
                addend: 0,
            },
            GlobalSymbolRef {
                offset: 24,
                symbol: "G".to_string(),
                addend: 16,
            },
        ],
        is_thread_local: false,
        is_import: false,
        is_weak: false,
        align: 1,
    };

    let func = build_x86_const_test_function();
    let elf_bytes = pipeline
        .compile_module_with_globals(std::slice::from_ref(&func), std::slice::from_ref(&vtable))
        .expect("ELF module emission with data relocations should succeed");

    // Valid ELF magic.
    assert_eq!(&elf_bytes[0..4], b"\x7fELF", "ELF magic");

    let relocs = elf_data_relocations(&elf_bytes);
    assert_eq!(
        relocs.len(),
        4,
        "expected 4 data relocations, got {}: {:?}",
        relocs.len(),
        relocs
    );
    for (sec, rela) in &relocs {
        assert!(
            sec == ".rela.data" || sec == ".rela.rodata",
            "data reloc in unexpected section {sec}"
        );
        assert_eq!(
            rela.reloc_type, R_X86_64_64,
            "data reloc must be R_X86_64_64 (absolute 64-bit), got type {}",
            rela.reloc_type
        );
    }

    // Offsets 0, 8, 16, 24 must all be covered.
    let mut offsets: Vec<u64> = relocs.iter().map(|(_, r)| r.r_offset).collect();
    offsets.sort_unstable();
    assert_eq!(offsets, vec![0, 8, 16, 24], "reloc offsets");

    // The &G + 16 slot must carry addend 16 in r_addend (ELF explicit addend).
    let g_reloc = relocs
        .iter()
        .find(|(_, r)| r.r_offset == 24)
        .map(|(_, r)| r)
        .expect("reloc at offset 24");
    assert_eq!(
        g_reloc.r_addend, 16,
        "non-zero addend carried in ELF r_addend"
    );
}
