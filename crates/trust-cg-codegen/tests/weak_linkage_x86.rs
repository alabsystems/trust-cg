// trust-cg-codegen/tests/weak_linkage_x86.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// OBJECT-LEVEL validation for WEAK / LINK-ONCE global linkage [WEAKLINK-1
// Part 1]. A `Weak` / `LinkOnce` (link-once ODR) global DEFINITION must be
// emitted with the Mach-O `N_WEAK_DEF` (`n_desc` bit `0x0080`) flag so that
// MULTIPLE objects each defining the same symbol COALESCE to one at link time
// instead of raising a duplicate-strong-definition error. This is the primitive
// the cross-static `ptr::eq` fix (Part 2) is built on.
//
// Two levels of coverage, both purely at the object/link level (no runtime
// semantics beyond reading the coalesced value):
//   1. REPARSE: emit a module with a weak global, walk the emitted Mach-O
//      symbol table, and assert `N_WEAK_DEF` is set on the weak symbol (and NOT
//      on a strong control symbol). Runs on any host (cross-emission).
//      - `weak_object_global_emits_n_weak_def_x86`  (X86Pipeline emitter branch)
//      - `weak_linkage_static_maps_to_n_weak_def_x86` (trust-ir Linkage::Weak /
//        LinkOnce -> is_weak -> N_WEAK_DEF, the full frontend->object chain)
//   2. COALESCE: emit TWO objects each DEFINING the same weak symbol, link both
//      against a driver that references it, and assert the link SUCCEEDS (the
//      duplicate weak defs coalesce) and reads the correct value; and that the
//      strong-linkage counterpart FAILS to link (duplicate symbol). Host-gated
//      (x86-64 + cc).
//      - `two_weak_defs_coalesce_link_x86`

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::pipeline::{ObjectGlobal, OptLevel};
use trust_cg_codegen::x86_64::{
    X86OutputFormat, X86Pipeline, X86PipelineConfig, build_x86_const_test_function,
};

use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction, Global,
    Inst, InstrNode, Linkage, Module as TrustIrModule, Ty, ValueId,
};

// =============================================================================
// Mach-O symbol-table reparse (minimal)
// =============================================================================

const LC_SYMTAB: u32 = 0x2;
const MACH_HEADER_64_SIZE: usize = 32;
const NLIST_64_SIZE: usize = 16;
/// `n_desc` weak-definition flag (`<mach-o/nlist.h>`).
const N_WEAK_DEF: u16 = 0x0080;

fn read_u32(b: &[u8], off: usize) -> u32 {
    u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]])
}

/// Parse the Mach-O symbol table and return `name -> n_desc` for every symbol.
fn macho_symbol_descs(bytes: &[u8]) -> HashMap<String, u16> {
    assert_eq!(
        &bytes[0..4],
        &0xFEED_FACFu32.to_le_bytes(),
        "expected a 64-bit Mach-O object"
    );
    let ncmds = read_u32(bytes, 16);
    let mut cmd_off = MACH_HEADER_64_SIZE;
    let (mut symoff, mut nsyms, mut stroff) = (0usize, 0u32, 0usize);
    for _ in 0..ncmds {
        let cmd = read_u32(bytes, cmd_off);
        let cmdsize = read_u32(bytes, cmd_off + 4) as usize;
        if cmd == LC_SYMTAB {
            symoff = read_u32(bytes, cmd_off + 8) as usize;
            nsyms = read_u32(bytes, cmd_off + 12);
            stroff = read_u32(bytes, cmd_off + 16) as usize;
            break;
        }
        cmd_off += cmdsize;
    }
    assert!(nsyms > 0, "Mach-O object has no symbols");

    let mut out = HashMap::new();
    for i in 0..nsyms as usize {
        let e = symoff + i * NLIST_64_SIZE;
        let n_strx = read_u32(bytes, e) as usize;
        let n_desc = u16::from_le_bytes([bytes[e + 6], bytes[e + 7]]);
        let name_start = stroff + n_strx;
        let mut end = name_start;
        while end < bytes.len() && bytes[end] != 0 {
            end += 1;
        }
        let name = String::from_utf8_lossy(&bytes[name_start..end]).to_string();
        out.insert(name, n_desc);
    }
    out
}

// =============================================================================
// ELF symbol-table reparse (minimal)
// =============================================================================

/// `st_info` binding values (`<elf.h>`).
const STB_GLOBAL: u8 = 1;
const STB_WEAK: u8 = 2;
const SHT_SYMTAB: u32 = 2;
const ELF_SYM_SIZE: usize = 24;
const ELF_SHDR_SIZE: usize = 64;

fn read_u16(b: &[u8], off: usize) -> u16 {
    u16::from_le_bytes([b[off], b[off + 1]])
}

fn read_u64(b: &[u8], off: usize) -> u64 {
    u64::from_le_bytes([
        b[off],
        b[off + 1],
        b[off + 2],
        b[off + 3],
        b[off + 4],
        b[off + 5],
        b[off + 6],
        b[off + 7],
    ])
}

/// Parse the ELF `.symtab` and return `name -> st_info binding` for every
/// named symbol. The ELF equivalent of Mach-O's `n_desc` weak inspection:
/// a weak DEFINITION carries the `STB_WEAK` binding (vs `STB_GLOBAL`).
fn elf_symbol_bindings(bytes: &[u8]) -> HashMap<String, u8> {
    assert_eq!(&bytes[0..4], b"\x7FELF", "expected an ELF object");
    assert_eq!(bytes[4], 2, "expected a 64-bit ELF object");
    let shoff = read_u64(bytes, 0x28) as usize;
    let shentsize = read_u16(bytes, 0x3A) as usize;
    let shnum = read_u16(bytes, 0x3C) as usize;
    assert_eq!(shentsize, ELF_SHDR_SIZE, "unexpected e_shentsize");

    let mut out = HashMap::new();
    for i in 0..shnum {
        let sh = shoff + i * shentsize;
        let sh_type = read_u32(bytes, sh + 0x04);
        if sh_type != SHT_SYMTAB {
            continue;
        }
        let sym_off = read_u64(bytes, sh + 0x18) as usize;
        let sym_size = read_u64(bytes, sh + 0x20) as usize;
        let strtab_index = read_u32(bytes, sh + 0x28) as usize; // sh_link
        let strtab_sh = shoff + strtab_index * shentsize;
        let str_off = read_u64(bytes, strtab_sh + 0x18) as usize;

        assert_eq!(sym_size % ELF_SYM_SIZE, 0, "symtab size not entry-aligned");
        for e in (sym_off..sym_off + sym_size).step_by(ELF_SYM_SIZE) {
            let st_name = read_u32(bytes, e) as usize;
            if st_name == 0 {
                continue;
            }
            let st_bind = bytes[e + 4] >> 4;
            let name_start = str_off + st_name;
            let mut end = name_start;
            while end < bytes.len() && bytes[end] != 0 {
                end += 1;
            }
            let name = String::from_utf8_lossy(&bytes[name_start..end]).to_string();
            out.insert(name, st_bind);
        }
    }
    assert!(!out.is_empty(), "ELF object has no named symbols");
    out
}

// =============================================================================
// trust-ir module builders
// =============================================================================

/// A minimal `fn <name>() -> i64 { return 0 }` so the emitted object carries a
/// text symbol (the global is what the test actually inspects).
fn const_func(id: u32, name: &str, ft: trust_ir::FuncTyId) -> TrustIrFunction {
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    }];
    f
}

/// A module with one const function and one immutable byte global of the given
/// linkage. The global's initializer is a raw byte aggregate.
fn module_with_global(
    module_name: &str,
    func_name: &str,
    global_name: &str,
    bytes: &[u8],
    linkage: Linkage,
) -> TrustIrModule {
    let mut module = TrustIrModule::new(module_name);
    let ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    module.add_function(const_func(0, func_name, ft));
    module.globals.push(Global {
        name: global_name.to_string(),
        ty: Ty::I32,
        mutable: false,
        initializer: Some(Constant::Aggregate(
            bytes.iter().map(|b| Constant::Int(*b as i128)).collect(),
        )),
        linkage,
        tls: None,
        align: None,
    });
    module
}

fn compile_x86_64(module: &TrustIrModule) -> Vec<u8> {
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
    assert!(!result.object_code.is_empty());
    result.object_code
}

// =============================================================================
// 1. REPARSE: N_WEAK_DEF on a weak global
// =============================================================================

/// The X86Pipeline Mach-O global emitter must route an `ObjectGlobal { is_weak:
/// true, .. }` through `add_weak_symbol` (=> `N_WEAK_DEF`), while a strong
/// global keeps `n_desc == 0`.
#[test]
fn weak_object_global_emits_n_weak_def_x86() {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        output_format: X86OutputFormat::MachO,
        ..X86PipelineConfig::default()
    });

    let globals = vec![
        ObjectGlobal {
            name: "WEAKG".to_string(),
            data: vec![7, 0, 0, 0],
            mutable: false,
            is_external: true,
            symbol_refs: vec![],
            is_thread_local: false,
            is_import: false,
            is_weak: true,
            align: 8,
        },
        ObjectGlobal {
            name: "STRONGG".to_string(),
            data: vec![9, 0, 0, 0],
            mutable: false,
            is_external: true,
            symbol_refs: vec![],
            is_thread_local: false,
            is_import: false,
            is_weak: false,
            align: 8,
        },
    ];

    let obj = pipeline
        .compile_module_with_globals(&[build_x86_const_test_function()], &globals)
        .expect("x86-64 Mach-O module with a weak global should emit");

    let descs = macho_symbol_descs(&obj);
    let weak_desc = descs
        .get("_WEAKG")
        .copied()
        .expect("weak global symbol _WEAKG must be present");
    let strong_desc = descs
        .get("_STRONGG")
        .copied()
        .expect("strong global symbol _STRONGG must be present");

    assert_ne!(
        weak_desc & N_WEAK_DEF,
        0,
        "a weak global DEFINITION must carry N_WEAK_DEF (0x0080), got n_desc={weak_desc:#06x}"
    );
    assert_eq!(
        strong_desc & N_WEAK_DEF,
        0,
        "a strong global must NOT carry N_WEAK_DEF, got n_desc={strong_desc:#06x}"
    );
}

/// The full frontend->object chain: a trust-ir global with `Weak` / `LinkOnce`
/// linkage maps (in `module_object_globals`) to `ObjectGlobal::is_weak` and is
/// emitted with the weak-definition marker of the HOST-NATIVE object format —
/// Mach-O `N_WEAK_DEF` on macOS, ELF `STB_WEAK` binding on Linux/BSD hosts
/// (the default target spec is OS-aware; asserting Mach-O unconditionally was
/// macOS-assumption test debt, 2026-07-31 x86-Linux battery). An `External`
/// global is NOT weak in either format.
#[test]
fn weak_linkage_static_maps_to_n_weak_def_x86() {
    let is_elf_host = matches!(
        std::env::consts::OS,
        "linux" | "android" | "freebsd" | "netbsd" | "openbsd" | "dragonfly"
    );
    if !is_elf_host && std::env::consts::OS != "macos" {
        panic!(
            "no host-native weak-binding expectation wired for OS {}",
            std::env::consts::OS
        );
    }

    for linkage in [Linkage::Weak, Linkage::LinkOnce] {
        let module = module_with_global("weakmod", "wf", "WSTATIC", &[7, 0, 0, 0], linkage);
        let obj = compile_x86_64(&module);
        if is_elf_host {
            // ELF: the weak DEFINITION carries the STB_WEAK binding (no
            // leading-underscore mangling on ELF).
            let binds = elf_symbol_bindings(&obj);
            let bind = binds
                .get("WSTATIC")
                .copied()
                .unwrap_or_else(|| panic!("WSTATIC missing for linkage {linkage:?}"));
            assert_eq!(
                bind, STB_WEAK,
                "trust-ir {linkage:?} static must emit STB_WEAK, got st_bind={bind}"
            );
        } else {
            let descs = macho_symbol_descs(&obj);
            let desc = descs
                .get("_WSTATIC")
                .copied()
                .unwrap_or_else(|| panic!("_WSTATIC missing for linkage {linkage:?}"));
            assert_ne!(
                desc & N_WEAK_DEF,
                0,
                "trust-ir {linkage:?} static must emit N_WEAK_DEF, got n_desc={desc:#06x}"
            );
        }
    }

    // Control: an External static is strong (STB_GLOBAL / n_desc == 0).
    let module = module_with_global(
        "strongmod",
        "sf",
        "SSTATIC",
        &[7, 0, 0, 0],
        Linkage::External,
    );
    let obj = compile_x86_64(&module);
    if is_elf_host {
        let binds = elf_symbol_bindings(&obj);
        let bind = binds.get("SSTATIC").copied().expect("SSTATIC missing");
        assert_eq!(
            bind, STB_GLOBAL,
            "an External static must be STB_GLOBAL (not weak), got st_bind={bind}"
        );
    } else {
        let descs = macho_symbol_descs(&obj);
        let desc = descs.get("_SSTATIC").copied().expect("_SSTATIC missing");
        assert_eq!(
            desc & N_WEAK_DEF,
            0,
            "an External static must NOT be weak, got n_desc={desc:#06x}"
        );
    }
}

// =============================================================================
// 2. COALESCE: two objects each defining the same weak symbol
// =============================================================================

fn x86_64_link_enabled() -> bool {
    if !cfg!(target_arch = "x86_64") {
        eprintln!("SKIP: weak-coalesce link test requires an x86-64 host");
        return false;
    }
    let cc = Command::new("cc")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    if !cc {
        eprintln!("SKIP: cc not available");
    }
    cc
}

fn test_dir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("trust_cg_weaklink_{name}"));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    dir
}

fn cleanup(dir: &Path) {
    let _ = fs::remove_dir_all(dir);
}

/// Two separate objects each DEFINE `SHARED`. With weak linkage the duplicate
/// definitions coalesce (link succeeds, `main` reads the single value); with
/// strong (External) linkage the same layout is a duplicate-symbol link error.
#[test]
fn two_weak_defs_coalesce_link_x86() {
    if !x86_64_link_enabled() {
        return;
    }
    let dir = test_dir("coalesce");

    // Driver references the shared symbol only.
    let driver = "extern int SHARED;\nint main(void) { return SHARED; }\n";
    let driver_path = dir.join("driver.c");
    fs::write(&driver_path, driver).expect("write driver.c");

    // --- Weak: two defs of SHARED coalesce. ---
    let a = module_with_global("obj_a", "fa", "SHARED", &[7, 0, 0, 0], Linkage::Weak);
    let b = module_with_global("obj_b", "fb", "SHARED", &[7, 0, 0, 0], Linkage::LinkOnce);
    let a_path = dir.join("a.o");
    let b_path = dir.join("b.o");
    fs::write(&a_path, compile_x86_64(&a)).expect("write a.o");
    fs::write(&b_path, compile_x86_64(&b)).expect("write b.o");

    let bin = dir.join("coalesced");
    let link = Command::new("cc")
        .args(if cfg!(target_os = "macos") {
            &["-arch", "x86_64"][..]
        } else {
            &[][..]
        })
        .args([
            "-O0",
            "-o",
            bin.to_str().unwrap(),
            driver_path.to_str().unwrap(),
            a_path.to_str().unwrap(),
            b_path.to_str().unwrap(),
        ])
        .output()
        .expect("run linker");
    assert!(
        link.status.success(),
        "two WEAK defs of SHARED must COALESCE (no duplicate-symbol error):\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(&bin).output().expect("run coalesced binary");
    assert_eq!(
        run.status.code(),
        Some(7),
        "coalesced SHARED must read its value (7)"
    );

    // --- Strong control: two External defs are a duplicate-symbol link error. ---
    let a_strong = module_with_global("obj_a2", "fa2", "SHARED", &[7, 0, 0, 0], Linkage::External);
    let b_strong = module_with_global("obj_b2", "fb2", "SHARED", &[7, 0, 0, 0], Linkage::External);
    let a2 = dir.join("a2.o");
    let b2 = dir.join("b2.o");
    fs::write(&a2, compile_x86_64(&a_strong)).expect("write a2.o");
    fs::write(&b2, compile_x86_64(&b_strong)).expect("write b2.o");
    let bin2 = dir.join("dup");
    let link_strong = Command::new("cc")
        .args(if cfg!(target_os = "macos") {
            &["-arch", "x86_64"][..]
        } else {
            &[][..]
        })
        .args([
            "-O0",
            "-o",
            bin2.to_str().unwrap(),
            driver_path.to_str().unwrap(),
            a2.to_str().unwrap(),
            b2.to_str().unwrap(),
        ])
        .output()
        .expect("run linker (strong)");
    assert!(
        !link_strong.status.success(),
        "two STRONG (External) defs of SHARED MUST be a duplicate-symbol link error \
         (this is the control that proves weak linkage is what enables coalescing)"
    );

    cleanup(&dir);
}
