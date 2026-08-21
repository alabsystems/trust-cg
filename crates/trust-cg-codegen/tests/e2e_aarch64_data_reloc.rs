// E2E: AArch64 Mach-O symbol-address DATA relocation — a function-pointer slot
// in a data global (`ARM64_RELOC_UNSIGNED`, 8-byte absolute pointer).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// This pins the AArch64 counterpart of the x86-64 `X86_64_RELOC_UNSIGNED` /
// `R_X86_64_64` data-relocation path (`e2e_x86_64_data_reloc.rs`): a global
// whose initializer embeds `Constant::SymbolAddr` (a vtable / `static FNS:
// [fn(); N]` slot) is emitted into `__DATA,__data` with an `ARM64_RELOC_UNSIGNED`
// relocation pointing the 8-byte slot at the target symbol. Before the fix the
// generic (non-x86) Mach-O emitter failed closed on any global with
// `symbol_refs`.
//
// The test builds a module with a one-entry function-pointer table
// (`_dg_table = { &dg_target }`) and a reader that loads and returns that
// pointer, links with `cc`, and calls THROUGH the loaded pointer — a wrong or
// missing relocation would return a null/garbage pointer and crash or mismatch.

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction, Global,
    Inst, InstrNode, Linkage, Module as TrustIrModule, Ty, ValueId,
};

/// These fixtures parse Mach-O structure (unwind/LSDA sections), so pin the
/// aarch64-apple-darwin spec explicitly: `Compiler::new` derives the object
/// format from the HOST, which on Linux emits ELF and breaks every Mach-O
/// header parse below. Mach-O byte emission itself is host-independent.
fn macho_compiler(config: CompilerConfig) -> Compiler {
    let spec = trust_cg_codegen::target::TargetSpec::parse("aarch64-apple-darwin")
        .expect("aarch64-apple-darwin parses");
    Compiler::new_for_target_spec(config, spec)
}

const ANSWER: i128 = 16963; // 0x4243

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

/// `dg_target() -> i64` returns `ANSWER`; `dg_read() -> i64` returns the
/// function pointer loaded from `dg_table[0]` (a data relocation to `dg_target`).
fn build_data_reloc_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("datareloc");

    // A one-entry function-pointer table whose slot 0 is `&dg_target`.
    module.globals.push(Global {
        name: "dg_table".to_string(),
        ty: Ty::Ptr,
        mutable: false,
        initializer: Some(Constant::Aggregate(vec![Constant::SymbolAddr {
            symbol: "dg_target".to_string(),
            addend: 0,
        }])),
        linkage: Linkage::External,
        tls: None,
        align: None,
    });

    let ret_ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    // dg_target() -> i64 { ANSWER }
    let mut target = TrustIrFunction::new(FuncId::new(0), "dg_target", ret_ft, BlockId::new(0));
    target.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(ANSWER),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    }];
    module.add_function(target);

    // dg_read() -> i64 { *(&dg_table) }  (loads the relocated fn pointer)
    let mut read = TrustIrFunction::new(FuncId::new(1), "dg_read", ret_ft, BlockId::new(0));
    read.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::GlobalAddr {
                global: trust_ir::value::GlobalId::new(0),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module.add_function(read);

    module
}

/// The compile path itself must SUCCEED on aarch64 (the fail-closed guard is
/// gone) and produce a non-empty Mach-O object. Runs on any host.
#[test]
fn aarch64_data_reloc_module_compiles() {
    let module = build_data_reloc_module();
    let compiler = macho_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(&module)
        .expect("aarch64 data-relocation module must compile (fail-closed guard removed)");
    assert!(
        !result.object_code.is_empty(),
        "object code must be non-empty"
    );
    // Mach-O 64 magic (little-endian MH_MAGIC_64 = 0xFEEDFACF).
    assert_eq!(
        &result.object_code[0..4],
        &[0xCF, 0xFA, 0xED, 0xFE],
        "must be a Mach-O 64 object"
    );
}

/// Full end-to-end: compile -> .o -> cc-link -> call THROUGH the relocated
/// function pointer -> observe `dg_target`'s value. A wrong/missing
/// `ARM64_RELOC_UNSIGNED` yields a null/garbage pointer (crash or mismatch).
#[test]
fn aarch64_data_reloc_links_runs_and_calls_through_pointer() {
    if !can_link_and_run_aarch64_macho() {
        eprintln!("SKIP: requires an aarch64-apple-darwin host");
        return;
    }

    let module = build_data_reloc_module();
    let compiler = macho_compiler(CompilerConfig {
        opt_level: OptLevel::O0,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(&module)
        .expect("aarch64 data-relocation compile should succeed");

    let dir = std::env::temp_dir().join("trust_cg_aarch64_data_reloc");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");

    let obj_path = dir.join("data_reloc.o");
    fs::write(&obj_path, &result.object_code).expect("write .o");

    let driver_path = dir.join("driver.c");
    fs::write(
        &driver_path,
        "#include <stdio.h>\n\
         extern void* dg_read(void);\n\
         extern long dg_target(void);\n\
         int main(void){\n\
             long (*fp)(void) = (long(*)(void))dg_read();\n\
             if ((void*)fp != (void*)dg_target) { printf(\"ptr mismatch\\n\"); return 2; }\n\
             long v = fp();\n\
             printf(\"%ld\\n\", v);\n\
             return v == 16963 ? 0 : 1;\n\
         }\n",
    )
    .expect("write driver.c");

    let bin_path = dir.join("data_reloc_bin");
    let link = Command::new("cc")
        .args([
            driver_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            bin_path.to_str().unwrap(),
        ])
        .output()
        .expect("cc should be available");
    assert!(
        link.status.success(),
        "link failed: {}",
        String::from_utf8_lossy(&link.stderr)
    );

    let run = Command::new(&bin_path).output().expect("run linked binary");
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        run.status.success(),
        "binary returned nonzero (bad data relocation); stdout={stdout:?}, status={:?}",
        run.status
    );
    assert_eq!(
        stdout.trim(),
        "16963",
        "calling through the relocated function pointer must reach dg_target (a wrong \
         ARM64_RELOC_UNSIGNED silently miscompiles the vtable/table slot)"
    );
}
