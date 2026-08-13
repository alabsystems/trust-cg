// E2E: AArch64 Mach-O symbolic DATA relocation — read a local immutable global.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// This is the foundational slice for statics + global data access on aarch64:
// a function that reads a local immutable global compiles to a linkable
// aarch64-apple-darwin Mach-O object via an ADRP/ADD page+pageoff pair
// (`ARM64_RELOC_PAGE21` on the ADRP, `ARM64_RELOC_PAGEOFF12` on the LDR/ADD),
// links with `cc`, runs, and reads back the global's CORRECT value.
//
// The relocation SELECTION/ENCODING for the emitted PAGE21/PAGEOFF12 rows is
// AY-discharged in `trust-cg-verify`
// (`aarch64_macho_data_reloc_proofs`, gated by the
// `proof_gate_strict::aarch64_macho_data_reloc_proofs_are_formally_verified`
// formal floor). This test pins unchecked END-TO-END behavior: the linked
// binary reads the global's exact value. The AY-backed formula and link/run
// regression are not production Certified authority; proof-required promotion
// remains fail-closed for the non-empty relocation inventory.
//
// CORRECTNESS REGRESSION GUARD: immutable globals must land in `__TEXT,__const`
// (`S_REGULAR`, 8-byte aligned), NOT `__cstring`/`S_CSTRING_LITERALS`. The
// linker merges/truncates cstring literals on NUL boundaries, which silently
// miscompiled every immutable global read (the value here came back as
// 0x0100000000004243 instead of 0x4243 before the fix).

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction, Global,
    Inst, InstrNode, Linkage, Module as TrustIrModule, Ty, ValueId,
};

const ANSWER: u64 = 0x0000_0000_0000_4243; // 16963

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

/// `_ag_read() -> i64` returns `*(&_ag_answer)`, where `_ag_answer` is a local
/// immutable 8-byte global holding `ANSWER`.
fn build_read_global_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("readglobal");

    module.globals.push(Global {
        name: "_ag_answer".to_string(),
        ty: Ty::I64,
        mutable: false,
        initializer: Some(Constant::Aggregate(
            ANSWER
                .to_le_bytes()
                .iter()
                .map(|b| Constant::Int(*b as i128))
                .collect(),
        )),
        linkage: Linkage::External,
        tls: None,
        align: None,
    });

    let ret_ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let mut entry = TrustIrFunction::new(FuncId::new(0), "_ag_read", ret_ft, BlockId::new(0));
    entry.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            // p = &_ag_answer   (lowers to ADRP+ADD => PAGE21 + PAGEOFF12)
            InstrNode::new(Inst::GlobalAddr {
                global: trust_ir::value::GlobalId::new(0),
            })
            .with_result(ValueId::new(0)),
            // v = *p
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
    module.add_function(entry);
    module
}

// NOTE: this file uses the default non-proof compile path to pin runtime
// behavior. The production relocation gate is exercised by the pipeline unit
// tests `aarch64_macho_adrp_add_global_inventory_promotes` and
// `aarch64_macho_branch26_and_unsigned_relocation_inventory_promotes`.
// The PAGE21/PAGEOFF12 selection formulas are AY-discharged by
// `proof_gate_strict::aarch64_macho_data_reloc_proofs_are_formally_verified`,
// and the registered lanes plus the ENC-9 Enforce reparse binding now
// authorize Certified object promotion (the x86 348021a1 composition).

/// Full end-to-end: compile -> .o -> cc-link -> run -> read the global's value.
/// Runs only on an aarch64-apple-darwin host (this host qualifies).
#[test]
fn aarch64_read_global_links_runs_and_reads_correct_value() {
    if !can_link_and_run_aarch64_macho() {
        eprintln!("SKIP: requires an aarch64-apple-darwin host");
        return;
    }

    let module = build_read_global_module();
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(&module)
        .expect("aarch64 read-global compile should succeed");
    assert!(
        !result.object_code.is_empty(),
        "object code must be non-empty"
    );

    let dir = std::env::temp_dir().join("trust_cg_aarch64_read_global");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");

    let obj_path = dir.join("read_global.o");
    fs::write(&obj_path, &result.object_code).expect("write .o");

    let driver_path = dir.join("driver.c");
    fs::write(
        &driver_path,
        "#include <stdio.h>\n\
         extern long _ag_read(void);\n\
         int main(void){ long v = _ag_read(); printf(\"%ld\\n\", v); return v == 16963 ? 0 : 1; }\n",
    )
    .expect("write driver.c");

    let bin_path = dir.join("read_global_bin");
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
        "binary returned nonzero (value mismatch); stdout={stdout:?}, status={:?}",
        run.status
    );
    assert_eq!(
        stdout.trim(),
        "16963",
        "the read-back global value must equal 0x4243 = 16963 (a wrong relocation or \
         wrong section type silently miscompiles this)"
    );
}
