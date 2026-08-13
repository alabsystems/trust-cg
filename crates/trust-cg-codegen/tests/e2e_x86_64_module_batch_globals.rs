// trust-cg-codegen/tests/e2e_x86_64_module_batch_globals.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// CT-BATCH STEP 4 compile+RUN proof (design
// `docs/module-batching-design-2026-07-04.md`): merging GLOBAL-BEARING
// per-function modules must preserve every global-address reference — a missed
// or mis-remapped `0xFADE` stub is a silent WRONG DATA ADDRESS.
//
// The scenario is exactly the collision batching creates:
//
//   module A: `batch_read_a() = *A_PRIV + *SHARED_TAB + batch_read_b()`
//     globals: [0] = A_PRIV (private byte data, Internal)
//              [1] = SHARED_TAB (cross-object IMPORT, defined by the driver)
//     sibling `batch_read_b` present only as an extern DECLARATION.
//   module B: `batch_read_b() = *B_PRIV + *SHARED_TAB`
//     globals: [0] = B_PRIV (DIFFERENT private data, also local index 0!)
//              [1] = SHARED_TAB (identical import)
//
// Both modules pack their private data as global index 0 and the shared import
// as index 1, so an unremapped merge would have B silently reading A's data
// (b = 1111+777 = 1888 instead of 3333+777 = 4110) — a visible corruption the
// run below would catch. The merge must produce ONE object where:
//   * A's stub(0) resolves to A_PRIV, B's stub(0) to B_PRIV (indices shifted),
//   * both stub(1)s resolve to the ONE deduplicated SHARED_TAB import,
//   * A's call to B is an intra-object local resolution,
// and the linked binary must print exactly what clang's reference computes.
//
// Expected values: b = 3333 + 777 = 4110; a = 1111 + 777 + 4110 = 5998.
//
// Host: x86-64 with a system `cc` (mirrors e2e_x86_64_data_reloc.rs). The
// compile itself (merge + object emission + determinism + fail-closed proof
// policy) is asserted even before the link/run stage. Proof promotion holds on
// both host containers: every emitted x86-64 relocation kind carries a
// registered object-relocation proof (Mach-O: macho_data/call_reloc_proofs;
// ELF: elf_data/call_reloc_proofs) plus the container's per-object reparse
// binding.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::global_stub::encode_global_addr_stub;
use trust_cg_codegen::module_merge::merge_modules;

use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction,
    Global, Inst, InstrNode, Linkage, Module as TrustIrModule, Ty, ValueId,
};

// =============================================================================
// Harness
// =============================================================================

fn x86_64_oracle_enabled() -> bool {
    if !cfg!(target_arch = "x86_64") {
        eprintln!("SKIP: x86-64 batch-globals oracle requires an x86-64 host");
        return false;
    }
    if !Command::new("cc")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
    {
        eprintln!("SKIP: cc not available");
        return false;
    }
    true
}

fn make_test_dir(test_name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("trust_cg_x86_64_batchglobals_{}", test_name));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    dir
}

fn cleanup(dir: &Path) {
    let _ = fs::remove_dir_all(dir);
}

/// Link the given trust-cg objects against the driver (EXTERN_ONLY mode) and
/// run; return (stdout, exit code).
fn link_and_run(dir: &Path, tag: &str, objects: &[&Path], driver: &Path) -> (String, i32) {
    let bin = dir.join(format!("test_{tag}"));
    // `-arch` is Darwin-only driver syntax (mirrors the clang-reference
    // invocation below); Linux cc is already targeting the x86-64 host.
    let mut args: Vec<String> = if cfg!(target_os = "macos") {
        vec!["-arch".into(), "x86_64".into()]
    } else {
        vec![]
    };
    args.extend([
        "-DEXTERN_ONLY".into(),
        "-O0".into(),
        "-o".into(),
        bin.to_str().unwrap().into(),
        driver.to_str().unwrap().into(),
    ]);
    for o in objects {
        args.push(o.to_str().unwrap().into());
    }
    let link = Command::new("cc").args(&args).output().expect("link");
    assert!(
        link.status.success(),
        "{tag} link failed: {}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(&bin).output().expect("run");
    (
        String::from_utf8_lossy(&run.stdout).to_string(),
        run.status.code().unwrap_or(-1),
    )
}

// =============================================================================
// trust_ir builders (the bridge's per-function global-bearing module shape)
// =============================================================================

/// Private immutable byte-data global holding one little-endian i64.
fn private_data_global(name: &str, value: i64) -> Global {
    Global {
        name: name.to_string(),
        ty: Ty::Ptr,
        mutable: false,
        initializer: Some(Constant::Aggregate(
            value
                .to_le_bytes()
                .iter()
                .map(|&b| Constant::Int(i128::from(b)))
                .collect(),
        )),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
    }
}

/// Cross-object data import (the bridge's `static mut` reader shape); the
/// C driver DEFINES this symbol in both link modes.
fn shared_import_global() -> Global {
    Global {
        name: "SHARED_TAB".to_string(),
        ty: Ty::Ptr,
        mutable: true,
        initializer: None,
        linkage: Linkage::External,
        tls: None,
        align: None,
    }
}

/// `v(next) = load_i64(&globals[stub_idx])` via the 0xFADE stub the bridge
/// emits: `Const I64 stub` then `Load I64` using the address value directly.
fn push_global_load(body: &mut Vec<InstrNode>, stub_idx: u64, addr_v: u32, out_v: u32) {
    body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(encode_global_addr_stub(stub_idx, 0).expect("valid stub")),
        })
        .with_result(ValueId::new(addr_v)),
    );
    body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::I64,
            ptr: ValueId::new(addr_v),
            volatile: false,
            align: None,
        })
        .with_result(ValueId::new(out_v)),
    );
}

/// Module A: defines `batch_read_a() = *A_PRIV + *SHARED_TAB + batch_read_b()`
/// with `batch_read_b` as an extern DECLARATION (FuncId 1) — the bridge's
/// exact per-function shape for a sibling call.
fn build_module_a() -> TrustIrModule {
    let mut m = TrustIrModule::new("batch_a_mod");
    let ft = m.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    m.globals
        .push(private_data_global("batch_read_a.const.alloc1", 1111)); // index 0
    m.globals.push(shared_import_global()); // index 1

    let mut body = Vec::new();
    push_global_load(&mut body, 0, 0, 1); // v1 = *A_PRIV       (local global 0)
    push_global_load(&mut body, 1, 2, 3); // v3 = *SHARED_TAB   (local global 1)
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(1),
            rhs: ValueId::new(3),
        })
        .with_result(ValueId::new(4)),
    );
    body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(1), // sibling batch_read_b (extern decl)
            args: vec![],
        })
        .with_result(ValueId::new(5)),
    );
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(4),
            rhs: ValueId::new(5),
        })
        .with_result(ValueId::new(6)),
    );
    body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(6)],
    }));

    let mut fa = TrustIrFunction::new(FuncId::new(0), "batch_read_a", ft, BlockId::new(0));
    fa.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body,
    }];
    m.add_function(fa);

    // Bodyless extern declaration of the sibling.
    let fb_decl = TrustIrFunction::new(FuncId::new(1), "batch_read_b", ft, BlockId::new(0));
    m.add_function(fb_decl);
    m
}

/// Module B: defines `batch_read_b() = *B_PRIV + *SHARED_TAB`. Its private
/// data is ALSO local global index 0 — the index collision under merge.
fn build_module_b() -> TrustIrModule {
    let mut m = TrustIrModule::new("batch_b_mod");
    let ft = m.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    m.globals
        .push(private_data_global("batch_read_b.const.alloc1", 3333)); // index 0
    m.globals.push(shared_import_global()); // index 1

    let mut body = Vec::new();
    push_global_load(&mut body, 0, 0, 1); // v1 = *B_PRIV       (local global 0)
    push_global_load(&mut body, 1, 2, 3); // v3 = *SHARED_TAB   (local global 1)
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(1),
            rhs: ValueId::new(3),
        })
        .with_result(ValueId::new(4)),
    );
    body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(4)],
    }));

    let mut fb = TrustIrFunction::new(FuncId::new(0), "batch_read_b", ft, BlockId::new(0));
    fb.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body,
    }];
    m.add_function(fb);
    m
}

const DRIVER_C: &str = r#"
#include <stdio.h>

/* Defined by the driver in BOTH modes: the trust-cg objects IMPORT it. */
long SHARED_TAB = 777;

#ifdef EXTERN_ONLY
extern long batch_read_a(void);
extern long batch_read_b(void);
#else
static const long A_PRIV = 1111;
static const long B_PRIV = 3333;
long batch_read_b(void) { return B_PRIV + SHARED_TAB; }
long batch_read_a(void) { return A_PRIV + SHARED_TAB + batch_read_b(); }
#endif

int main(void) {
    printf("a=%ld b=%ld\n", batch_read_a(), batch_read_b());
    return 0;
}
"#;

fn compile(
    module: &TrustIrModule,
    emit_proofs: bool,
) -> trust_cg_codegen::compiler::CompilationResult {
    Compiler::new(CompilerConfig {
        target: Target::X86_64,
        emit_proofs,
        ..CompilerConfig::default()
    })
    .compile(module)
    .expect("x86-64 compile should succeed")
}

fn assert_relocation_proof_promotion_accepted(module: &TrustIrModule) {
    // The x86-64 object relocation inventory is now promotable on both host
    // containers: every emitted kind carries a standing solver-backed value
    // proof (Mach-O: macho_data/call_reloc_proofs; ELF:
    // elf_data/call_reloc_proofs) and the container's reparse gate (ENC-9 on
    // Mach-O, its ELF sibling) binds the record set of the exact emitted
    // object (default-Enforce). The fail-closed complement (unproved kind /
    // missing or cross-container binding) is covered by the object_inventory
    // unit tests.
    let result = Compiler::new(CompilerConfig {
        target: Target::X86_64,
        emit_proofs: true,
        ..CompilerConfig::default()
    })
    .compile(module)
    .expect("proved x86-64 object relocation inventory must promote");
    assert!(
        result.proofs.is_some(),
        "promoting compile must carry proof certificates"
    );
}

// =============================================================================
// The Step-4 proof
// =============================================================================

#[cfg(not(target_os = "windows"))]
#[test]
fn step4_merged_global_bearing_modules_run_with_the_right_data() {
    // ---- 1. The merge itself: one module, remapped stubs, deduped import.
    let a = build_module_a();
    let b = build_module_b();
    let merged =
        merge_modules(&[a.clone(), b.clone()]).expect("global-bearing merge must succeed (Step 4)");
    assert_eq!(merged.functions.len(), 2, "decl->def dedup");
    assert_eq!(
        merged.globals.len(),
        3,
        "A_PRIV + SHARED_TAB (deduped import) + B_PRIV"
    );

    // ---- 2. Proof promotion succeeds: the object relocation inventory is
    // covered (solver value proofs + the container's per-object reparse
    // binding). The non-promoting object route remains deterministic and
    // supplies the execution oracle below.
    assert_relocation_proof_promotion_accepted(&merged);
    let r1 = compile(&merged, false);
    let r2 = compile(&merged, false);
    assert_eq!(
        r1.metrics.function_count, 2,
        "one object must carry BOTH functions"
    );
    assert!(
        r1.proofs.is_none(),
        "non-promoting compile must not claim proofs"
    );
    assert_eq!(
        r1.object_code, r2.object_code,
        "merged global-bearing compile must be byte-identical (determinism)"
    );
    assert_eq!(r1.proofs, r2.proofs, "proof absence must be deterministic");

    if !x86_64_oracle_enabled() {
        return; // compile-side assertions above still ran.
    }

    // ---- 3. RUN it: merged object vs separate objects vs clang reference.
    let dir = make_test_dir("step4_right_data");
    let driver = dir.join("driver.c");
    fs::write(&driver, DRIVER_C).expect("write driver");

    let merged_obj = dir.join("merged.o");
    fs::write(&merged_obj, &r1.object_code).expect("write merged.o");

    // Separate (per-fn, pre-batching baseline) objects of the SAME inputs.
    let a_obj = dir.join("a.o");
    let b_obj = dir.join("b.o");
    fs::write(&a_obj, compile(&a, false).object_code).expect("write a.o");
    fs::write(&b_obj, compile(&b, false).object_code).expect("write b.o");

    let (merged_out, merged_exit) = link_and_run(&dir, "merged", &[&merged_obj], &driver);
    let (sep_out, sep_exit) = link_and_run(&dir, "separate", &[&a_obj, &b_obj], &driver);

    // clang reference: driver compiled standalone.
    let clang_bin = dir.join("test_clang");
    let clang = Command::new("cc")
        .args(if cfg!(target_os = "macos") {
            &["-arch", "x86_64"][..]
        } else {
            &[][..]
        })
        .args([
            "-O0",
            "-o",
            clang_bin.to_str().unwrap(),
            driver.to_str().unwrap(),
        ])
        .output()
        .expect("clang compile");
    assert!(
        clang.status.success(),
        "clang reference compile failed: {}",
        String::from_utf8_lossy(&clang.stderr)
    );
    let clang_run = Command::new(&clang_bin).output().expect("run clang bin");
    let clang_out = String::from_utf8_lossy(&clang_run.stdout).to_string();
    let clang_exit = clang_run.status.code().unwrap_or(-1);

    eprintln!("=== step4 batch-globals differential ===");
    eprintln!("  merged:   {}", merged_out.trim());
    eprintln!("  separate: {}", sep_out.trim());
    eprintln!("  clang:    {}", clang_out.trim());

    // The load-bearing assertions: every global resolved to the RIGHT data.
    // (b reading A's private data would print b=1888; a shared/private swap
    // would corrupt both.)
    assert_eq!(
        clang_out.trim(),
        "a=5998 b=4110",
        "clang reference must compute the expected constants"
    );
    assert_eq!(
        merged_out, clang_out,
        "MERGED output diverges — a stub resolved to the WRONG global"
    );
    assert_eq!(
        merged_out, sep_out,
        "merged vs separate-compilation divergence"
    );
    assert_eq!(merged_exit, 0, "merged binary must exit 0");
    assert_eq!(sep_exit, 0);
    assert_eq!(clang_exit, 0);

    cleanup(&dir);
}
