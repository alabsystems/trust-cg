// trust-cg-codegen/tests/e2e_x86_64_module_batch_fnptr.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// CT-BATCH-5 compile+RUN proof (design `docs/module-batching-design-2026-07-04.md`,
// the LAST ineligibility class): merging modules that carry FIRST-CLASS
// FUNCTION-POINTER VALUES must preserve every function identity — a missed or
// wrong-but-in-range `FuncId` remap inside a `FnDef`/`Closure` constant is an
// indirect call to the WRONG FUNCTION.
//
// The scenario is exactly the collision batching creates:
//
//   module TARGETS: [0] `fnptr_target(x) = x * 2`   (the intended callee)
//                   [1] `fnptr_decoy(x)  = x + 1000` (same signature, visibly
//                                                     different math)
//   module CALLER:  [0] `fnptr_caller(x)`: materializes `FnDef(fnptr_target)`
//                       — declared as ITS OWN LOCAL FuncId 1 — threads the
//                       pointer through a `Ty::Func` BLOCK PARAMETER, and
//                       invokes it via `CallIndirect`.
//                   [1] extern DECLARATION of `fnptr_target`.
//   module CLOSCLR: [0] `closure_caller(x)`: same shape but the pointer is a
//                       capture-free `Constant::Closure` (the bridge's
//                       lang_start / fn-item-as-value shape).
//                   [1] extern DECLARATION of `fnptr_target`.
//
// Merge order [TARGETS, CALLER, CLOSCLR] forces the remap: the callers' LOCAL
// FuncId(1) must land on merged dense id 0 (`fnptr_target`); an identity
// (missed) remap would leave it pointing at dense id 1 — `fnptr_decoy` — so a
// wrong remap visibly mis-dispatches (a=1021 instead of a=42). The merged
// object must make the indirect call reach the RIGHT function,
// deterministically and byte-run-identically to both separate compilation and
// the clang reference. Proof promotion holds on both host containers: every
// emitted x86-64 relocation kind carries a registered object-relocation proof
// (Mach-O: macho_data/call_reloc_proofs; ELF: elf_data/call_reloc_proofs)
// plus the container's per-object reparse binding.
//
// Host: x86-64 with a system `cc` (mirrors e2e_x86_64_module_batch_globals.rs).
// The compile-side assertions (merge + eligibility + object emission +
// determinism + fail-closed proof-policy check) run even without the link/run
// oracle.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::module_merge::{merge_modules, module_batch_eligible};

use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, CallingConv, Constant, FuncId, FuncTy, FuncTyId,
    Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
};

// =============================================================================
// Harness
// =============================================================================

fn x86_64_oracle_enabled() -> bool {
    if !cfg!(target_arch = "x86_64") {
        eprintln!("SKIP: x86-64 batch-fnptr oracle requires an x86-64 host");
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
    let dir = std::env::temp_dir().join(format!("trust_cg_x86_64_batchfnptr_{}", test_name));
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
// trust_ir builders (the bridge's per-function fn-pointer module shapes)
// =============================================================================

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn node(inst: Inst, results: Vec<u32>) -> InstrNode {
    InstrNode {
        inst,
        results: results.into_iter().map(ValueId::new).collect(),
        proofs: vec![],
        span: None,
        proof_context: None,
        scope: None,
    }
}

/// `(i64) -> i64` as this module's FuncTyId 0.
fn unary_i64_func_ty(m: &mut TrustIrModule) -> FuncTyId {
    m.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    })
}

/// Module TARGETS: `fnptr_target(x) = x * 2` (FuncId 0) and the same-signature
/// DECOY `fnptr_decoy(x) = x + 1000` (FuncId 1).
fn build_targets_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("batch_fnptr_targets_mod");
    let ft = unary_i64_func_ty(&mut m);

    let mut target = TrustIrFunction::new(FuncId::new(0), "fnptr_target", ft, BlockId::new(0));
    target.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(v(0), Ty::I64)],
        body: vec![
            node(
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(0),
                },
                vec![1],
            ),
            node(Inst::Return { values: vec![v(1)] }, vec![]),
        ],
    }];
    m.add_function(target);

    let mut decoy = TrustIrFunction::new(FuncId::new(1), "fnptr_decoy", ft, BlockId::new(0));
    decoy.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(v(0), Ty::I64)],
        body: vec![
            node(
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1000),
                },
                vec![1],
            ),
            node(
                Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(1),
                },
                vec![2],
            ),
            node(Inst::Return { values: vec![v(2)] }, vec![]),
        ],
    }];
    m.add_function(decoy);
    m
}

/// A caller module: `NAME(x)` materializes a function-pointer constant to its
/// sibling `fnptr_target` (an extern DECLARATION at LOCAL FuncId 1), threads
/// it through a `Ty::Func` block parameter, and `CallIndirect`s it. When
/// `as_closure` is set the pointer is a capture-free `Constant::Closure`
/// instead of a `Constant::FnDef` (both bridge shapes).
fn build_caller_module(mod_name: &str, fn_name: &str, as_closure: bool) -> TrustIrModule {
    let mut m = TrustIrModule::new(mod_name);
    let ft = unary_i64_func_ty(&mut m);

    let fnptr_const = if as_closure {
        Constant::Closure {
            func: FuncId::new(1),
            captures: vec![],
        }
    } else {
        Constant::FnDef(FuncId::new(1))
    };

    let mut caller = TrustIrFunction::new(FuncId::new(0), fn_name, ft, BlockId::new(0));
    caller.blocks = vec![
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(v(0), Ty::I64)],
            body: vec![
                node(
                    Inst::Const {
                        ty: Ty::Func(ft),
                        value: fnptr_const,
                    },
                    vec![1],
                ),
                node(
                    Inst::Br {
                        target: BlockId::new(1),
                        args: vec![v(1), v(0)],
                    },
                    vec![],
                ),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(1),
            // The function POINTER as a block parameter (a runtime value).
            params: vec![(v(2), Ty::Func(ft)), (v(3), Ty::I64)],
            body: vec![
                node(
                    Inst::CallIndirect {
                        callee: v(2),
                        sig: ft,
                        args: vec![v(3)],
                        calling_conv: CallingConv::C,
                    },
                    vec![4],
                ),
                node(Inst::Return { values: vec![v(4)] }, vec![]),
            ],
        },
    ];
    m.add_function(caller);

    // Bodyless extern declaration of the target at LOCAL FuncId 1.
    let decl = TrustIrFunction::new(FuncId::new(1), "fnptr_target", ft, BlockId::new(0));
    m.add_function(decl);
    m
}

const DRIVER_C: &str = r#"
#include <stdio.h>

#ifdef EXTERN_ONLY
extern long fnptr_caller(long);
extern long closure_caller(long);
#else
static long fnptr_target(long x) { return x + x; }
typedef long (*unary_fn)(long);
long fnptr_caller(long x) {
    unary_fn fp = fnptr_target; /* volatile-free but opaque enough at -O0 */
    return fp(x);
}
long closure_caller(long x) {
    unary_fn fp = fnptr_target;
    return fp(x);
}
#endif

int main(void) {
    printf("a=%ld b=%ld\n", fnptr_caller(21), closure_caller(10));
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
// The CT-BATCH-5 proof
// =============================================================================

#[cfg(not(target_os = "windows"))]
#[test]
fn batched_fn_pointer_indirect_call_reaches_the_right_function() {
    // ---- 1. Eligibility: the fn-pointer modules are batchable now.
    let targets = build_targets_module();
    let caller = build_caller_module("batch_fnptr_caller_mod", "fnptr_caller", false);
    let closclr = build_caller_module("batch_fnptr_closure_mod", "closure_caller", true);
    for (m, tag) in [
        (&targets, "targets"),
        (&caller, "caller"),
        (&closclr, "closure"),
    ] {
        assert!(
            module_batch_eligible(m).is_ok(),
            "{tag} module must be batch-eligible: {:?}",
            module_batch_eligible(m)
        );
    }

    // ---- 2. The merge: FuncIds shifted, FnDef/Closure constants remapped.
    let merged = merge_modules(&[targets.clone(), caller.clone(), closclr.clone()])
        .expect("fn-pointer merge must succeed (CT-BATCH-5)");
    assert_eq!(merged.functions.len(), 4, "decl->def dedup");
    assert_eq!(merged.functions[0].name, "fnptr_target");
    assert_eq!(merged.functions[1].name, "fnptr_decoy");
    // Both callers' fn-pointer constants must now name the DEFINITION.
    for f in [&merged.functions[2], &merged.functions[3]] {
        let fid = f
            .blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .find_map(|n| match &n.inst {
                Inst::Const {
                    value: Constant::FnDef(fid),
                    ..
                }
                | Inst::Const {
                    value: Constant::Closure { func: fid, .. },
                    ..
                } => Some(*fid),
                _ => None,
            })
            .expect("caller must carry a fn-pointer constant");
        assert_eq!(
            fid,
            FuncId::new(0),
            "`{}`'s fn-pointer constant must resolve to fnptr_target (dense 0); \
             an unremapped id would name the DECOY",
            f.name
        );
    }

    // ---- 3. Proof promotion succeeds: the object relocation inventory is
    // covered (solver value proofs + the container's per-object reparse
    // binding). The non-promoting object route remains deterministic and
    // supplies the execution oracle below.
    assert_relocation_proof_promotion_accepted(&merged);
    let r1 = compile(&merged, false);
    let r2 = compile(&merged, false);
    assert_eq!(
        r1.metrics.function_count, 4,
        "one object must carry all four functions"
    );
    assert!(
        r1.proofs.is_none(),
        "non-promoting compile must not claim proofs"
    );
    assert_eq!(
        r1.object_code, r2.object_code,
        "merged fn-pointer compile must be byte-identical (determinism)"
    );
    assert_eq!(r1.proofs, r2.proofs, "proof absence must be deterministic");

    if !x86_64_oracle_enabled() {
        return; // compile-side assertions above still ran.
    }

    // ---- 4. RUN it: merged object vs separate objects vs clang reference.
    let dir = make_test_dir("right_dispatch");
    let driver = dir.join("driver.c");
    fs::write(&driver, DRIVER_C).expect("write driver");

    let merged_obj = dir.join("merged.o");
    fs::write(&merged_obj, &r1.object_code).expect("write merged.o");

    // Separate (per-fn, pre-batching baseline) objects of the SAME inputs.
    let t_obj = dir.join("targets.o");
    let c_obj = dir.join("caller.o");
    let l_obj = dir.join("closure.o");
    fs::write(&t_obj, compile(&targets, false).object_code).expect("write targets.o");
    fs::write(&c_obj, compile(&caller, false).object_code).expect("write caller.o");
    fs::write(&l_obj, compile(&closclr, false).object_code).expect("write closure.o");

    let (merged_out, merged_exit) = link_and_run(&dir, "merged", &[&merged_obj], &driver);
    let (sep_out, sep_exit) = link_and_run(&dir, "separate", &[&t_obj, &c_obj, &l_obj], &driver);

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

    eprintln!("=== CT-BATCH-5 batch-fnptr differential ===");
    eprintln!("  merged:   {}", merged_out.trim());
    eprintln!("  separate: {}", sep_out.trim());
    eprintln!("  clang:    {}", clang_out.trim());

    // The load-bearing assertions: the indirect calls reached the RIGHT
    // function. (A wrong-but-in-range remap to the decoy would print
    // a=1021 b=1010; an unresolved/wrong relocation would crash or diverge.)
    assert_eq!(
        clang_out.trim(),
        "a=42 b=20",
        "clang reference must compute the expected constants"
    );
    assert_eq!(
        merged_out, clang_out,
        "MERGED output diverges — an indirect call dispatched to the WRONG function"
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
