// trust-cg-codegen/tests/e2e_x86_64_heap_alloc.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// On-host AOT differential oracle for the x86-64 lowering of the trust-ir heap
// primitives `Inst::HeapAlloc` and `Inst::GlobalAddr` (the Box/Vec/String/
// collections enabler).
//
// HeapAlloc lowering (see `translate_heap_alloc` in
// `trust-cg-lower/src/adapter.rs`):
//   * size = count * sizeof(ty), folded when count is a constant, else an
//     emitted i64 `Imul`.
//   * The allocator symbol is chosen from `AllocOrigin`:
//       - `RustHeap` -> `__rust_alloc(size: usize, align: usize) -> *mut u8`
//         (the Rust global allocator; the driver below provides the shim
//         forwarding to the system allocator, exactly as the bridge's
//         allocator shim does).
//       - `CMalloc`  -> `malloc(size: usize)` (libc; alignment satisfied by
//         malloc's fundamental-alignment guarantee).
//       - `SwiftHeap` stays fail-closed (no portable shim yet).
//   * The CALL reuses the external-CALL relocation path (same machinery as the
//     i128-division compiler-rt libcall and memcpy/memmove/memset intrinsics);
//     the returned pointer is the call's result vreg.
//
// GlobalAddr lowering (see `translate_global_addr`): resolves the `GlobalId` to
// the global's symbol name and emits `Opcode::GlobalRef { name }` -> x86
// `LeaRip dst, Symbol(name)` -> a Mach-O RIP-relative relocation the linker
// fills in (identical to the existing data-global-address stub path).
//
// TRUST ASSUMPTION: like every libcall, the correctness of the heap allocation
// itself rests on the EXTERNAL allocator (`__rust_alloc` / `malloc`). It is NOT
// covered by an SMT lowering proof; the abstract heap semantics live in the
// trust-ir Lean spec, and the executable behavior is verified by DIFFERENTIAL
// execution against the clang-compiled C equivalent (malloc + fill + sum)
// below. GlobalAddr is linker-resolved address materialization, verified the
// same way (link + run), with no new SMT proof.
//
// These use the AOT Mach-O path: the produced object is linked with
// `cc -arch x86_64` against a driver that provides `main` and the `__rust_alloc`
// / `__rust_dealloc` shims, so the external CALL relocations resolve at link
// time. Host: x86-64 macOS only; on AArch64 hosts these early-return so they
// never break the Apple-silicon dev machine.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::inst::AllocOrigin;
use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction,
    Global, ICmpOp, Inst, InstrNode, Linkage, Module as TrustIrModule, Ty, ValueId,
};

// =============================================================================
// Host gating + harness (mirrors e2e_x86_64_symbol_address.rs)
// =============================================================================

fn x86_64_oracle_enabled() -> bool {
    if !cfg!(target_arch = "x86_64") {
        eprintln!("SKIP: x86-64 heap-alloc oracle requires an x86-64 host");
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
    let dir = std::env::temp_dir().join(format!("trust_cg_x86_64_heapalloc_{}", test_name));
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

/// Compile the trust-cg object, link against the driver (which supplies
/// `main`, the `__rust_alloc`/`__rust_dealloc` shims, and the reference C
/// definitions under `#ifndef EXTERN_ONLY`), run both the trust-cg and the
/// clang reference, and diff stdout + exit code.
fn differential_test(
    test_name: &str,
    module: &TrustIrModule,
    driver_src: &str,
) -> Result<(), String> {
    let dir = make_test_dir(test_name);

    let obj_bytes = compile_trust_ir_module_x86_64(module);
    let obj_path = dir.join("trust_cg.o");
    fs::write(&obj_path, &obj_bytes).map_err(|e| format!("write .o: {}", e))?;

    let driver_path = dir.join("driver.c");
    fs::write(&driver_path, driver_src).map_err(|e| format!("write driver.c: {}", e))?;

    // trust-cg path: compile the driver in EXTERN_ONLY mode (declarations +
    // shims + main only) and link against the trust-cg object that defines the
    // entry functions / data globals. The allocator CALL relocations and the
    // GlobalRef LEA relocations resolve here.
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
        cleanup(&dir);
        return Err(format!("trust-cg link failed: {}\nnm:\n{}", stderr, nm_out));
    }

    let trust_cg_run = Command::new(&trust_cg_bin)
        .output()
        .map_err(|e| format!("run trust-cg binary: {}", e))?;
    let trust_cg_stdout = String::from_utf8_lossy(&trust_cg_run.stdout).to_string();
    let trust_cg_exit = trust_cg_run.status.code().unwrap_or(-1);

    // clang reference: same driver compiled standalone (clang provides the
    // entry-function / global definitions under `#ifndef EXTERN_ONLY`).
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

    eprintln!("=== x86-64 heap-alloc differential: {} ===", test_name);
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

// =============================================================================
// trust_ir builders
// =============================================================================

/// Build:
///   long FNAME(long n) {
///       long *p = <HeapAlloc i64 x n via ORIGIN>;   // p = alloc(n * 8, 8)
///       for (long i = 0; i < n; i++) p[i] = i * i;
///       long s = 0;
///       for (long i = 0; i < n; i++) s += p[i];
///       return s;
///   }
///
/// `count` is the runtime parameter `n`, exercising the dynamic-size multiply
/// path of `translate_heap_alloc`. Element addressing uses `GEP` (stride =
/// sizeof(i64) = 8).
fn build_heap_sum_squares_module(fname: &str, origin: AllocOrigin) -> TrustIrModule {
    let mut module = TrustIrModule::new("heapsumsq");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    // Value ids:
    //  0  = n (param)
    //  1  = p = HeapAlloc(i64, count=n)
    //  2  = const 0   (loop start / sum init)
    //  3  = const 1   (loop step)
    // Fill loop (block 1): params (10 = i)
    //  11 = i < n
    //  12 = &p[i]   (GEP)
    //  13 = i * i
    //  14 = i + 1
    // Sum loop (block 3): params (20 = i, 21 = s)
    //  22 = i < n
    //  23 = &p[i]
    //  24 = *(&p[i])
    //  25 = s + load
    //  26 = i + 1
    let mut func = TrustIrFunction::new(FuncId::new(0), fname, ft, BlockId::new(0));
    func.blocks = vec![
        // entry: allocate, init constants, jump into fill loop with i = 0
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::HeapAlloc {
                    ty: Ty::I64,
                    count: Some(ValueId::new(0)),
                    align: None,
                    origin,
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(2)],
                }),
            ],
        },
        // fill loop header (block 1): param i = ValueId(10)
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![(ValueId::new(10), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: Ty::I64,
                    lhs: ValueId::new(10),
                    rhs: ValueId::new(0),
                })
                .with_result(ValueId::new(11)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(11),
                    then_target: BlockId::new(2),
                    then_args: vec![],
                    else_target: BlockId::new(3),
                    // start sum loop with i = 0, s = 0 (both ValueId(2))
                    else_args: vec![ValueId::new(2), ValueId::new(2)],
                }),
            ],
        },
        // fill loop body (block 2): p[i] = i * i; i++
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: ValueId::new(1),
                    indices: vec![ValueId::new(10)],
                    inbounds: false,
                })
                .with_result(ValueId::new(12)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Mul,
                    ty: Ty::I64,
                    lhs: ValueId::new(10),
                    rhs: ValueId::new(10),
                })
                .with_result(ValueId::new(13)),
                InstrNode::new(Inst::Store {
                    ty: Ty::I64,
                    ptr: ValueId::new(12),
                    value: ValueId::new(13),
                    volatile: false,
                    align: None,
                }),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(10),
                    rhs: ValueId::new(3),
                })
                .with_result(ValueId::new(14)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(14)],
                }),
            ],
        },
        // sum loop header (block 3): params i = ValueId(20), s = ValueId(21)
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![(ValueId::new(20), Ty::I64), (ValueId::new(21), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: Ty::I64,
                    lhs: ValueId::new(20),
                    rhs: ValueId::new(0),
                })
                .with_result(ValueId::new(22)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(22),
                    then_target: BlockId::new(4),
                    then_args: vec![],
                    else_target: BlockId::new(5),
                    else_args: vec![ValueId::new(21)],
                }),
            ],
        },
        // sum loop body (block 4): s += p[i]; i++
        TrustIrBlock {
            id: BlockId::new(4),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: ValueId::new(1),
                    indices: vec![ValueId::new(20)],
                    inbounds: false,
                })
                .with_result(ValueId::new(23)),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: ValueId::new(23),
                    volatile: false,
                    align: None,
                })
                .with_result(ValueId::new(24)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(21),
                    rhs: ValueId::new(24),
                })
                .with_result(ValueId::new(25)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(20),
                    rhs: ValueId::new(3),
                })
                .with_result(ValueId::new(26)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(3),
                    args: vec![ValueId::new(26), ValueId::new(25)],
                }),
            ],
        },
        // exit (block 5): return accumulated sum (param 30)
        TrustIrBlock {
            id: BlockId::new(5),
            params: vec![(ValueId::new(30), Ty::I64)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(30)],
            })],
        },
    ];
    module.add_function(func);
    module
}

/// `static const long _heap_data_answer = 0x4243; long _use_global() { ... }`
/// Takes the address of a static data global via `Inst::GlobalAddr`, loads it,
/// returns it.
fn build_global_addr_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("globaladdr");

    // Little-endian i64 0x0000_0000_0000_4243 = 16963.
    module.globals.push(Global {
        name: "_heap_data_answer".to_string(),
        ty: Ty::I64,
        mutable: false,
        initializer: Some(Constant::Aggregate(vec![
            Constant::Int(0x43),
            Constant::Int(0x42),
            Constant::Int(0),
            Constant::Int(0),
            Constant::Int(0),
            Constant::Int(0),
            Constant::Int(0),
            Constant::Int(0),
        ])),
        linkage: Linkage::External,
        tls: None,
        align: None,
    });

    let ret_ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let mut entry =
        TrustIrFunction::new(FuncId::new(0), "_use_heap_global", ret_ft, BlockId::new(0));
    entry.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            // p = &_heap_data_answer  -- GlobalAddr
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

// =============================================================================
// Shared driver fragments
// =============================================================================

/// `__rust_alloc` / `__rust_dealloc` shims forwarding to the system allocator,
/// exactly as the bridge's allocator shim does. Provided in both the trust-cg
/// link (where the trust-cg-emitted function CALLs `__rust_alloc`) and the
/// clang reference (harmless there).
const RUST_ALLOC_SHIM: &str = r#"
#include <stdlib.h>
void *__rust_alloc(unsigned long size, unsigned long align) {
    (void)align;
    return malloc(size);
}
void __rust_dealloc(void *ptr, unsigned long size, unsigned long align) {
    (void)size; (void)align;
    free(ptr);
}
"#;

// =============================================================================
// Tests
// =============================================================================

#[test]
fn test_x86_64_heap_alloc_rust_heap_sum_squares() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_heap_sum_squares_module("_heap_sum_squares", AllocOrigin::RustHeap);
    let driver_src = format!(
        r#"
#include <stdio.h>
#include <stdlib.h>
{shim}

#ifndef EXTERN_ONLY
long _heap_sum_squares(long n) {{
    long *p = (long *)__rust_alloc((unsigned long)n * sizeof(long), 8);
    for (long i = 0; i < n; i++) p[i] = i * i;
    long s = 0;
    for (long i = 0; i < n; i++) s += p[i];
    __rust_dealloc(p, (unsigned long)n * sizeof(long), 8);
    return s;
}}
#endif
#ifdef EXTERN_ONLY
extern long _heap_sum_squares(long n);
#endif

int main(void) {{
    printf("h(0)=%ld\n", _heap_sum_squares(0));
    printf("h(1)=%ld\n", _heap_sum_squares(1));
    printf("h(5)=%ld\n", _heap_sum_squares(5));
    printf("h(10)=%ld\n", _heap_sum_squares(10));
    printf("h(100)=%ld\n", _heap_sum_squares(100));
    return 0;
}}
"#,
        shim = RUST_ALLOC_SHIM
    );
    let r = differential_test("rust_heap_sum_squares", &module, &driver_src);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_heap_alloc_cmalloc_sum_squares() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_heap_sum_squares_module("_heap_sum_squares_malloc", AllocOrigin::CMalloc);
    let driver_src = r#"
#include <stdio.h>
#include <stdlib.h>

#ifndef EXTERN_ONLY
long _heap_sum_squares_malloc(long n) {
    long *p = (long *)malloc((unsigned long)n * sizeof(long));
    for (long i = 0; i < n; i++) p[i] = i * i;
    long s = 0;
    for (long i = 0; i < n; i++) s += p[i];
    free(p);
    return s;
}
#endif
#ifdef EXTERN_ONLY
extern long _heap_sum_squares_malloc(long n);
#endif

int main(void) {
    printf("m(0)=%ld\n", _heap_sum_squares_malloc(0));
    printf("m(1)=%ld\n", _heap_sum_squares_malloc(1));
    printf("m(5)=%ld\n", _heap_sum_squares_malloc(5));
    printf("m(10)=%ld\n", _heap_sum_squares_malloc(10));
    printf("m(100)=%ld\n", _heap_sum_squares_malloc(100));
    return 0;
}
"#;
    let r = differential_test("cmalloc_sum_squares", &module, driver_src);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_global_addr_load() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_global_addr_module();
    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
static const long _heap_data_answer = 0x4243;
long _use_heap_global(void) {
    const long *p = &_heap_data_answer;
    return *p;
}
#endif
#ifdef EXTERN_ONLY
extern long _use_heap_global(void);
#endif

int main(void) {
    printf("g=%ld\n", _use_heap_global());
    return 0;
}
"#;
    let r = differential_test("global_addr_load", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}
