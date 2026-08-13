// trust-cg-codegen/tests/e2e_x86_64_symbol_address.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// On-host AOT differential oracle for x86-64 SYMBOL-ADDRESS relocation: taking
// the ADDRESS of a named function or a static data global as a first-class
// value (trust-ir `GlobalRef`). Before this work, raw/AOT x86-64 Mach-O
// emission rejected GlobalRef symbol addresses ("raw module emission cannot
// relocate GlobalRef symbol addresses"), which blocked:
//   (a) function pointers to NAMED in-module functions, and
//   (b) the address of a static/global data symbol.
//
// trust-ir expresses these via:
//   - `Inst::Const { ty: Ty::Func(ft), value: Constant::FnDef(func_id) }`
//     (the address of a defined function), and
//   - `Inst::Const { ty: I64, value: Int(0xFADE<<48 | idx<<32 | off) }` plus a
//     registered `module.globals[idx]` (a data-global address stub).
//
// Both lower to `Opcode::GlobalRef { name }` -> x86 `LeaRip dst, Symbol(name)`
// -> a Mach-O `X86_64_RELOC_SIGNED` (RIP-relative LEA) relocation that the
// linker fills in. This is address materialization (the linker resolves the
// address), so correctness is established by LINK + RUN against clang, not a
// new SMT lowering proof.
//
// The trust_ir interpreter does not model `CallIndirect` / symbol addresses, so
// this is DIFFERENTIAL-ONLY (trust-cg vs clang). Host: x86-64 macOS.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction,
    Global, ICmpOp, Inst, InstrNode, Linkage, Module as TrustIrModule, Ty, ValueId,
};

// =============================================================================
// Host gating + harness (mirrors e2e_x86_64_indirect_calls.rs)
// =============================================================================

fn x86_64_oracle_enabled() -> bool {
    if !cfg!(target_arch = "x86_64") {
        eprintln!("SKIP: x86-64 symbol-address oracle requires an x86-64 host");
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
    let dir = std::env::temp_dir().join(format!("trust_cg_x86_64_symaddr_{}", test_name));
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

    // trust-cg path: compile the driver in EXTERN_ONLY mode (declarations only)
    // and link against the trust-cg object that defines the entry functions /
    // data globals. This is where the symbol-address relocations get resolved
    // by the system linker.
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

    eprintln!("=== x86-64 symbol-address differential: {} ===", test_name);
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

/// Magic global-address stub recognized by the adapter:
///   bits[63:48] = 0xFADE, bits[47:32] = global index, bits[31:0] = byte offset.
fn global_addr_stub(global_index: u64, offset: u32) -> i128 {
    ((0xFADE_u64 << 48) | ((global_index & 0xFFFF) << 32) | (offset as u64)) as i128
}

/// `fn _leaf_add1(a) -> a + 1`
/// `fn _use_fnptr(a) -> (&_leaf_add1)(a)`  -- function-address GlobalRef + CallIndirect
fn build_fn_address_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("fnaddr");
    let unary_ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    // _leaf_add1(a) -> a + 1
    let mut leaf = TrustIrFunction::new(FuncId::new(0), "_leaf_add1", unary_ft, BlockId::new(0));
    leaf.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
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
    module.add_function(leaf);

    // _use_fnptr(a) -> let f = &_leaf_add1; f(a)
    let mut entry = TrustIrFunction::new(FuncId::new(1), "_use_fnptr", unary_ft, BlockId::new(0));
    entry.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            // f = address of _leaf_add1 (FuncId 0) -- GlobalRef
            InstrNode::new(Inst::Const {
                ty: Ty::Func(unary_ft),
                value: Constant::FnDef(FuncId::new(0)),
            })
            .with_result(ValueId::new(1)),
            // r = f(a)
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(1),
                sig: unary_ft,
                args: vec![ValueId::new(0)],
                calling_conv: trust_ir::CallingConv::C,
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

/// `fn _double(a) -> a * 2`, `fn _negate(a) -> -a`
/// `fn _use_dispatch(sel, a) -> (sel != 0 ? &_double : &_negate)(a)`
/// Builds a 2-entry dispatch table from two function-address GlobalRefs, picks
/// one with `Select`, and calls through it.
fn build_dispatch_table_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("dispatchtbl");
    let unary_ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let dispatch_ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    // _double(a) -> a * 2
    let mut dbl = TrustIrFunction::new(FuncId::new(0), "_double", unary_ft, BlockId::new(0));
    dbl.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(2),
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
    module.add_function(dbl);

    // _negate(a) -> 0 - a
    let mut neg = TrustIrFunction::new(FuncId::new(1), "_negate", unary_ft, BlockId::new(0));
    neg.blocks = vec![TrustIrBlock {
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
    module.add_function(neg);

    // _use_dispatch(sel, a) -> (sel != 0 ? &_double : &_negate)(a)
    let mut entry = TrustIrFunction::new(
        FuncId::new(2),
        "_use_dispatch",
        dispatch_ft,
        BlockId::new(0),
    );
    entry.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            // fp_double = &_double
            InstrNode::new(Inst::Const {
                ty: Ty::Func(unary_ft),
                value: Constant::FnDef(FuncId::new(0)),
            })
            .with_result(ValueId::new(2)),
            // fp_negate = &_negate
            InstrNode::new(Inst::Const {
                ty: Ty::Func(unary_ft),
                value: Constant::FnDef(FuncId::new(1)),
            })
            .with_result(ValueId::new(3)),
            // zero
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(4)),
            // cond = sel != 0
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
            // chosen = cond ? fp_double : fp_negate
            InstrNode::new(Inst::Select {
                ty: Ty::Ptr,
                cond: ValueId::new(5),
                then_val: ValueId::new(2),
                else_val: ValueId::new(3),
            })
            .with_result(ValueId::new(6)),
            // r = chosen(a)
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

/// `static const long _data_answer = 0x4243; long _use_global() { return _data_answer; }`
/// Takes the address of a static data global (GlobalRef), loads it, returns it.
fn build_data_global_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("dataglobal");

    // Little-endian i64 0x0000_0000_0000_4243 = 16963.
    module.globals.push(Global {
        name: "_data_answer".to_string(),
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

    let stub = global_addr_stub(0, 0);
    let mut entry = TrustIrFunction::new(FuncId::new(0), "_use_global", ret_ft, BlockId::new(0));
    entry.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            // p = &_data_answer  -- GlobalRef to a data symbol
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(stub),
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
// Tests
// =============================================================================

#[test]
fn test_x86_64_function_address_call_indirect() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_fn_address_module();
    // The C reference takes the address of a NAMED function and calls through it.
    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
static long _leaf_add1(long a) { return a + 1; }
long _use_fnptr(long a) {
    long (*f)(long) = _leaf_add1;
    return f(a);
}
#endif
#ifdef EXTERN_ONLY
extern long _use_fnptr(long a);
#endif

int main(void) {
    printf("f(0)=%ld\n", _use_fnptr(0));
    printf("f(41)=%ld\n", _use_fnptr(41));
    printf("f(-1)=%ld\n", _use_fnptr(-1));
    printf("f(1000000)=%ld\n", _use_fnptr(1000000));
    return 0;
}
"#;
    let r = differential_test("fn_address", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_dispatch_table_of_named_functions() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_dispatch_table_module();
    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
static long _double(long a) { return a * 2; }
static long _negate(long a) { return 0 - a; }
long _use_dispatch(long sel, long a) {
    long (*chosen)(long) = (sel != 0) ? _double : _negate;
    return chosen(a);
}
#endif
#ifdef EXTERN_ONLY
extern long _use_dispatch(long sel, long a);
#endif

int main(void) {
    printf("d(1,5)=%ld\n", _use_dispatch(1, 5));
    printf("d(0,5)=%ld\n", _use_dispatch(0, 5));
    printf("d(7,-3)=%ld\n", _use_dispatch(7, -3));
    printf("d(0,-3)=%ld\n", _use_dispatch(0, -3));
    printf("d(-9,100)=%ld\n", _use_dispatch(-9, 100));
    printf("d(0,100)=%ld\n", _use_dispatch(0, 100));
    return 0;
}
"#;
    let r = differential_test("dispatch_table", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}

#[test]
fn test_x86_64_data_global_address() {
    if !x86_64_oracle_enabled() {
        return;
    }
    let module = build_data_global_module();
    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
static const long _data_answer = 0x4243;
long _use_global(void) {
    const long *p = &_data_answer;
    return *p;
}
#endif
#ifdef EXTERN_ONLY
extern long _use_global(void);
#endif

int main(void) {
    printf("g=%ld\n", _use_global());
    return 0;
}
"#;
    let r = differential_test("data_global", &module, c_source);
    assert!(r.is_ok(), "{}", r.unwrap_err());
}
