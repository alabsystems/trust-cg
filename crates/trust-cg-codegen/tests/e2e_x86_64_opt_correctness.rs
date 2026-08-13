// trust-cg-codegen/tests/e2e_x86_64_opt_correctness.rs - x86-64 optimization correctness oracle
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Differential regression tests that exercise the x86-64 *optimization* passes
// (trust-cg-opt's x86_const_fold / x86_cse / x86_dce / x86_peephole, wired into
// the O2/O3 pipeline) against clang. The O0 corpus harness in
// `common/x86_64_corpus.rs` does not run machine optimization passes, so these
// tests compile at O2 and O3 explicitly and link/run the result against a clang
// reference (clang is the golden oracle).
//
// The anchor case is the const-fold Gpr32 implicit zero-extension regression:
// x86-64 writes to a 32-bit register zero-extend into the full 64-bit register,
// so a folded 32-bit constant whose high bit is set (e.g. 0x8000_0000) must be
// tracked as its zero-extended (unsigned) value, NOT a sign-extended one, when
// the same vreg is subsequently read as 64-bit.

mod common;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use common::x86_64_corpus::x86_64_oracle_enabled;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;

use trust_cg_codegen::x86_64::{X86OutputFormat, X86Pipeline, X86PipelineConfig};

use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs;
use trust_cg_lower::function::Signature;
use trust_cg_lower::instructions::Block as X86Block;
use trust_cg_lower::types::Type as X86Type;
use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use trust_ir::{BinOp, CastOp, Constant, FuncTy, Inst, InstrNode};
use trust_ir::{Block as TrustIrBlock, Function as TrustIrFunction, Module as TrustIrModule, Ty};
use trust_ir::{BlockId, FuncId, ValueId};

// =============================================================================
// Local O2/O3 compile + link/run harness (the corpus helper is O0-only).
// =============================================================================

fn compile_module_x86_64(module: &TrustIrModule, opt_level: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level,
        target: Target::X86_64,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("Trust Codegen x86-64 compilation should succeed");
    assert!(
        !result.object_code.is_empty(),
        "Trust Codegen must produce non-empty x86-64 object code"
    );
    result.object_code
}

fn make_test_dir(test_name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("trust_cg_x86_64_opt_{test_name}"));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("Failed to create test directory");
    dir
}

fn cc_x86_64(args: &[&str]) -> Result<(bool, String), String> {
    let mut cmd = Command::new("cc");
    if cfg!(target_os = "macos") {
        cmd.arg("-arch").arg("x86_64");
    }
    for a in args {
        cmd.arg(a);
    }
    let out = cmd
        .output()
        .map_err(|e| format!("cc -arch x86_64 failed to spawn: {e}"))?;
    let stderr = String::from_utf8_lossy(&out.stderr).to_string();
    Ok((out.status.success(), stderr))
}

fn run_binary(binary: &Path) -> Result<(i32, String), String> {
    let out = Command::new(binary)
        .output()
        .map_err(|e| format!("run x86-64 binary failed to spawn: {e}"))?;
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    let exit = out.status.code().unwrap_or(-1);
    Ok((exit, stdout))
}

/// Compile `module` through Trust Codegen at `opt_level` and clang (O0) and
/// assert identical stdout/exit. clang is the golden oracle.
fn differential_at_opt(
    test_name: &str,
    module: &TrustIrModule,
    c_reference: &str,
    driver_src: &str,
    opt_level: OptLevel,
) -> Result<(), String> {
    let dir = make_test_dir(test_name);

    // --- Trust Codegen path (optimized) ---
    let obj = compile_module_x86_64(module, opt_level);
    let obj_path = dir.join("trust_cg_func.o");
    fs::write(&obj_path, &obj).map_err(|e| format!("write trust-cg .o: {e}"))?;

    // --- clang reference path ---
    let ref_c_path = dir.join("reference.c");
    fs::write(&ref_c_path, c_reference).map_err(|e| format!("write reference.c: {e}"))?;
    let clang_obj_path = dir.join("clang_func.o");
    let (ok, e) = cc_x86_64(&[
        "-c",
        "-O0",
        "-o",
        clang_obj_path.to_str().unwrap(),
        ref_c_path.to_str().unwrap(),
    ])?;
    if !ok {
        return Err(format!("cc -c reference.c failed: {e}"));
    }

    // --- shared driver ---
    let driver_path = dir.join("driver.c");
    fs::write(&driver_path, driver_src).map_err(|e| format!("write driver.c: {e}"))?;

    // --- link + run Trust Codegen ---
    let trust_cg_binary = dir.join("test_trust_cg");
    let (ok, e) = cc_x86_64(&[
        "-o",
        trust_cg_binary.to_str().unwrap(),
        driver_path.to_str().unwrap(),
        obj_path.to_str().unwrap(),
    ])?;
    if !ok {
        return Err(format!("Linking Trust Codegen x86-64 binary failed: {e}"));
    }
    let (trust_cg_exit, trust_cg_stdout) = run_binary(&trust_cg_binary)?;

    // --- link + run clang ---
    let clang_binary = dir.join("test_clang");
    let (ok, e) = cc_x86_64(&[
        "-o",
        clang_binary.to_str().unwrap(),
        driver_path.to_str().unwrap(),
        clang_obj_path.to_str().unwrap(),
    ])?;
    if !ok {
        return Err(format!("Linking clang x86-64 binary failed: {e}"));
    }
    let (clang_exit, clang_stdout) = run_binary(&clang_binary)?;

    eprintln!("=== x86-64 opt-correctness differential: {test_name} ({opt_level:?}) ===");
    eprintln!("  Trust Codegen stdout: {}", trust_cg_stdout.trim());
    eprintln!("  Clang stdout:         {}", clang_stdout.trim());

    let _ = fs::remove_dir_all(&dir);

    if trust_cg_stdout != clang_stdout {
        return Err(format!(
            "OUTPUT MISMATCH ({opt_level:?})!\n  Trust Codegen: {}\n  Clang: {}",
            trust_cg_stdout.trim(),
            clang_stdout.trim(),
        ));
    }
    if trust_cg_exit != clang_exit {
        return Err(format!(
            "EXIT CODE MISMATCH ({opt_level:?})!\n  Trust Codegen: {trust_cg_exit}\n  Clang: {clang_exit}"
        ));
    }
    if clang_exit != 0 {
        return Err(format!("Both binaries exited non-zero ({clang_exit})"));
    }
    Ok(())
}

// =============================================================================
// trust_ir builders
// =============================================================================

/// `unsigned long _zext_highbit(long sel)`
///
/// Builds a 32-bit constant whose high bit is set via constant-foldable 32-bit
/// arithmetic, then zero-extends (ZExt) the 32-bit result to 64 bits and
/// returns it.
///
///   int  t32 = (0x40000000 + 0x40000000); // i32 add -> 0x80000000 (high bit)
///   unsigned long r = (unsigned int) t32;  // ZExt i32 -> i64
///   return r;                              // must be 0x80000000 (2147483648)
///
/// On x86-64 the i32 add writes a 32-bit register, which zero-extends into the
/// full 64-bit register; ZExt is then a no-op reinterpretation. The correct
/// result is 0x0000_0000_8000_0000 (2147483648). A const-folder that tracked
/// the folded i32 value as a *sign-extended* i64 (0xffff_ffff_8000_0000) would
/// miscompile the 64-bit read.
fn build_zext_highbit_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_zext_highbit", ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            // half = 0x40000000 (i32)
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0x4000_0000),
            })
            .with_result(ValueId::new(1)),
            // t32 = half + half = 0x80000000 (i32, high bit set)
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: ValueId::new(1),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            // r64 = (u64)(u32) t32  -- zero-extend
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::I32,
                dst_ty: Ty::I64,
                operand: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

/// `unsigned long _zext_shift_highbit(long sel)`
///
///   int  t32 = (1 << 31);             // i32 shift -> 0x80000000 (high bit set)
///   unsigned long r = (unsigned int) t32; // ZExt i32 -> i64
///   return r;                             // must be 0x80000000
///
/// Same property as `_zext_highbit`, reached through a left-shift fold instead
/// of an add fold, to cover the shift constant-fold path.
fn build_zext_shift_highbit_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(
        FuncId::new(0),
        "_zext_shift_highbit",
        ft_id,
        BlockId::new(0),
    );
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(31),
            })
            .with_result(ValueId::new(2)),
            // t32 = 1 << 31 = 0x80000000 (i32)
            InstrNode::new(Inst::BinOp {
                op: BinOp::Shl,
                ty: Ty::I32,
                lhs: ValueId::new(1),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::I32,
                dst_ty: Ty::I64,
                operand: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(4)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

// =============================================================================
// C references + drivers
// =============================================================================

const ZEXT_HIGHBIT_C: &str = r#"
unsigned long _zext_highbit(long sel) {
    (void)sel;
    unsigned int half = 0x40000000u;
    unsigned int t32 = half + half;     /* 0x80000000 as u32 */
    unsigned long r = (unsigned long) t32;
    return r;
}
"#;

const ZEXT_HIGHBIT_DRIVER: &str = r#"
#include <stdio.h>
extern unsigned long _zext_highbit(long sel);
int main(void) {
    printf("zext_highbit=%lu\n", _zext_highbit(0));
    return 0;
}
"#;

const ZEXT_SHIFT_HIGHBIT_C: &str = r#"
unsigned long _zext_shift_highbit(long sel) {
    (void)sel;
    unsigned int t32 = (1u << 31);      /* 0x80000000 as u32 */
    unsigned long r = (unsigned long) t32;
    return r;
}
"#;

const ZEXT_SHIFT_HIGHBIT_DRIVER: &str = r#"
#include <stdio.h>
extern unsigned long _zext_shift_highbit(long sel);
int main(void) {
    printf("zext_shift_highbit=%lu\n", _zext_shift_highbit(0));
    return 0;
}
"#;

// =============================================================================
// Tests
// =============================================================================

#[test]
fn test_x86_64_const_fold_gpr32_zero_extension_o2() {
    if !x86_64_oracle_enabled("const_fold_gpr32_zext_o2") {
        return;
    }
    let module = build_zext_highbit_module();
    let result = differential_at_opt(
        "const_fold_gpr32_zext_o2",
        &module,
        ZEXT_HIGHBIT_C,
        ZEXT_HIGHBIT_DRIVER,
        OptLevel::O2,
    );
    assert!(
        result.is_ok(),
        "x86-64 const-fold Gpr32 zero-extension (O2) failed: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_const_fold_gpr32_zero_extension_o3() {
    if !x86_64_oracle_enabled("const_fold_gpr32_zext_o3") {
        return;
    }
    let module = build_zext_highbit_module();
    let result = differential_at_opt(
        "const_fold_gpr32_zext_o3",
        &module,
        ZEXT_HIGHBIT_C,
        ZEXT_HIGHBIT_DRIVER,
        OptLevel::O3,
    );
    assert!(
        result.is_ok(),
        "x86-64 const-fold Gpr32 zero-extension (O3) failed: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_const_fold_gpr32_shift_zero_extension_o3() {
    if !x86_64_oracle_enabled("const_fold_gpr32_shift_zext_o3") {
        return;
    }
    let module = build_zext_shift_highbit_module();
    let result = differential_at_opt(
        "const_fold_gpr32_shift_zext_o3",
        &module,
        ZEXT_SHIFT_HIGHBIT_C,
        ZEXT_SHIFT_HIGHBIT_DRIVER,
        OptLevel::O3,
    );
    assert!(
        result.is_ok(),
        "x86-64 const-fold Gpr32 shift zero-extension (O3) failed: {}",
        result.unwrap_err()
    );
}

// =============================================================================
// Deterministic ISel-level reproduction of the const-fold Gpr32 implicit
// zero-extension regression.
//
// trust_ir lowers scalar arithmetic to register-register x86 forms, so the
// register-immediate const-fold path is awkward to reach through the front of
// the pipeline. To exercise it precisely and deterministically we build the
// exact ISel instruction stream and drive it through `X86Pipeline` at O2 (which
// runs the x86 const-fold pass), link it with a C driver, run it, and compare
// against a golden C value.
//
// The stream models:
//
//   uint32_t t = 0x40000000u + 0x40000000u;   // foldable Gpr32 AddRI -> 0x80000000
//   uint64_t w = t;                            // MOV r64, r32 zero-extend idiom
//   uint64_t r = w | 1;                        // downstream Gpr64 OrRI
//   return r;                                  // must be 0x0000_0000_8000_0001
//
// The const folder folds the Gpr32 AddRI to `MovRI r32, 0x80000000`, then
// (after the fix) tracks the `MOV r64, r32` zero-extend as the Gpr64 constant
// 0x0000_0000_8000_0000, allowing the downstream `OrRI r64, 1` to fold to
// `MovRI r64, 0x0000_0000_8000_0001`.
//
// Correct result: 2147483649 (0x80000001).
//
// A sign-extending const model would track the zero-extend as
// 0xffff_ffff_8000_0000 and fold the OrRI to 0xffff_ffff_8000_0001 =
// 18446744071562067969, a miscompile this test would catch.
// =============================================================================

fn build_zext_or_isel_function() -> X86ISelFunction {
    let sig = Signature {
        params: vec![X86Type::I64],
        returns: vec![X86Type::I64],
    };
    let mut func = X86ISelFunction::new("_isel_zext_or".to_string(), sig);
    let entry = X86Block(0);
    func.ensure_block(entry);

    let r32_a = VReg::new(0, RegClass::Gpr32);
    let r32_b = VReg::new(1, RegClass::Gpr32);
    let r64_w = VReg::new(2, RegClass::Gpr64);
    let r64_r = VReg::new(3, RegClass::Gpr64);
    func.next_vreg = 4;

    // MOV r32_a, 0x40000000
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![
                X86ISelOperand::VReg(r32_a),
                X86ISelOperand::Imm(0x4000_0000),
            ],
        ),
    );
    // ADD r32_b, r32_a, 0x40000000   (folds to MovRI r32_b, 0x80000000)
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::AddRI,
            vec![
                X86ISelOperand::VReg(r32_b),
                X86ISelOperand::VReg(r32_a),
                X86ISelOperand::Imm(0x4000_0000),
            ],
        ),
    );
    // MOV r64_w, r32_b   (zero-extend idiom: w = zext(b))
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovRR32,
            vec![X86ISelOperand::VReg(r64_w), X86ISelOperand::VReg(r32_b)],
        ),
    );
    // OR r64_r, r64_w, 1   (downstream Gpr64 fold; folds iff zext is tracked)
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::OrRI,
            vec![
                X86ISelOperand::VReg(r64_r),
                X86ISelOperand::VReg(r64_w),
                X86ISelOperand::Imm(1),
            ],
        ),
    );
    // A trailing flag-clobbering compare on an unrelated value makes the OrRI's
    // RFLAGS provably dead, so the const folder is allowed to REPLACE the OrRI
    // with `MovRI r64_r, <folded>`. This is what makes the tracked (possibly
    // sign-extended) constant observable in the emitted code: the returned
    // value then comes from the folded immediate, not from a runtime `or`.
    let r64_z = VReg::new(4, RegClass::Gpr64);
    func.next_vreg = 5;
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![X86ISelOperand::VReg(r64_z), X86ISelOperand::Imm(0)],
        ),
    );
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::CmpRI,
            vec![X86ISelOperand::VReg(r64_z), X86ISelOperand::Imm(0)],
        ),
    );
    // MOV RAX, r64_r
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![
                X86ISelOperand::PReg(x86_64_regs::RAX),
                X86ISelOperand::VReg(r64_r),
            ],
        ),
    );
    func.push_inst(entry, X86ISelInst::new(X86Opcode::Ret, vec![]));
    func
}

fn compile_isel_link_run(
    test_name: &str,
    func: &X86ISelFunction,
    driver_src: &str,
) -> Result<(i32, String), String> {
    let config = X86PipelineConfig {
        output_format: X86OutputFormat::MachO,
        emit_frame: true,
        opt_level: trust_cg_opt::OptLevel::O2,
        ..X86PipelineConfig::default()
    };
    let pipeline = X86Pipeline::new(config);
    let bytes = pipeline
        .compile_function(func)
        .map_err(|e| format!("x86-64 compile_function failed: {e:?}"))?;

    let dir = make_test_dir(test_name);
    let obj_path = dir.join(format!("{test_name}.o"));
    fs::write(&obj_path, &bytes).map_err(|e| format!("write .o: {e}"))?;
    let driver_path = dir.join("driver.c");
    fs::write(&driver_path, driver_src).map_err(|e| format!("write driver.c: {e}"))?;

    let binary = dir.join(format!("test_{test_name}"));
    let (ok, e) = cc_x86_64(&[
        "-o",
        binary.to_str().unwrap(),
        driver_path.to_str().unwrap(),
        obj_path.to_str().unwrap(),
    ])?;
    if !ok {
        return Err(format!("link failed: {e}"));
    }
    let (exit, stdout) = run_binary(&binary)?;
    let _ = fs::remove_dir_all(&dir);
    Ok((exit, stdout))
}

#[test]
fn test_x86_64_const_fold_isel_zext_then_or_o2() {
    if !x86_64_oracle_enabled("const_fold_isel_zext_or_o2") {
        return;
    }

    let func = build_zext_or_isel_function();
    let driver = r#"
#include <stdio.h>
extern unsigned long _isel_zext_or(long sel);
int main(void) {
    printf("isel_zext_or=%lu\n", _isel_zext_or(0));
    return 0;
}
"#;

    // Golden truth computed by clang on the same expression shape.
    let golden_c = r#"
#include <stdio.h>
unsigned long _isel_zext_or(long sel) {
    (void)sel;
    unsigned int t = 0x40000000u + 0x40000000u;  /* 0x80000000 */
    unsigned long w = (unsigned long) t;          /* zero-extend */
    unsigned long r = w | 1ul;
    return r;
}
int main(void) {
    printf("isel_zext_or=%lu\n", _isel_zext_or(0));
    return 0;
}
"#;

    let (exit, stdout) = compile_isel_link_run("const_fold_isel_zext_or_o2", &func, driver)
        .unwrap_or_else(|e| panic!("trust-cg ISel zext-or path failed: {e}"));
    assert_eq!(exit, 0, "trust-cg binary exited non-zero");

    // clang golden.
    let gdir = make_test_dir("const_fold_isel_zext_or_o2_golden");
    let gsrc = gdir.join("golden.c");
    let gbin = gdir.join("golden");
    fs::write(&gsrc, golden_c).expect("write golden.c");
    let (ok, e) = cc_x86_64(&["-O0", "-o", gbin.to_str().unwrap(), gsrc.to_str().unwrap()])
        .expect("cc golden");
    assert!(ok, "golden compile failed: {e}");
    let (gexit, gstdout) = run_binary(&gbin).expect("run golden");
    let _ = fs::remove_dir_all(&gdir);

    eprintln!("=== ISel zext-or O2 ===");
    eprintln!("  trust-cg: {}", stdout.trim());
    eprintln!("  clang:    {}", gstdout.trim());

    assert_eq!(gexit, 0, "golden exited non-zero");
    assert_eq!(
        stdout.trim(),
        gstdout.trim(),
        "const-fold Gpr32 zero-extension miscompile: trust-cg {} vs clang {} \
         (a sign-extending const model would print 18446744071562067969)",
        stdout.trim(),
        gstdout.trim()
    );
    // Pin the exact expected value so the regression is unambiguous.
    assert_eq!(stdout.trim(), "isel_zext_or=2147483649");
}
