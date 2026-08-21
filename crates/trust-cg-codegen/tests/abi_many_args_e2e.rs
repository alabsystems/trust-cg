// trust-cg-codegen/tests/abi_many_args_e2e.rs - AAPCS64 >8-arg ABI E2E test
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Verifies the stack-slot overflow path in crates/trust-cg-lower/src/abi.rs::classify_params.
// Apple AArch64 ABI (AAPCS64):
//   - GPR args 0-7 in X0-X7; arg 8+ spills to SP+0, SP+8, ... (8-byte aligned).
//   - FPR args 0-7 in V0-V7; arg 8+ spills to stack (8-byte aligned for F64).
//
// If the ABI is broken (e.g., overflow args read from the wrong slot), the
// compiled function returns a wrong sum and the `cc`-linked driver exits
// non-zero. If the ABI is correct, the driver prints "OK".
//
// Part of #489, #495, #534

#![cfg(target_arch = "aarch64")]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};

use trust_ir::{BinOp, Inst, InstrNode};
use trust_ir::{
    Block as TrustIrBlock, CastOp, Constant, FuncTy, Function as TrustIrFunction,
    Module as TrustIrModule,
};
use trust_ir::{BlockId, FuncId, Ty, ValueId};

// ---------------------------------------------------------------------------
// Host-native object support (GB10 re-baseline): these e2e tests emit objects
// the HOST toolchain links and runs, so emission, magic checks, PIE flags and
// disassembly must follow the host format — Mach-O on macOS, ELF elsewhere.
// ---------------------------------------------------------------------------

#[allow(dead_code)]
fn host_aarch64_triple() -> &'static str {
    if cfg!(target_os = "macos") {
        "aarch64-apple-darwin"
    } else {
        "aarch64-unknown-linux-gnu"
    }
}

#[allow(dead_code)]
fn host_no_pie_flag() -> &'static str {
    if cfg!(target_os = "macos") {
        "-Wl,-no_pie"
    } else {
        "-no-pie"
    }
}

#[allow(dead_code)]
fn host_object_magic_u32() -> u32 {
    if cfg!(target_os = "macos") {
        0xFEED_FACF
    } else {
        u32::from_le_bytes([0x7F, b'E', b'L', b'F'])
    }
}

#[allow(dead_code)]
fn assert_host_object_magic_bytes(obj_bytes: &[u8], context: &str) {
    assert!(obj_bytes.len() >= 4, "{context}: object too small");
    let expected = host_object_magic_u32().to_le_bytes();
    assert_eq!(
        &obj_bytes[0..4],
        &expected,
        "{context}: object magic must match the host-native format"
    );
}

// ---------------------------------------------------------------------------
// Helpers (mirror crates/trust-cg-codegen/tests/ty_bfs_minimal.rs)
// ---------------------------------------------------------------------------

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn is_aarch64() -> bool {
    cfg!(target_arch = "aarch64")
}

fn has_cc() -> bool {
    Command::new("cc")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn make_test_dir(test_name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("trust_cg_e2e_{}", test_name));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    dir
}

fn write_object_file(dir: &Path, filename: &str, bytes: &[u8]) -> PathBuf {
    let path = dir.join(filename);
    fs::write(&path, bytes).expect("write .o file");
    path
}

fn write_c_driver(dir: &Path, filename: &str, source: &str) -> PathBuf {
    let path = dir.join(filename);
    fs::write(&path, source).expect("write C driver");
    path
}

fn link_with_cc(dir: &Path, driver_c: &Path, obj: &Path, output_name: &str) -> PathBuf {
    let binary = dir.join(output_name);
    let result = Command::new("cc")
        .arg("-o")
        .arg(&binary)
        .arg(driver_c)
        .arg(obj)
        .arg(host_no_pie_flag())
        .output()
        .expect("run cc");
    if !result.status.success() {
        let stderr = String::from_utf8_lossy(&result.stderr);
        panic!("Linking failed: {}", stderr);
    }
    binary
}

fn run_binary(binary: &Path) -> (i32, String) {
    let result = Command::new(binary).output().expect("run binary");
    let stdout = String::from_utf8_lossy(&result.stdout).to_string();
    (result.status.code().unwrap_or(-1), stdout)
}

fn assert_linked_object_runs_ok(
    dir: &Path,
    driver_path: &Path,
    obj_name: &str,
    obj_bytes: &[u8],
    binary_name: &str,
) {
    let obj_path = write_object_file(dir, obj_name, obj_bytes);
    let binary = link_with_cc(dir, driver_path, &obj_path, binary_name);

    let (exit_code, stdout) = run_binary(&binary);
    assert_eq!(
        exit_code, 0,
        "{} should exit cleanly; stdout: {}",
        binary_name, stdout
    );
    assert_eq!(
        stdout.trim(),
        "OK",
        "{} unexpected driver output: {}",
        binary_name,
        stdout
    );
}

fn cleanup(dir: &Path) {
    let _ = fs::remove_dir_all(dir);
}

fn compile_trust_ir(
    trust_ir_func: &TrustIrFunction,
    module: &TrustIrModule,
    opt_level: OptLevel,
) -> Result<Vec<u8>, String> {
    let (lir_func, _proof_ctx) = trust_cg_lower::translate_function(trust_ir_func, module)
        .map_err(|e| format!("adapter: {}", e))?;
    let config = PipelineConfig {
        target_triple: host_aarch64_triple().to_string(),
        opt_level,
        emit_debug: false,
        ..Default::default()
    };
    let pipeline = Pipeline::new(config);
    pipeline
        .compile_function(&lir_func)
        .map_err(|e| format!("pipeline: {}", e))
}

fn assert_valid_macho(bytes: &[u8], ctx: &str) {
    assert!(
        bytes.len() >= 4,
        "{}: too small ({} bytes)",
        ctx,
        bytes.len()
    );
    assert_eq!(
        &bytes[0..4],
        &host_object_magic_u32().to_le_bytes(),
        "{}: invalid host object magic",
        ctx
    );
}

struct VidCounter(u32);

impl VidCounter {
    fn new(start: u32) -> Self {
        Self(start)
    }

    fn next(&mut self) -> ValueId {
        let v = ValueId::new(self.0);
        self.0 += 1;
        v
    }
}

#[allow(dead_code)]
fn const_i64(vid: &mut VidCounter, val: i64) -> (ValueId, InstrNode) {
    let r = vid.next();
    let node = InstrNode::new(Inst::Const {
        ty: Ty::I64,
        value: Constant::Int(val as i128),
    })
    .with_result(r);
    (r, node)
}

fn binop_i64(vid: &mut VidCounter, op: BinOp, lhs: ValueId, rhs: ValueId) -> (ValueId, InstrNode) {
    let r = vid.next();
    let node = InstrNode::new(Inst::BinOp {
        op,
        ty: Ty::I64,
        lhs,
        rhs,
    })
    .with_result(r);
    (r, node)
}

fn add_i64(vid: &mut VidCounter, lhs: ValueId, rhs: ValueId) -> (ValueId, InstrNode) {
    binop_i64(vid, BinOp::Add, lhs, rhs)
}

fn fp_to_si_i64(vid: &mut VidCounter, operand: ValueId) -> (ValueId, InstrNode) {
    let r = vid.next();
    let node = InstrNode::new(Inst::Cast {
        op: CastOp::FPToSI,
        src_ty: Ty::F64,
        dst_ty: Ty::I64,
        operand,
    })
    .with_result(r);
    (r, node)
}

// ---------------------------------------------------------------------------
// Test 1: sum10_i64 (10 i64 args, last 2 spill to stack)
// ---------------------------------------------------------------------------
//
// AAPCS64 placement:
//   v(0)..v(7) -> X0..X7  (registers)
//   v(8)       -> [SP + 0]  (stack overflow)
//   v(9)       -> [SP + 8]  (stack overflow)
//
// Body: iterative add chain v(0)+v(1)+...+v(9).
// Expected result for (1,2,3,4,5,6,7,8,9,10): 55.

fn build_sum10_i64() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("abi_sum10_i64");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64; 10],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let entry = b(0);
    let mut func = TrustIrFunction::new(FuncId::new(0), "sum10_i64", ft_id, entry);

    // Block params: v(0)..v(9) all i64.
    let params: Vec<(ValueId, Ty)> = (0..10).map(|i| (v(i), Ty::I64)).collect();

    // Result ids start at 10 to avoid colliding with block params.
    let mut vid = VidCounter::new(10);
    let mut body = Vec::new();

    // Iteratively accumulate: acc = v(0) + v(1); acc = acc + v(2); ...
    let mut acc: ValueId = v(0);
    for i in 1..10u32 {
        let (next, node) = add_i64(&mut vid, acc, v(i));
        body.push(node);
        acc = next;
    }

    body.push(InstrNode::new(Inst::Return { values: vec![acc] }));

    func.blocks = vec![TrustIrBlock {
        id: entry,
        params,
        body,
    }];

    module.add_function(func.clone());
    (func, module)
}

const C_DRIVER_SUM10: &str = r#"
#include <stdint.h>
#include <stdio.h>

extern int64_t sum10_i64(int64_t, int64_t, int64_t, int64_t, int64_t,
                         int64_t, int64_t, int64_t, int64_t, int64_t);

int main(void) {
    int64_t r = sum10_i64(1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
    if (r != 55) {
        printf("sum10_i64 r=%lld expected=55\n", (long long)r);
        return 1;
    }
    printf("OK\n");
    return 0;
}
"#;

fn run_sum10_i64_e2e(opt_level: OptLevel, test_name: &str) {
    if !is_aarch64() {
        eprintln!("skipping {}: requires aarch64", test_name);
        return;
    }
    if !has_cc() {
        eprintln!("skipping {}: cc not available", test_name);
        return;
    }

    let dir = make_test_dir(test_name);
    let (func, module) = build_sum10_i64();
    let obj_bytes =
        compile_trust_ir(&func, &module, opt_level).expect("sum10_i64 compilation should succeed");
    assert_valid_macho(&obj_bytes, test_name);

    let obj_path = write_object_file(&dir, "sum10_i64.o", &obj_bytes);
    let driver_path = write_c_driver(&dir, "driver.c", C_DRIVER_SUM10);
    let binary = link_with_cc(&dir, &driver_path, &obj_path, "sum10_i64_test");

    let (exit_code, stdout) = run_binary(&binary);
    assert_eq!(
        exit_code, 0,
        "binary should exit cleanly; stdout: {}",
        stdout
    );
    assert_eq!(stdout.trim(), "OK", "unexpected driver output: {}", stdout);

    cleanup(&dir);
}

fn run_sum10_i64_o0_o2_semantics(test_name: &str) {
    if !is_aarch64() {
        eprintln!("skipping {}: requires aarch64", test_name);
        return;
    }
    if !has_cc() {
        eprintln!("skipping {}: cc not available", test_name);
        return;
    }

    let dir = make_test_dir(test_name);
    let (func, module) = build_sum10_i64();

    let obj_o0 =
        compile_trust_ir(&func, &module, OptLevel::O0).expect("sum10_i64 should compile at O0");
    let obj_o2 =
        compile_trust_ir(&func, &module, OptLevel::O2).expect("sum10_i64 should compile at O2");
    assert_valid_macho(&obj_o0, "sum10_i64 O0");
    assert_valid_macho(&obj_o2, "sum10_i64 O2");

    let driver_path = write_c_driver(&dir, "driver.c", C_DRIVER_SUM10);
    assert_linked_object_runs_ok(
        &dir,
        &driver_path,
        "sum10_i64_o0.o",
        &obj_o0,
        "sum10_i64_o0_test",
    );
    assert_linked_object_runs_ok(
        &dir,
        &driver_path,
        "sum10_i64_o2.o",
        &obj_o2,
        "sum10_i64_o2_test",
    );

    cleanup(&dir);
}

// ---------------------------------------------------------------------------
// Test 1b: sum20_i64 (20 i64 args, last 12 spill to stack)
// ---------------------------------------------------------------------------
//
// AAPCS64 placement:
//   v(0)..v(7)   -> X0..X7
//   v(8)..v(19)  -> [SP + 0]..[SP + 88] (12 stack slots)
//
// Body: iterative add chain v(0)+v(1)+...+v(19).
// Expected result for (1..20): 210.

fn build_sum20_i64() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("abi_sum20_i64");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64; 20],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let entry = b(0);
    let mut func = TrustIrFunction::new(FuncId::new(0), "sum20_i64", ft_id, entry);

    let params: Vec<(ValueId, Ty)> = (0..20).map(|i| (v(i), Ty::I64)).collect();
    let mut vid = VidCounter::new(20);
    let mut body = Vec::new();

    let mut acc: ValueId = v(0);
    for i in 1..20u32 {
        let (next, node) = add_i64(&mut vid, acc, v(i));
        body.push(node);
        acc = next;
    }

    body.push(InstrNode::new(Inst::Return { values: vec![acc] }));

    func.blocks = vec![TrustIrBlock {
        id: entry,
        params,
        body,
    }];

    module.add_function(func.clone());
    (func, module)
}

const C_DRIVER_SUM20: &str = r#"
#include <stdint.h>
#include <stdio.h>

extern int64_t sum20_i64(int64_t, int64_t, int64_t, int64_t, int64_t,
                         int64_t, int64_t, int64_t, int64_t, int64_t,
                         int64_t, int64_t, int64_t, int64_t, int64_t,
                         int64_t, int64_t, int64_t, int64_t, int64_t);

int main(void) {
    int64_t r = sum20_i64(1, 2, 3, 4, 5,
                          6, 7, 8, 9, 10,
                          11, 12, 13, 14, 15,
                          16, 17, 18, 19, 20);
    if (r != 210) {
        printf("sum20_i64 r=%lld expected=210\n", (long long)r);
        return 1;
    }
    printf("OK\n");
    return 0;
}
"#;

fn run_sum20_i64_e2e(opt_level: OptLevel, test_name: &str) {
    if !is_aarch64() {
        eprintln!("skipping {}: requires aarch64", test_name);
        return;
    }
    if !has_cc() {
        eprintln!("skipping {}: cc not available", test_name);
        return;
    }

    let dir = make_test_dir(test_name);
    let (func, module) = build_sum20_i64();
    let obj_bytes =
        compile_trust_ir(&func, &module, opt_level).expect("sum20_i64 compilation should succeed");
    assert_valid_macho(&obj_bytes, test_name);

    let obj_path = write_object_file(&dir, "sum20_i64.o", &obj_bytes);
    let driver_path = write_c_driver(&dir, "driver.c", C_DRIVER_SUM20);
    let binary = link_with_cc(&dir, &driver_path, &obj_path, "sum20_i64_test");

    let (exit_code, stdout) = run_binary(&binary);
    assert_eq!(
        exit_code, 0,
        "binary should exit cleanly; stdout: {}",
        stdout
    );
    assert_eq!(stdout.trim(), "OK", "unexpected driver output: {}", stdout);

    cleanup(&dir);
}

fn run_sum20_i64_o0_o2_semantics(test_name: &str) {
    if !is_aarch64() {
        eprintln!("skipping {}: requires aarch64", test_name);
        return;
    }
    if !has_cc() {
        eprintln!("skipping {}: cc not available", test_name);
        return;
    }

    let dir = make_test_dir(test_name);
    let (func, module) = build_sum20_i64();

    let obj_o0 =
        compile_trust_ir(&func, &module, OptLevel::O0).expect("sum20_i64 should compile at O0");
    let obj_o2 =
        compile_trust_ir(&func, &module, OptLevel::O2).expect("sum20_i64 should compile at O2");
    assert_valid_macho(&obj_o0, "sum20_i64 O0");
    assert_valid_macho(&obj_o2, "sum20_i64 O2");

    let driver_path = write_c_driver(&dir, "driver.c", C_DRIVER_SUM20);
    assert_linked_object_runs_ok(
        &dir,
        &driver_path,
        "sum20_i64_o0.o",
        &obj_o0,
        "sum20_i64_o0_test",
    );
    assert_linked_object_runs_ok(
        &dir,
        &driver_path,
        "sum20_i64_o2.o",
        &obj_o2,
        "sum20_i64_o2_test",
    );

    cleanup(&dir);
}

// ---------------------------------------------------------------------------
// Test 2: mixed_4i64_10f64 (4 i64 + 10 f64, last 2 f64 spill to stack)
// ---------------------------------------------------------------------------
//
// AAPCS64 placement:
//   v(0)..v(3)   -> X0..X3   (integer regs; X4..X7 unused)
//   v(4)..v(11)  -> V0..V7   (FP regs)
//   v(12)        -> [SP + 0] (FP overflow, 8-byte aligned)
//   v(13)        -> [SP + 8] (FP overflow)
//
// Body: FPToSI-cast each f64 to i64, then sum all 14 i64 values.
// Expected result for (1,2,3,4, 1.0..10.0): (1+2+3+4) + (1+...+10) = 10 + 55 = 65.

fn build_mixed_4i64_10f64() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("abi_mixed_4i64_10f64");
    let mut params_ty: Vec<Ty> = vec![Ty::I64; 4];
    params_ty.extend(std::iter::repeat_n(Ty::F64, 10));
    let ft_id = module.add_func_type(FuncTy {
        params: params_ty,
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let entry = b(0);
    let mut func = TrustIrFunction::new(FuncId::new(0), "mixed_4i64_10f64", ft_id, entry);

    // Block params: v(0)..v(3) i64, v(4)..v(13) f64.
    let mut params: Vec<(ValueId, Ty)> = (0..4).map(|i| (v(i), Ty::I64)).collect();
    params.extend((4..14).map(|i| (v(i), Ty::F64)));

    // Result ids start at 14.
    let mut vid = VidCounter::new(14);
    let mut body = Vec::new();

    // Cast each f64 parameter to i64.
    let mut casts: Vec<ValueId> = Vec::with_capacity(10);
    for i in 4..14u32 {
        let (r, node) = fp_to_si_i64(&mut vid, v(i));
        body.push(node);
        casts.push(r);
    }

    // Accumulate: start with the 4 i64 block params, then add each cast result.
    let mut acc: ValueId = v(0);
    for i in 1..4u32 {
        let (next, node) = add_i64(&mut vid, acc, v(i));
        body.push(node);
        acc = next;
    }
    for cast_r in &casts {
        let (next, node) = add_i64(&mut vid, acc, *cast_r);
        body.push(node);
        acc = next;
    }

    body.push(InstrNode::new(Inst::Return { values: vec![acc] }));

    func.blocks = vec![TrustIrBlock {
        id: entry,
        params,
        body,
    }];

    module.add_function(func.clone());
    (func, module)
}

const C_DRIVER_MIXED: &str = r#"
#include <stdint.h>
#include <stdio.h>

extern int64_t mixed_4i64_10f64(int64_t, int64_t, int64_t, int64_t,
                                double, double, double, double, double,
                                double, double, double, double, double);

int main(void) {
    int64_t r = mixed_4i64_10f64(1, 2, 3, 4,
                                 1.0, 2.0, 3.0, 4.0, 5.0,
                                 6.0, 7.0, 8.0, 9.0, 10.0);
    // (1+2+3+4) + (1+2+3+4+5+6+7+8+9+10) = 10 + 55 = 65
    if (r != 65) {
        printf("mixed_4i64_10f64 r=%lld expected=65\n", (long long)r);
        return 1;
    }
    printf("OK\n");
    return 0;
}
"#;

fn run_mixed_4i64_10f64_e2e(opt_level: OptLevel, test_name: &str) {
    if !is_aarch64() {
        eprintln!("skipping {}: requires aarch64", test_name);
        return;
    }
    if !has_cc() {
        eprintln!("skipping {}: cc not available", test_name);
        return;
    }

    let dir = make_test_dir(test_name);
    let (func, module) = build_mixed_4i64_10f64();
    let obj_bytes = compile_trust_ir(&func, &module, opt_level)
        .expect("mixed_4i64_10f64 compilation should succeed");
    assert_valid_macho(&obj_bytes, test_name);

    let obj_path = write_object_file(&dir, "mixed_4i64_10f64.o", &obj_bytes);
    let driver_path = write_c_driver(&dir, "driver.c", C_DRIVER_MIXED);
    let binary = link_with_cc(&dir, &driver_path, &obj_path, "mixed_4i64_10f64_test");

    let (exit_code, stdout) = run_binary(&binary);
    assert_eq!(
        exit_code, 0,
        "binary should exit cleanly; stdout: {}",
        stdout
    );
    assert_eq!(stdout.trim(), "OK", "unexpected driver output: {}", stdout);

    cleanup(&dir);
}

// ---------------------------------------------------------------------------
// Test 3: mixed_10i64_10f64_alt (20 alternating GPR/FPR args)
// ---------------------------------------------------------------------------
//
// AAPCS64 placement with alternating i64/f64 parameters:
//   i64 args 0..7  -> X0..X7
//   f64 args 0..7  -> V0..V7
//   final 2 i64 + final 2 f64 values spill in source-order stack slots
//
// Body: FPToSI-cast each f64 to i64, then sum all 20 logical inputs.
// Expected result for integer 1..10 and double 1.0..10.0: 55 + 55 = 110.

fn build_mixed_10i64_10f64_alt() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("abi_mixed_10i64_10f64_alt");
    let mut params_ty = Vec::with_capacity(20);
    for _ in 0..10 {
        params_ty.push(Ty::I64);
        params_ty.push(Ty::F64);
    }
    let ft_id = module.add_func_type(FuncTy {
        params: params_ty,
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let entry = b(0);
    let mut func = TrustIrFunction::new(FuncId::new(0), "mixed_10i64_10f64_alt", ft_id, entry);

    let mut params = Vec::with_capacity(20);
    for i in 0..20u32 {
        let ty = if i % 2 == 0 { Ty::I64 } else { Ty::F64 };
        params.push((v(i), ty));
    }

    let mut vid = VidCounter::new(20);
    let mut body = Vec::new();
    let mut cast_f64_args = Vec::with_capacity(10);

    for i in (1..20u32).step_by(2) {
        let (r, node) = fp_to_si_i64(&mut vid, v(i));
        body.push(node);
        cast_f64_args.push(r);
    }

    let mut acc: ValueId = v(0);
    for i in (2..20u32).step_by(2) {
        let (next, node) = add_i64(&mut vid, acc, v(i));
        body.push(node);
        acc = next;
    }
    for cast_r in &cast_f64_args {
        let (next, node) = add_i64(&mut vid, acc, *cast_r);
        body.push(node);
        acc = next;
    }

    body.push(InstrNode::new(Inst::Return { values: vec![acc] }));

    func.blocks = vec![TrustIrBlock {
        id: entry,
        params,
        body,
    }];

    module.add_function(func.clone());
    (func, module)
}

const C_DRIVER_MIXED20_ALT: &str = r#"
#include <stdint.h>
#include <stdio.h>

extern int64_t mixed_10i64_10f64_alt(int64_t, double, int64_t, double,
                                     int64_t, double, int64_t, double,
                                     int64_t, double, int64_t, double,
                                     int64_t, double, int64_t, double,
                                     int64_t, double, int64_t, double);

int main(void) {
    int64_t r = mixed_10i64_10f64_alt(1, 1.0,
                                      2, 2.0,
                                      3, 3.0,
                                      4, 4.0,
                                      5, 5.0,
                                      6, 6.0,
                                      7, 7.0,
                                      8, 8.0,
                                      9, 9.0,
                                      10, 10.0);
    if (r != 110) {
        printf("mixed_10i64_10f64_alt r=%lld expected=110\n", (long long)r);
        return 1;
    }
    printf("OK\n");
    return 0;
}
"#;

fn run_mixed_10i64_10f64_alt_e2e(opt_level: OptLevel, test_name: &str) {
    if !is_aarch64() {
        eprintln!("skipping {}: requires aarch64", test_name);
        return;
    }
    if !has_cc() {
        eprintln!("skipping {}: cc not available", test_name);
        return;
    }

    let dir = make_test_dir(test_name);
    let (func, module) = build_mixed_10i64_10f64_alt();
    let obj_bytes = compile_trust_ir(&func, &module, opt_level)
        .expect("mixed_10i64_10f64_alt compilation should succeed");
    assert_valid_macho(&obj_bytes, test_name);

    let obj_path = write_object_file(&dir, "mixed_10i64_10f64_alt.o", &obj_bytes);
    let driver_path = write_c_driver(&dir, "driver.c", C_DRIVER_MIXED20_ALT);
    let binary = link_with_cc(&dir, &driver_path, &obj_path, "mixed_10i64_10f64_alt_test");

    let (exit_code, stdout) = run_binary(&binary);
    assert_eq!(
        exit_code, 0,
        "binary should exit cleanly; stdout: {}",
        stdout
    );
    assert_eq!(stdout.trim(), "OK", "unexpected driver output: {}", stdout);

    cleanup(&dir);
}

// ===========================================================================
// Tests — compile-only + O0/O2 divergence + end-to-end
// ===========================================================================

#[test]
fn test_sum10_i64_compiles_o0() {
    let (func, module) = build_sum10_i64();
    let obj_bytes =
        compile_trust_ir(&func, &module, OptLevel::O0).expect("sum10_i64 should compile at O0");
    assert_valid_macho(&obj_bytes, "sum10_i64 O0");
}

#[test]
fn test_sum10_i64_compiles_o2() {
    let (func, module) = build_sum10_i64();
    let obj_bytes =
        compile_trust_ir(&func, &module, OptLevel::O2).expect("sum10_i64 should compile at O2");
    assert_valid_macho(&obj_bytes, "sum10_i64 O2");
}

#[test]
fn test_sum10_i64_o0_vs_o2_differ() {
    // Historical name retained for #437/#618 targeted filters. This straight-line
    // ABI kernel may compile to identical O0/O2 bytes when O2 has nothing to
    // rewrite, so pin the semantic ABI property instead.
    run_sum10_i64_o0_o2_semantics("sum10_i64_o0_vs_o2_semantics");
}

#[test]
fn test_sum10_i64_e2e_correctness() {
    run_sum10_i64_e2e(OptLevel::O0, "sum10_i64_e2e_o0");
}

#[test]
fn test_sum10_i64_e2e_correctness_o2() {
    run_sum10_i64_e2e(OptLevel::O2, "sum10_i64_e2e_o2");
}

#[test]
fn test_sum20_i64_compiles_o0() {
    let (func, module) = build_sum20_i64();
    let obj_bytes =
        compile_trust_ir(&func, &module, OptLevel::O0).expect("sum20_i64 should compile at O0");
    assert_valid_macho(&obj_bytes, "sum20_i64 O0");
}

#[test]
fn test_sum20_i64_compiles_o2() {
    let (func, module) = build_sum20_i64();
    let obj_bytes =
        compile_trust_ir(&func, &module, OptLevel::O2).expect("sum20_i64 should compile at O2");
    assert_valid_macho(&obj_bytes, "sum20_i64 O2");
}

#[test]
fn test_sum20_i64_o0_vs_o2_differ() {
    // Historical name retained for #437/#618 targeted filters. This straight-line
    // ABI kernel may compile to identical O0/O2 bytes when O2 has nothing to
    // rewrite, so pin the semantic ABI property instead.
    run_sum20_i64_o0_o2_semantics("sum20_i64_o0_vs_o2_semantics");
}

#[test]
fn test_sum20_i64_e2e_correctness() {
    run_sum20_i64_e2e(OptLevel::O0, "sum20_i64_e2e_o0");
}

#[test]
fn test_sum20_i64_e2e_correctness_o2() {
    run_sum20_i64_e2e(OptLevel::O2, "sum20_i64_e2e_o2");
}

#[test]
fn test_mixed_4i64_10f64_compiles_o0() {
    let (func, module) = build_mixed_4i64_10f64();
    let obj_bytes = compile_trust_ir(&func, &module, OptLevel::O0)
        .expect("mixed_4i64_10f64 should compile at O0");
    assert_valid_macho(&obj_bytes, "mixed_4i64_10f64 O0");
}

#[test]
fn test_mixed_4i64_10f64_compiles_o2() {
    let (func, module) = build_mixed_4i64_10f64();
    let obj_bytes = compile_trust_ir(&func, &module, OptLevel::O2)
        .expect("mixed_4i64_10f64 should compile at O2");
    assert_valid_macho(&obj_bytes, "mixed_4i64_10f64 O2");
}

#[test]
fn test_mixed_4i64_10f64_o0_vs_o2_differ() {
    let (func, module) = build_mixed_4i64_10f64();
    let obj_o0 = compile_trust_ir(&func, &module, OptLevel::O0)
        .expect("mixed_4i64_10f64 should compile at O0");
    let obj_o2 = compile_trust_ir(&func, &module, OptLevel::O2)
        .expect("mixed_4i64_10f64 should compile at O2");
    assert_ne!(
        obj_o0, obj_o2,
        "O0 and O2 should produce different object files"
    );
}

#[test]
fn test_mixed_4i64_10f64_e2e_correctness() {
    run_mixed_4i64_10f64_e2e(OptLevel::O0, "mixed_4i64_10f64_e2e_o0");
}

#[test]
fn test_mixed_4i64_10f64_e2e_correctness_o2() {
    run_mixed_4i64_10f64_e2e(OptLevel::O2, "mixed_4i64_10f64_e2e_o2");
}

#[test]
fn test_mixed_10i64_10f64_alt_compiles_o0() {
    let (func, module) = build_mixed_10i64_10f64_alt();
    let obj_bytes = compile_trust_ir(&func, &module, OptLevel::O0)
        .expect("mixed_10i64_10f64_alt should compile at O0");
    assert_valid_macho(&obj_bytes, "mixed_10i64_10f64_alt O0");
}

#[test]
fn test_mixed_10i64_10f64_alt_compiles_o2() {
    let (func, module) = build_mixed_10i64_10f64_alt();
    let obj_bytes = compile_trust_ir(&func, &module, OptLevel::O2)
        .expect("mixed_10i64_10f64_alt should compile at O2");
    assert_valid_macho(&obj_bytes, "mixed_10i64_10f64_alt O2");
}

#[test]
fn test_mixed_10i64_10f64_alt_o0_vs_o2_differ() {
    let (func, module) = build_mixed_10i64_10f64_alt();
    let obj_o0 = compile_trust_ir(&func, &module, OptLevel::O0)
        .expect("mixed_10i64_10f64_alt should compile at O0");
    let obj_o2 = compile_trust_ir(&func, &module, OptLevel::O2)
        .expect("mixed_10i64_10f64_alt should compile at O2");
    assert_ne!(
        obj_o0, obj_o2,
        "O0 and O2 should produce different object files"
    );
}

#[test]
fn test_mixed_10i64_10f64_alt_e2e_correctness() {
    run_mixed_10i64_10f64_alt_e2e(OptLevel::O0, "mixed_10i64_10f64_alt_e2e_o0");
}

#[test]
fn test_mixed_10i64_10f64_alt_e2e_correctness_o2() {
    run_mixed_10i64_10f64_alt_e2e(OptLevel::O2, "mixed_10i64_10f64_alt_e2e_o2");
}
