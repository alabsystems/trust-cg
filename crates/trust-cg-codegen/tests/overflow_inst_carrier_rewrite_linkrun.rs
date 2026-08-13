// overflow_inst_carrier_rewrite_linkrun.rs — production auto-rewrite oracle for the trust-ir
// `Inst::Overflow` checked-add idiom -> eliminable `GuardOverflow` carrier (#29).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
//! UNLIKE `guard_kernel_gate_overflow_linkrun.rs` (which hand-builds a `GuardOverflow` LIR op), this
//! test starts from a REAL trust-ir `Inst::Overflow { AddOverflow, I64 }` — the idiom real Trust
//! programs emit for checked add — and drives it through the production lowering
//! (`translate_module` -> `Pipeline` at O2 with the kernel gate at its default-ON setting).
//!
//! It establishes the production auto-rewrite end-to-end:
//!
//!   (a) WITH a discharged `NoOverflow` proof and a DEAD overflow flag, the adapter rewrites the
//!       legacy entangled `CheckedSadd` (ADDS+CSET) into a plain `Iadd` value op + a self-contained
//!       `GuardOverflow` carrier with a SYNTHESIZED discharged obligation. The default-on kernel gate
//!       then ELIMINATES the carrier — the prepared AArch64 stream has NO guard `Brk` — while a
//!       non-overflowing call still returns the CORRECT sum with no trap.
//!
//!   (b) FAIL-SAFE: WITHOUT the proof, the SAME `Inst::Overflow` keeps the legacy `CheckedSadd`
//!       lowering (NO `TrapOverflowExact` carrier is ever emitted), and a non-overflowing call still
//!       returns the correct sum. (The legacy checked path does not trap on its own — it materializes
//!       the (value, did_overflow) pair; the "kept carrier TRAPS on real overflow" half is covered by
//!       the explicit-carrier oracle in guard_kernel_gate_overflow_linkrun.rs.)
//!
//! Compile-time assertions (the carrier is eliminated vs. legacy path is kept) run on ALL platforms;
//! the link+run half is gated on aarch64 macOS with `cc`.

use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::macho::MachOWriter;
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, encode_function};
use trust_cg_ir::function::MachFunction;
use trust_cg_ir::inst::AArch64Opcode;

use trust_ir::{
    Block as TrustIrBlock, BlockId, FuncId, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, OverflowOp, ProofAnnotation, Ty, ValueId,
};

fn is_aarch64_macos() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

fn has_cc() -> bool {
    Command::new("cc")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Build a single-function module `checked_add(a: i64, b: i64) -> i64` whose body is a REAL
/// `Inst::Overflow { AddOverflow, I64 }` returning ONLY the wrapped value (the overflow flag,
/// result[1], is DEAD). When `with_proof` is set, the node carries `ProofAnnotation::NoOverflow`.
fn build_overflow_add_module(name: &str, with_proof: bool) -> TrustIrModule {
    let mut module = TrustIrModule::new(name);
    let func_ty = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let entry = BlockId::new(0);
    let mut func = TrustIrFunction::new(FuncId::new(0), name, func_ty, entry);

    let overflow = InstrNode::new(Inst::Overflow {
        op: OverflowOp::AddOverflow,
        ty: Ty::I64,
        lhs: ValueId::new(0),
        rhs: ValueId::new(1),
    })
    // result[0] = wrapped sum (returned); result[1] = overflow flag (DEAD).
    .with_result(ValueId::new(2))
    .with_result(ValueId::new(3));
    let overflow = if with_proof {
        overflow.with_proof(ProofAnnotation::NoOverflow)
    } else {
        overflow
    };

    func.blocks = vec![TrustIrBlock {
        id: entry,
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            overflow,
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

/// Lower + prepare the module through the REAL pipeline (O2, kernel gate default-ON, AArch64 carrier
/// arch). Returns the prepared MachFunction.
fn prepare(module: &TrustIrModule) -> MachFunction {
    let lowered = trust_cg_lower::translate_module(module).expect("Inst::Overflow module lowers");
    assert_eq!(lowered.len(), 1, "expected one lowered function");

    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O2,
        verify: false,
        ..PipelineConfig::default()
    });
    pipeline
        .prepare_function_with_proofs(&lowered[0].0, Some(&lowered[0].1))
        .expect("Inst::Overflow function prepares")
}

fn brk_count(func: &MachFunction) -> usize {
    let mut n = 0;
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            if func.inst(inst_id).opcode == AArch64Opcode::Brk {
                n += 1;
            }
        }
    }
    n
}

/// Whether any `TrapOverflowExact` carrier survives in the prepared stream (the AArch64 lowering of a
/// KEPT `GuardOverflow`). The eliminated carrier leaves none; the legacy `CheckedSadd` path never
/// emits one.
fn has_trap_overflow_exact(func: &MachFunction) -> bool {
    func.block_order.iter().any(|&block_id| {
        func.block(block_id)
            .insts
            .iter()
            .any(|&inst_id| func.inst(inst_id).opcode == AArch64Opcode::TrapOverflowExact)
    })
}

fn make_dir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("trust_cg_ovf_inst_linkrun_{name}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create test dir");
    dir
}

fn emit_object(func: &MachFunction) -> Vec<u8> {
    let code = encode_function(func).expect("encode prepared overflow function");
    let mut writer = MachOWriter::new();
    writer.add_text_section(&code);
    writer
        .add_symbol(&format!("_{}", func.name), 1, 0, true)
        .unwrap();
    writer.write().unwrap()
}

/// Link the object with a C driver that calls `checked_add(a, b)` and exits 0 iff the result equals
/// `expected`.
fn link(dir: &Path, sym: &str, obj: &[u8], a: i64, b: i64, expected: i64) -> PathBuf {
    let obj_path = dir.join("checked_add.o");
    std::fs::write(&obj_path, obj).expect("write object");

    let driver = format!(
        r#"
#include <stdio.h>
extern long long {sym}(long long a, long long b);
int main(void) {{
    long long r = {sym}({a}LL, {b}LL);
    if (r != ({expected}LL)) {{
        fprintf(stderr, "{sym} => %lld, expected {expected}\n", r);
        return 1;
    }}
    return 0;
}}
"#
    );
    let driver_path = dir.join("driver.c");
    std::fs::write(&driver_path, driver).expect("write driver");

    let bin = dir.join("checked_add_bin");
    let status = Command::new("cc")
        .arg("-o")
        .arg(&bin)
        .arg(&driver_path)
        .arg(&obj_path)
        .arg("-Wl,-no_pie")
        .status()
        .expect("run cc");
    assert!(status.success(), "linking checked_add failed");
    bin
}

fn run(bin: &Path) -> Result<(), String> {
    use std::os::unix::process::ExitStatusExt;
    let out = Command::new(bin).output().expect("run binary");
    if let Some(code) = out.status.code() {
        if code == 0 {
            Ok(())
        } else {
            Err(format!("exit {code}"))
        }
    } else if let Some(sig) = out.status.signal() {
        Err(format!("TRAPPED (signal {sig}, shell exit {})", 128 + sig))
    } else {
        Err("unknown termination".to_string())
    }
}

/// PRODUCTION: a real `Inst::Overflow` add with a DISCHARGED `NoOverflow` proof and a dead flag has
/// its overflow check ELIMINATED (no guard Brk, no surviving TrapOverflowExact carrier) and still
/// computes the correct sum at runtime.
#[test]
fn overflow_inst_proven_dead_flag_eliminates_carrier_and_computes_sum() {
    let module = build_overflow_add_module("checked_add_proven", true);
    let prepared = prepare(&module);

    assert_eq!(
        brk_count(&prepared),
        0,
        "a discharged-NoOverflow Inst::Overflow (dead flag) must have its check ELIMINATED \
         (no guard Brk)"
    );
    assert!(
        !has_trap_overflow_exact(&prepared),
        "the eliminated carrier must leave no TrapOverflowExact in the prepared stream"
    );

    if !is_aarch64_macos() || !has_cc() {
        eprintln!("SKIP runtime half: not AArch64 macOS or cc unavailable");
        return;
    }

    let dir = make_dir("proven");
    let obj = emit_object(&prepared);
    // 2 + 3 = 5, no overflow.
    let bin = link(&dir, "checked_add_proven", &obj, 2, 3, 5);
    run(&bin).expect("proven-safe add must return the correct value with NO trap");
    let _ = std::fs::remove_dir_all(&dir);
}

/// FAIL-SAFE: the SAME real `Inst::Overflow` add WITHOUT a proof keeps the legacy `CheckedSadd`
/// lowering — NO `TrapOverflowExact` carrier is ever emitted (default to KEEP) — and still computes
/// the correct sum at runtime.
#[test]
fn overflow_inst_unproven_keeps_legacy_path_and_computes_sum() {
    let module = build_overflow_add_module("checked_add_unproven", false);
    let prepared = prepare(&module);

    assert!(
        !has_trap_overflow_exact(&prepared),
        "an unproven Inst::Overflow must keep the legacy CheckedSadd path — never an overflow \
         carrier"
    );

    if !is_aarch64_macos() || !has_cc() {
        eprintln!("SKIP runtime half: not AArch64 macOS or cc unavailable");
        return;
    }

    let dir = make_dir("unproven");
    let obj = emit_object(&prepared);
    // 100 + 23 = 123, no overflow.
    let bin = link(&dir, "checked_add_unproven", &obj, 100, 23, 123);
    run(&bin).expect("legacy-path add must return the correct value with NO trap");
    let _ = std::fs::remove_dir_all(&dir);
}
