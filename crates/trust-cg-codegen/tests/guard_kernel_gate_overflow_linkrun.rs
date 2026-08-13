// guard_kernel_gate_overflow_linkrun.rs — RUNTIME differential oracle for the overflow carrier
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The overflow guard kind's correctness oracle is runtime behavior. The value op is a plain
//! `ADD/SUB`; a separate self-contained `TrapOverflowExact` carrier re-derives flags from its own
//! operands when retained.
//!
//! Downstream `ProofContext` facts and its synthesized `Discharged` status are report-only, so both
//! the synthesized-status and pending-reference fixtures must retain the carrier. The link/run lane
//! proves retained checks return correct non-overflowing values and trap on real overflow.

use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::macho::MachOWriter;
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, encode_function};
use trust_cg_ir::function::MachFunction;
use trust_cg_ir::inst::AArch64Opcode;
use trust_cg_ir::{OverflowOp, pack_overflow_tag};

use trust_cg_lower::function::{BasicBlock, Function as LirFunction, Signature as LirSignature};
use trust_cg_lower::instructions::{Block as LirBlock, Instruction, Opcode, Value};
use trust_cg_lower::{Proof, ProofContext, Type as LirType};

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

/// A bound pending obligation id for the explicit-reference fixture.
const PENDING_OBLIGATION_ID: u64 = 4242;

/// Which report-only downstream status spelling the fixture uses.
#[derive(Clone, Copy)]
enum Mode {
    /// `NoOverflow` plus a downstream-synthesized, report-only Discharged status.
    SynthesizedReportOnly,
    /// `NoOverflow` plus a bound pending obligation.
    PendingReference,
}

/// Build the decoupled LIR `checked_add(a: i64, b: i64) -> i64`:
///
/// ```text
///   v2 = Iadd v0, v1          ; plain value op (NO flags, NO overflow check)
///   GuardOverflow{sadd64} v0, v1   ; SEPARATE self-contained overflow carrier
///   return v2
/// ```
///
/// The `ProofContext` carries `NoOverflow{signed:true}` keyed to BOTH input values so the codegen
/// proof-annotation binder reports `NoSignedOverflow` on the `TrapOverflowExact` carrier. Neither
/// that annotation nor a synthesized status is authority.
fn build(mode: Mode) -> (LirFunction, ProofContext) {
    let sig = LirSignature {
        params: vec![LirType::I64, LirType::I64],
        returns: vec![LirType::I64],
    };
    let mut func = LirFunction::new("checked_add", sig);
    func.entry_block = LirBlock(0);
    func.block_order = vec![LirBlock(0)];

    let a = Value(0);
    let b = Value(1);
    let sum = Value(2);

    let op_tag = pack_overflow_tag(OverflowOp::SignedAdd, 64);

    let mut proof_ctx = ProofContext::default();
    // NoOverflow{signed} keyed to BOTH operands so the binder can match the carrier on lhs OR rhs.
    proof_ctx
        .value_proofs
        .insert(a, vec![Proof::NoOverflow { signed: true }]);
    proof_ctx
        .value_proofs
        .insert(b, vec![Proof::NoOverflow { signed: true }]);

    let obligation = match mode {
        Mode::SynthesizedReportOnly => proof_ctx.synthesize_discharged_obligation(),
        Mode::PendingReference => Some(PENDING_OBLIGATION_ID),
    };

    let block = BasicBlock {
        params: vec![(a, LirType::I64), (b, LirType::I64)],
        instructions: vec![
            // Plain value op — produces a+b, NEVER touched by carrier elimination.
            Instruction {
                opcode: Opcode::Iadd,
                args: vec![a, b],
                results: vec![sum],
            },
            // Self-contained overflow carrier (no result; value is the plain Iadd above).
            Instruction {
                opcode: Opcode::GuardOverflow { op_tag, obligation },
                args: vec![a, b],
                results: vec![],
            },
            Instruction {
                opcode: Opcode::Return,
                args: vec![sum],
                results: vec![],
            },
        ],
        ..Default::default()
    };
    func.blocks.insert(LirBlock(0), block);

    (func, proof_ctx)
}

/// Prepare the function through the real production pipeline.
fn prepare(func: &LirFunction, proof_ctx: &ProofContext) -> MachFunction {
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O2,
        verify: false,
        ..PipelineConfig::default()
    });
    pipeline
        .prepare_function_with_metrics(func, Some(proof_ctx))
        .map(|(prepared, _)| prepared)
        .expect("prepare overflow carrier function")
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

fn make_dir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("trust_cg_ovf_linkrun_{name}"));
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
/// `expected`. Returns the linked binary path.
fn link(dir: &Path, obj: &[u8], a: i64, b: i64, expected: i64) -> PathBuf {
    let obj_path = dir.join("checked_add.o");
    std::fs::write(&obj_path, obj).expect("write object");

    let driver = format!(
        r#"
#include <stdio.h>
#include <stdint.h>
extern long long checked_add(long long a, long long b);
int main(void) {{
    long long r = checked_add({a}LL, {b}LL);
    if (r != ({expected}LL)) {{
        fprintf(stderr, "checked_add => %lld, expected {expected}\n", r);
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

/// Run the binary; returns Ok(()) on exit 0 (correct value, no trap), Err(describe) on a non-zero
/// exit, and a distinguished "TRAPPED" marker when the process was killed by a signal.
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
        // Killed by a signal (the BRK trap raises SIGTRAP/SIGILL): the conventional shell exit code
        // is 128 + sig, which is >= 128.
        Err(format!("TRAPPED (signal {sig}, shell exit {})", 128 + sig))
    } else {
        Err("unknown termination".to_string())
    }
}

/// A synthesized downstream Discharged status is report-only: the guard remains, while a safe call
/// still returns the correct value without trapping.
#[test]
fn overflow_carrier_synthesized_discharge_is_report_only_and_guarded() {
    let (func, ctx) = build(Mode::SynthesizedReportOnly);

    let prepared = prepare(&func, &ctx);
    assert_eq!(
        brk_count(&prepared),
        1,
        "a downstream-synthesized Discharged status must not remove the overflow guard"
    );

    if !is_aarch64_macos() || !has_cc() {
        eprintln!("SKIP runtime half: not AArch64 macOS or cc unavailable");
        return;
    }

    let dir = make_dir("synthesized_report_only");
    let obj = emit_object(&prepared);
    // 2 + 3 = 5, no overflow.
    let bin = link(&dir, &obj, 2, 3, 5);
    run(&bin).expect("retained overflow guard must allow a non-overflowing add");
    let _ = std::fs::remove_dir_all(&dir);
}

/// UNPROVEN: the carrier is KEPT (one guard Brk). A non-overflowing call returns the correct value
/// (no trap); an actually-overflowing call TRAPS — proving the kept carrier really re-derives the
/// overflow condition rather than being inert.
#[test]
fn overflow_carrier_pending_reference_traps_on_actual_overflow_but_correct_otherwise() {
    let (func, ctx) = build(Mode::PendingReference);

    let prepared = prepare(&func, &ctx);
    assert_eq!(
        brk_count(&prepared),
        1,
        "an unproven overflow carrier must be KEPT (exactly one guard Brk: ADDS XZR; B.VC +2; BRK)"
    );

    if !is_aarch64_macos() || !has_cc() {
        eprintln!("SKIP runtime half: not AArch64 macOS or cc unavailable");
        return;
    }

    let dir = make_dir("kept");
    let obj = emit_object(&prepared);

    // (a) Non-overflowing: 100 + 23 = 123, NO trap, correct value.
    {
        let bin = link(&dir, &obj, 100, 23, 123);
        run(&bin).expect("a KEPT carrier must NOT trap on a non-overflowing add");
    }

    // (b) Actually overflowing: i64::MAX + 1 overflows signed -> the kept carrier must TRAP. The
    //     `expected` value is irrelevant; the process should be killed by the trap before returning.
    {
        let bin = link(&dir, &obj, i64::MAX, 1, 0);
        let result = run(&bin);
        match result {
            Err(reason) if reason.starts_with("TRAPPED") => { /* the required outcome */ }
            Err(other) => panic!(
                "actual signed overflow on a KEPT carrier must TRAP (signal), but got: {other}"
            ),
            Ok(()) => panic!(
                "actual signed overflow on a KEPT carrier must TRAP, but the add returned normally \
                 (exit 0) — the kept carrier failed to re-derive the overflow condition"
            ),
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}
