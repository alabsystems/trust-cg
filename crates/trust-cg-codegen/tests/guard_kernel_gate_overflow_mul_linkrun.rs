// guard_kernel_gate_overflow_mul_linkrun.rs — RUNTIME differential oracle for the MUL overflow carrier
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Runtime oracle for retained multiplication-overflow guards. The carrier expands to the canonical
//! mul-high overflow-detection idiom:
//!
//!   SignedMul@64:   MUL X16; SMULH X17; ASR X16,X16,#63; CMP X17,X16; B.EQ +2; BRK
//!   UnsignedMul@64: UMULH X16; CMP X16,#0; B.EQ +2; BRK
//!
//! Downstream `ProofContext` facts and synthesized `Discharged` statuses are report-only. Both the
//! synthesized-status and pending-reference fixtures must retain the carrier. The link/run lane
//! proves retained checks return exact non-overflowing products and trap on genuine overflow.

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
const PENDING_OBLIGATION_ID: u64 = 7373;

#[derive(Clone, Copy)]
enum Mode {
    SynthesizedReportOnly,
    PendingReference,
}

/// Build `checked_mul(a: i64, b: i64) -> i64`:
///
/// ```text
///   v2 = Imul v0, v1                       ; plain value op (low 64 bits)
///   GuardOverflow{signed/unsigned mul64} v0, v1   ; SEPARATE self-contained mul-overflow carrier
///   return v2
/// ```
fn build(mode: Mode, signed: bool) -> (LirFunction, ProofContext) {
    let sig = LirSignature {
        params: vec![LirType::I64, LirType::I64],
        returns: vec![LirType::I64],
    };
    let mut func = LirFunction::new("checked_mul", sig);
    func.entry_block = LirBlock(0);
    func.block_order = vec![LirBlock(0)];

    let a = Value(0);
    let b = Value(1);
    let prod = Value(2);

    let carrier_op = if signed {
        OverflowOp::SignedMul
    } else {
        OverflowOp::UnsignedMul
    };
    let op_tag = pack_overflow_tag(carrier_op, 64);

    let mut proof_ctx = ProofContext::default();
    // NoOverflow{signed} keyed to BOTH operands so the binder can match the carrier on lhs OR rhs.
    proof_ctx
        .value_proofs
        .insert(a, vec![Proof::NoOverflow { signed }]);
    proof_ctx
        .value_proofs
        .insert(b, vec![Proof::NoOverflow { signed }]);

    let obligation = match mode {
        Mode::SynthesizedReportOnly => proof_ctx.synthesize_discharged_obligation(),
        Mode::PendingReference => Some(PENDING_OBLIGATION_ID),
    };

    let block = BasicBlock {
        params: vec![(a, LirType::I64), (b, LirType::I64)],
        instructions: vec![
            Instruction {
                opcode: Opcode::Imul,
                args: vec![a, b],
                results: vec![prod],
            },
            Instruction {
                opcode: Opcode::GuardOverflow { op_tag, obligation },
                args: vec![a, b],
                results: vec![],
            },
            Instruction {
                opcode: Opcode::Return,
                args: vec![prod],
                results: vec![],
            },
        ],
        ..Default::default()
    };
    func.blocks.insert(LirBlock(0), block);

    (func, proof_ctx)
}

fn prepare(func: &LirFunction, proof_ctx: &ProofContext) -> MachFunction {
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O2,
        verify: false,
        ..PipelineConfig::default()
    });
    pipeline
        .prepare_function_with_metrics(func, Some(proof_ctx))
        .map(|(prepared, _)| prepared)
        .expect("prepare mul overflow carrier function")
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
    let dir = std::env::temp_dir().join(format!("trust_cg_ovf_mul_linkrun_{name}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create test dir");
    dir
}

fn emit_object(func: &MachFunction) -> Vec<u8> {
    let code = encode_function(func).expect("encode prepared mul overflow function");
    let mut writer = MachOWriter::new();
    writer.add_text_section(&code);
    writer
        .add_symbol(&format!("_{}", func.name), 1, 0, true)
        .unwrap();
    writer.write().unwrap()
}

/// Link with a C driver calling `checked_mul(a, b)`. `signed` selects the C operand type so the bit
/// pattern is interpreted correctly (the machine code is identical; only the C decl changes). The
/// `a`/`b`/`expected` are raw 64-bit bit patterns passed as the corresponding C type.
fn link(dir: &Path, obj: &[u8], signed: bool, a: i64, b: i64, expected: i64) -> PathBuf {
    let obj_path = dir.join("checked_mul.o");
    std::fs::write(&obj_path, obj).expect("write object");

    let driver = if signed {
        format!(
            r#"
#include <stdio.h>
extern long long checked_mul(long long a, long long b);
int main(void) {{
    long long r = checked_mul({a}LL, {b}LL);
    if (r != ({expected}LL)) {{
        fprintf(stderr, "checked_mul => %lld, expected {expected}\n", r);
        return 1;
    }}
    return 0;
}}
"#
        )
    } else {
        // Reinterpret the i64 bit patterns as unsigned 64-bit values for the unsigned driver.
        let au = a as u64;
        let bu = b as u64;
        let eu = expected as u64;
        format!(
            r#"
#include <stdio.h>
extern unsigned long long checked_mul(unsigned long long a, unsigned long long b);
int main(void) {{
    unsigned long long r = checked_mul({au}ULL, {bu}ULL);
    if (r != ({eu}ULL)) {{
        fprintf(stderr, "checked_mul => %llu, expected {eu}\n", r);
        return 1;
    }}
    return 0;
}}
"#
        )
    };
    let driver_path = dir.join("driver.c");
    std::fs::write(&driver_path, driver).expect("write driver");

    let bin = dir.join("checked_mul_bin");
    let status = Command::new("cc")
        .arg("-o")
        .arg(&bin)
        .arg(&driver_path)
        .arg(&obj_path)
        .arg("-Wl,-no_pie")
        .status()
        .expect("run cc");
    assert!(status.success(), "linking checked_mul failed");
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

/// A synthesized downstream Discharged status is report-only: the signed-mul guard remains, while a
/// safe call returns the exact product without trapping.
#[test]
fn signed_mul_carrier_synthesized_discharge_is_report_only_and_guarded() {
    let (func, ctx) = build(Mode::SynthesizedReportOnly, true);
    let prepared = prepare(&func, &ctx);
    assert_eq!(
        brk_count(&prepared),
        1,
        "a downstream-synthesized Discharged status must not remove the mul overflow guard"
    );

    if !is_aarch64_macos() || !has_cc() {
        eprintln!("SKIP runtime half: not AArch64 macOS or cc unavailable");
        return;
    }

    let dir = make_dir("signed_synthesized_report_only");
    let obj = emit_object(&prepared);
    // 6 * 7 = 42, no overflow.
    let bin = link(&dir, &obj, true, 6, 7, 42);
    run(&bin).expect("retained signed-mul guard must allow a non-overflowing product");
    let _ = std::fs::remove_dir_all(&dir);
}

/// UNPROVEN (signed): the carrier is KEPT (one guard Brk). A non-overflowing call returns the correct
/// product (no trap); `i64::MIN * -1` (the canonical signed mul overflow) TRAPS — proving the kept
/// carrier really detects mul overflow and the SMULH/ASR/CMP detection is arithmetically EXACT.
#[test]
fn signed_mul_carrier_pending_reference_traps_on_overflow_and_is_exact() {
    let (func, ctx) = build(Mode::PendingReference, true);
    let prepared = prepare(&func, &ctx);
    assert_eq!(
        brk_count(&prepared),
        1,
        "an unproven signed mul carrier must be KEPT (exactly one guard Brk)"
    );

    if !is_aarch64_macos() || !has_cc() {
        eprintln!("SKIP runtime half: not AArch64 macOS or cc unavailable");
        return;
    }

    let dir = make_dir("signed_kept");
    let obj = emit_object(&prepared);

    // (a) Non-overflowing products must NOT trap and must be correct.
    {
        let bin = link(&dir, &obj, true, -9, 8, -72);
        run(&bin).expect("a KEPT signed mul carrier must NOT trap on a non-overflowing product");
    }
    // (a2) Small product near sign boundary: -1 * -1 = 1 (hi=0, sext(lo)=0) — must NOT trap.
    {
        let bin = link(&dir, &obj, true, -1, -1, 1);
        run(&bin).expect("(-1)*(-1)=1 must NOT trap (exact: hi == sext(lo))");
    }

    // (b) i64::MIN * -1 overflows signed (the magnitude is not representable). The kept carrier must
    //     TRAP. SMULH hi = 0, lo = i64::MIN, asr(lo,63) = -1, hi(0) != -1 => correctly flagged.
    {
        let bin = link(&dir, &obj, true, i64::MIN, -1, 0);
        match run(&bin) {
            Err(reason) if reason.starts_with("TRAPPED") => { /* required */ }
            Err(other) => {
                panic!("i64::MIN * -1 on a KEPT signed mul carrier must TRAP, got: {other}")
            }
            Ok(()) => panic!(
                "i64::MIN * -1 on a KEPT signed mul carrier must TRAP, but it returned normally"
            ),
        }
    }
    // (b2) Large * large signed overflow.
    {
        let bin = link(&dir, &obj, true, i64::MAX, 2, 0);
        match run(&bin) {
            Err(reason) if reason.starts_with("TRAPPED") => { /* required */ }
            Err(other) => {
                panic!("i64::MAX * 2 on a KEPT signed mul carrier must TRAP, got: {other}")
            }
            Ok(()) => {
                panic!("i64::MAX * 2 on a KEPT signed mul carrier must TRAP, but returned normally")
            }
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// UNPROVEN (unsigned): the carrier is KEPT. A non-overflowing product is correct/no-trap;
/// `u64::MAX * 2` (the canonical unsigned mul overflow) TRAPS — proving the UMULH/CMP#0 detection.
#[test]
fn unsigned_mul_carrier_pending_reference_traps_on_overflow_and_is_exact() {
    let (func, ctx) = build(Mode::PendingReference, false);
    let prepared = prepare(&func, &ctx);
    assert_eq!(
        brk_count(&prepared),
        1,
        "an unproven unsigned mul carrier must be KEPT (exactly one guard Brk)"
    );

    if !is_aarch64_macos() || !has_cc() {
        eprintln!("SKIP runtime half: not AArch64 macOS or cc unavailable");
        return;
    }

    let dir = make_dir("unsigned_kept");
    let obj = emit_object(&prepared);

    // (a) Non-overflowing: 1000 * 1000 = 1_000_000 — must NOT trap.
    {
        let bin = link(&dir, &obj, false, 1000, 1000, 1_000_000);
        run(&bin).expect("a KEPT unsigned mul carrier must NOT trap on a non-overflowing product");
    }

    // (b) u64::MAX * 2 overflows unsigned (UMULH hi != 0) — must TRAP.
    {
        let bin = link(&dir, &obj, false, u64::MAX as i64, 2, 0);
        match run(&bin) {
            Err(reason) if reason.starts_with("TRAPPED") => { /* required */ }
            Err(other) => {
                panic!("u64::MAX * 2 on a KEPT unsigned mul carrier must TRAP, got: {other}")
            }
            Ok(()) => panic!(
                "u64::MAX * 2 on a KEPT unsigned mul carrier must TRAP, but returned normally"
            ),
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}
