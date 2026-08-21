// trust-cg-codegen/tests/xxh3_main_loop_trust_ir.rs - xxh3 main-loop primitive as trust_ir
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
// xxHash-derived algorithm material and constants:
// Copyright (c) 2012-2021 Yann Collet | BSD-2-Clause
// See third_party/vendor/xxhash-LICENSE.
//
// Implements the xxh3 bulk-hashing main loop primitive as trust_ir and verifies
// that Trust Codegen's O2 pipeline compiles it to correct machine code. This is the
// hot path for ty's compiled state fingerprinting (issue #343) — one xxh3
// round per 8-byte chunk of a BFS state label.
//
// Operations used: 64-bit multiply, rotate (as shift+or), XOR, pointer load,
// counted loop with block-parameter-threaded accumulator.
//
// Part of #343 - Inline xxh3 hash as trust_ir for compiled fingerprinting

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::{AArch64Opcode, BlockId, MachFunction, MachOperand, PReg};
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

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

const XXH3_PRIME1: u64 = 0x9E37_79B1_85EB_CA87;
const XXH3_PRIME2: u64 = 0xC2B2_AE3D_27D4_EB4F;

const XXH3_MAIN_LOOP_DRIVER_C: &str = r#"
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

extern uint64_t xxh3_main_loop(uint64_t acc, const void* data, uint64_t nblocks);

int main(int argc, char** argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s <acc_hex> <data_hex>\n", argv[0]); return 1; }
    uint64_t acc = strtoull(argv[1], NULL, 16);
    const char* hex = argv[2];
    size_t hexlen = strlen(hex);
    if (hexlen % 2 != 0) { fprintf(stderr, "bad hex len\n"); return 1; }
    size_t nbytes = hexlen / 2;
    uint8_t* buf = (uint8_t*)malloc(nbytes + 16);
    if (!buf) { return 1; }
    for (size_t i = 0; i < nbytes; i++) {
        unsigned int b;
        sscanf(hex + 2*i, "%02x", &b);
        buf[i] = (uint8_t)b;
    }
    uint64_t nblocks = nbytes / 8;
    uint64_t r = xxh3_main_loop(acc, buf, nblocks);
    printf("%016llx\n", (unsigned long long)r);
    free(buf);
    return 0;
}
"#;

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
    let dir = std::env::temp_dir().join(format!("trust_cg_xxh3_main_loop_{test_name}"));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    dir
}

fn write_object_file(dir: &Path, filename: &str, bytes: &[u8]) -> PathBuf {
    let path = dir.join(filename);
    fs::write(&path, bytes).expect("write object file");
    path
}

fn write_c_driver(dir: &Path, filename: &str, source: &str) -> PathBuf {
    let path = dir.join(filename);
    fs::write(&path, source).expect("write C driver");
    path
}

fn link_with_cc(dir: &Path, driver_c: &Path, obj: &Path, output_name: &str) -> PathBuf {
    let binary = dir.join(output_name);
    let output = Command::new("cc")
        .arg("-o")
        .arg(&binary)
        .arg(driver_c)
        .arg(obj)
        .arg(host_no_pie_flag())
        .output()
        .expect("run cc");
    if !output.status.success() {
        panic!(
            "link failed: {}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    binary
}

fn run_binary_with_args(binary: &Path, args: &[&str]) -> (i32, String) {
    let output = Command::new(binary)
        .args(args)
        .output()
        .expect("run binary");
    (
        output.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&output.stdout).to_string(),
    )
}

fn cleanup(dir: &Path) {
    let _ = fs::remove_dir_all(dir);
}

fn compile_trust_ir(
    trust_ir_func: &trust_ir::Function,
    module: &trust_ir::Module,
    opt_level: OptLevel,
) -> Result<Vec<u8>, String> {
    let (lir_func, _proof) = trust_cg_lower::translate_function(trust_ir_func, module)
        .map_err(|e| format!("adapter: {e}"))?;
    let config = PipelineConfig {
        target_triple: host_aarch64_triple().to_string(),
        opt_level,
        emit_debug: false,
        ..Default::default()
    };
    let pipeline = Pipeline::new(config);
    pipeline
        .compile_function(&lir_func)
        .map_err(|e| format!("pipeline: {e}"))
}

fn prepare_trust_ir(
    trust_ir_func: &trust_ir::Function,
    module: &trust_ir::Module,
    opt_level: OptLevel,
) -> Result<MachFunction, String> {
    let (lir_func, _proof) = trust_cg_lower::translate_function(trust_ir_func, module)
        .map_err(|e| format!("adapter: {e}"))?;
    let config = PipelineConfig {
        target_triple: host_aarch64_triple().to_string(),
        opt_level,
        emit_debug: false,
        ..Default::default()
    };
    let pipeline = Pipeline::new(config);
    pipeline
        .prepare_function(&lir_func)
        .map_err(|e| format!("pipeline: {e}"))
}

fn count_opcode(func: &MachFunction, opcode: AArch64Opcode) -> usize {
    func.insts
        .iter()
        .filter(|inst| inst.opcode == opcode)
        .count()
}

fn count_opcode_with_imm(func: &MachFunction, opcode: AArch64Opcode, imm: i64) -> usize {
    func.insts
        .iter()
        .filter(|inst| {
            inst.opcode == opcode
                && inst
                    .operands
                    .iter()
                    .any(|operand| matches!(operand, MachOperand::Imm(value) if *value == imm))
        })
        .count()
}

fn preg_operand(operand: &MachOperand) -> Option<PReg> {
    match operand {
        MachOperand::PReg(preg) => Some(*preg),
        _ => None,
    }
}

fn defines_preg(inst: &trust_cg_ir::MachInst, preg: PReg) -> bool {
    inst.opcode.produces_value()
        && inst
            .operands
            .first()
            .and_then(preg_operand)
            .is_some_and(|def| def == preg)
}

fn ordered_block_inst_indices(func: &MachFunction) -> Vec<(usize, Vec<usize>)> {
    let block_indices: Vec<usize> = if func.block_order.is_empty() {
        (0..func.blocks.len()).collect()
    } else {
        func.block_order
            .iter()
            .map(|block_id| block_id.0 as usize)
            .collect()
    };

    block_indices
        .into_iter()
        .map(|block_idx| {
            (
                block_idx,
                func.blocks[block_idx]
                    .insts
                    .iter()
                    .map(|inst_id| inst_id.0 as usize)
                    .collect(),
            )
        })
        .collect()
}

fn post_computation_movs_after_add_mul(func: &MachFunction) -> Vec<String> {
    let mut residual = Vec::new();

    for (block_idx, inst_indices) in ordered_block_inst_indices(func) {
        for (pos, &inst_idx) in inst_indices.iter().enumerate() {
            let inst = &func.insts[inst_idx];
            if inst.opcode != AArch64Opcode::MovR {
                continue;
            }

            let Some(dst) = inst.operands.first().and_then(preg_operand) else {
                continue;
            };
            let Some(src) = inst.operands.get(1).and_then(preg_operand) else {
                continue;
            };
            if dst == src {
                continue;
            }

            for &producer_idx in inst_indices[..pos].iter().rev() {
                let producer = &func.insts[producer_idx];
                if !defines_preg(producer, src) {
                    continue;
                }

                if matches!(
                    producer.opcode,
                    AArch64Opcode::AddRR
                        | AArch64Opcode::AddRI
                        | AArch64Opcode::AddRIShift12
                        | AArch64Opcode::MulRR
                ) {
                    residual.push(format!(
                        "block {block_idx}: inst {producer_idx} {:?} defines {:?}; inst {inst_idx} MovR commits {:?} <- {:?}",
                        producer.opcode, src, dst, src
                    ));
                }
                break;
            }
        }
    }

    residual
}

fn assert_valid_macho(bytes: &[u8], ctx: &str) {
    assert!(
        bytes.len() >= 4,
        "{ctx}: object too small ({})",
        bytes.len()
    );
    assert_eq!(
        &bytes[..4],
        &host_object_magic_u32().to_le_bytes(),
        "{ctx}: invalid Mach-O magic"
    );
}

fn hex_encode(data: &[u8]) -> String {
    let mut hex = String::with_capacity(data.len() * 2);
    for byte in data {
        write!(&mut hex, "{byte:02x}").expect("write hex");
    }
    hex
}

fn sample_data(nbytes: usize) -> Vec<u8> {
    (0..nbytes)
        .map(|i| (i as u8).wrapping_mul(17).wrapping_add(3))
        .collect()
}

fn build_xxh3_main_loop() -> (trust_ir::Function, trust_ir::Module) {
    let mut mb = ModuleBuilder::new("xxh3_main_loop_fixture");
    let ty = mb.add_func_type(vec![Ty::I64, Ty::Ptr, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("xxh3_main_loop", ty);

    let entry = fb.create_block();
    let acc = fb.add_block_param(entry, Ty::I64);
    let data = fb.add_block_param(entry, Ty::Ptr);
    let nblocks = fb.add_block_param(entry, Ty::I64);

    let loop_header = fb.create_block();
    let loop_acc = fb.add_block_param(loop_header, Ty::I64);
    let loop_i = fb.add_block_param(loop_header, Ty::I64);

    let loop_body = fb.create_block();

    let exit = fb.create_block();
    let exit_acc = fb.add_block_param(exit, Ty::I64);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I64, 0);
    fb.br(loop_header, vec![acc, zero]);

    fb.switch_to_block(loop_header);
    let cond = fb.icmp(ICmpOp::Slt, Ty::I64, loop_i, nblocks);
    fb.condbr(cond, loop_body, vec![], exit, vec![loop_acc]);

    fb.switch_to_block(loop_body);
    let eight = fb.iconst(Ty::I64, 8);
    let byte_offset = fb.mul(Ty::I64, loop_i, eight);
    let block_ptr = fb.gep(Ty::I8, data, vec![byte_offset]);
    let block_val = fb.load(Ty::I64, block_ptr);
    let prime1 = fb.iconst(Ty::I64, XXH3_PRIME1 as i128);
    let mixed = fb.mul(Ty::I64, block_val, prime1);
    let tmp = fb.binop(BinOp::Xor, Ty::I64, loop_acc, mixed);
    let shl_amt = fb.iconst(Ty::I64, 31);
    let shr_amt = fb.iconst(Ty::I64, 33);
    let tmp_shl = fb.binop(BinOp::Shl, Ty::I64, tmp, shl_amt);
    let tmp_lshr = fb.binop(BinOp::LShr, Ty::I64, tmp, shr_amt);
    let rotated = fb.binop(BinOp::Or, Ty::I64, tmp_shl, tmp_lshr);
    let prime2 = fb.iconst(Ty::I64, XXH3_PRIME2 as i128);
    let next_acc = fb.mul(Ty::I64, rotated, prime2);
    let one = fb.iconst(Ty::I64, 1);
    let next_i = fb.add(Ty::I64, loop_i, one);
    fb.br(loop_header, vec![next_acc, next_i]);

    fb.switch_to_block(exit);
    fb.ret(vec![exit_acc]);

    fb.build();
    let module = mb.build();
    let func = module
        .functions
        .iter()
        .find(|f| f.name == "xxh3_main_loop")
        .expect("xxh3_main_loop function")
        .clone();
    (func, module)
}

fn xxh3_main_loop_ref(initial_acc: u64, data: &[u8]) -> u64 {
    let mut acc = initial_acc;
    let nblocks = data.len() / 8;
    for i in 0..nblocks {
        let off = i * 8;
        let block = u64::from_le_bytes(data[off..off + 8].try_into().unwrap());
        let tmp = acc ^ block.wrapping_mul(XXH3_PRIME1);
        acc = tmp.rotate_left(31).wrapping_mul(XXH3_PRIME2);
    }
    acc
}

fn run_xxh3_main_loop_case(test_name: &str, initial_acc: u64, data: &[u8]) {
    let dir = make_test_dir(test_name);
    let (func, module) = build_xxh3_main_loop();
    let obj_bytes = compile_trust_ir(&func, &module, OptLevel::O2).expect("O2 compile");
    assert_valid_macho(&obj_bytes, test_name);
    let obj_path = write_object_file(&dir, "xxh3_main_loop.o", &obj_bytes);
    let driver_path = write_c_driver(&dir, "driver.c", XXH3_MAIN_LOOP_DRIVER_C);
    let binary = link_with_cc(&dir, &driver_path, &obj_path, "xxh3_main_loop_test");
    let acc_hex = format!("{initial_acc:016x}");
    let data_hex = hex_encode(data);
    let (exit_code, stdout) = run_binary_with_args(&binary, &[&acc_hex, &data_hex]);
    assert_eq!(
        exit_code, 0,
        "{test_name}: binary failed with stdout {stdout:?}"
    );
    let expected_stdout = format!("{:016x}\n", xxh3_main_loop_ref(initial_acc, data));
    assert_eq!(stdout, expected_stdout, "{test_name}: output mismatch");
    cleanup(&dir);
}

#[test]
fn test_xxh3_main_loop_ref_deterministic() {
    let initial_acc = 0x0123_4567_89AB_CDEF;
    let data = sample_data(64);
    assert_eq!(
        xxh3_main_loop_ref(initial_acc, &data),
        xxh3_main_loop_ref(initial_acc, &data)
    );
}

#[test]
fn test_xxh3_main_loop_ref_sensitive() {
    let initial_acc = 0x0123_4567_89AB_CDEF;
    let data_a = sample_data(32);
    let mut data_b = data_a.clone();
    data_b[15] ^= 0x5A;
    assert_ne!(
        xxh3_main_loop_ref(initial_acc, &data_a),
        xxh3_main_loop_ref(initial_acc, &data_b)
    );
}

#[test]
fn test_xxh3_main_loop_compiles_o0() {
    let (func, module) = build_xxh3_main_loop();
    let obj_bytes = compile_trust_ir(&func, &module, OptLevel::O0).expect("O0 compile");
    assert_valid_macho(&obj_bytes, "xxh3_main_loop O0");
    assert!(obj_bytes.len() > 100, "O0 object should be substantial");
}

#[test]
fn test_xxh3_main_loop_compiles_o2() {
    let (func, module) = build_xxh3_main_loop();
    let obj_bytes = compile_trust_ir(&func, &module, OptLevel::O2).expect("O2 compile");
    assert_valid_macho(&obj_bytes, "xxh3_main_loop O2");
    assert!(obj_bytes.len() > 100, "O2 object should be substantial");
}

#[test]
fn test_xxh3_main_loop_o2_uses_native_ror_for_rotate() {
    let (func, module) = build_xxh3_main_loop();
    let prepared = prepare_trust_ir(&func, &module, OptLevel::O2).expect("O2 prepare");

    assert_eq!(
        count_opcode_with_imm(&prepared, AArch64Opcode::RorRI, 33),
        1,
        "rotate-left-by-31 should lower to one ROR #33"
    );
    assert_eq!(
        count_opcode_with_imm(&prepared, AArch64Opcode::LslRI, 31),
        0,
        "rotate idiom should not leave LSL #31 in O2 code"
    );
    assert_eq!(
        count_opcode_with_imm(&prepared, AArch64Opcode::LsrRI, 33),
        0,
        "rotate idiom should not leave LSR #33 in O2 code"
    );
    assert_eq!(
        count_opcode(&prepared, AArch64Opcode::OrrRR),
        0,
        "rotate idiom should not be glued back together with ORR"
    );
}

#[test]
fn test_xxh3_main_loop_o2_coalesces_post_computation_movs() {
    let (func, module) = build_xxh3_main_loop();
    let prepared = prepare_trust_ir(&func, &module, OptLevel::O2).expect("O2 prepare");

    assert!(
        count_opcode(&prepared, AArch64Opcode::MulRR) >= 2,
        "fixture should still contain the xxh3 block and rotate multiplies"
    );
    let add_computations = count_opcode(&prepared, AArch64Opcode::AddRR)
        + count_opcode(&prepared, AArch64Opcode::AddRI)
        + count_opcode(&prepared, AArch64Opcode::AddRIShift12);
    assert!(
        add_computations >= 1,
        "fixture should still contain the loop index increment as a register or immediate add"
    );

    let residual = post_computation_movs_after_add_mul(&prepared);
    assert!(
        residual.is_empty(),
        "O2 should coalesce post-computation MovR commits after register/immediate adds and MulRR:\n{}",
        residual.join("\n")
    );
}

#[test]
fn test_xxh3_main_loop_o2_uses_latch_conditional_backedge() {
    let (func, module) = build_xxh3_main_loop();
    let prepared = prepare_trust_ir(&func, &module, OptLevel::O2).expect("O2 prepare");

    assert_eq!(
        count_opcode(&prepared, AArch64Opcode::CSet),
        0,
        "O2 counted-loop guard/latch should not materialize the loop predicate"
    );
    assert_eq!(
        count_opcode(&prepared, AArch64Opcode::Cbnz),
        0,
        "O2 counted-loop guard/latch should use B.cond instead of CBNZ on a CSET result"
    );

    let ordered_blocks: Vec<BlockId> = if prepared.block_order.is_empty() {
        (0..prepared.blocks.len())
            .map(|block_idx| BlockId(block_idx as u32))
            .collect()
    } else {
        prepared.block_order.clone()
    };
    let (body_pos, body_block) = ordered_blocks
        .iter()
        .enumerate()
        .find(|(_, block_id)| {
            let block_id = **block_id;
            prepared
                .block(block_id)
                .insts
                .iter()
                .any(|&inst_id| prepared.inst(inst_id).opcode == AArch64Opcode::RorRI)
        })
        .map(|(pos, block_id)| (pos, *block_id))
        .expect("expected to identify the xxh3 loop body");

    let body_opcodes: Vec<AArch64Opcode> = prepared
        .block(body_block)
        .insts
        .iter()
        .map(|&inst_id| prepared.inst(inst_id).opcode)
        .collect();
    // The body's only successor is the split latch, which is laid out
    // IMMEDIATELY next — so the historical trailing `B latch` is a taken
    // branch to the very next instruction, and the layout-independent
    // branch-to-next elision (`layout::aarch64_elide_branch_to_next`) now
    // deletes it: the body FALLS THROUGH into the latch. Pin that: no
    // unconditional B, and no branch of any kind, terminates the body.
    assert!(
        !matches!(
            body_opcodes.last(),
            Some(&AArch64Opcode::B) | Some(&AArch64Opcode::BCond)
        ),
        "xxh3 loop body should fall through into the layout-next split latch \
         (redundant `b latch` elided), got {body_opcodes:?}"
    );

    let latch_block = *ordered_blocks
        .get(body_pos + 1)
        .expect("split latch should immediately follow the loop body");
    let latch_opcodes: Vec<AArch64Opcode> = prepared
        .block(latch_block)
        .insts
        .iter()
        .map(|&inst_id| prepared.inst(inst_id).opcode)
        .collect();
    // Regalloc-level copy coalescing (CoalesceTuning::aarch64) now merges the
    // hardened `AddRI dst, src, #0` carrier-commit guard copies into in-place
    // body updates whenever the carrier's live range permits, so the split
    // latch should carry NO commit copies at all for this kernel — only the
    // cloned compare and the conditional backedge. (Historically this asserted
    // `contains AddRI`: the commits existed as guard copies in the latch.)
    assert!(
        !latch_opcodes.contains(&AArch64Opcode::AddRI),
        "split latch commit copies should be coalesced into in-place body \
         updates, got {latch_opcodes:?}"
    );
    assert!(
        latch_opcodes
            .iter()
            .any(|opcode| matches!(opcode, AArch64Opcode::CmpRR | AArch64Opcode::CmpRI)),
        "split latch should clone the counted-loop compare after carrier commits"
    );
    assert_eq!(
        latch_opcodes.last(),
        Some(&AArch64Opcode::BCond),
        "split latch should end with the conditional backedge"
    );

    let latch_branch_id = prepared
        .block(latch_block)
        .insts
        .last()
        .copied()
        .expect("split latch branch");
    let latch_branch_target = prepared
        .inst(latch_branch_id)
        .operands
        .iter()
        .rev()
        .find_map(|operand| match operand {
            MachOperand::Imm(value) => Some(*value),
            _ => None,
        })
        .expect("resolved latch branch target offset");
    assert!(
        latch_branch_target < 0,
        "split latch conditional branch should run the steady-state path backward"
    );

    let exit_fallthrough = *ordered_blocks
        .get(body_pos + 2)
        .expect("loop exit path should immediately follow the split latch");
    let fallthrough_reaches_exit = |mut block_id: BlockId| {
        for _ in 0..prepared.blocks.len() {
            let block = prepared.block(block_id);
            let opcodes: Vec<AArch64Opcode> = block
                .insts
                .iter()
                .map(|&inst_id| prepared.inst(inst_id).opcode)
                .collect();
            if opcodes.contains(&AArch64Opcode::Ret) {
                return true;
            }
            if opcodes == [AArch64Opcode::B] && block.succs.len() == 1 {
                block_id = block.succs[0];
                continue;
            }
            return false;
        }
        false
    };
    assert!(
        fallthrough_reaches_exit(exit_fallthrough),
        "split latch fallthrough should reach the loop exit"
    );
}

#[test]
fn test_xxh3_main_loop_o2_differs_from_o0() {
    let (func, module) = build_xxh3_main_loop();
    let obj_o0 = compile_trust_ir(&func, &module, OptLevel::O0).expect("O0 compile");
    let obj_o2 = compile_trust_ir(&func, &module, OptLevel::O2).expect("O2 compile");
    assert_ne!(obj_o0, obj_o2, "O2 output should differ from O0");
}

#[test]
fn test_xxh3_main_loop_determinism_o2() {
    let (func, module) = build_xxh3_main_loop();
    let obj_a = compile_trust_ir(&func, &module, OptLevel::O2).expect("O2 compile A");
    let obj_b = compile_trust_ir(&func, &module, OptLevel::O2).expect("O2 compile B");
    assert_eq!(obj_a, obj_b, "O2 output must be byte-identical");
}

#[test]
fn test_xxh3_main_loop_e2e_single_block() {
    if !is_aarch64() || !has_cc() {
        return;
    }
    run_xxh3_main_loop_case("single_block", 0x243F_6A88_85A3_08D3, &sample_data(8));
}

#[test]
fn test_xxh3_main_loop_e2e_four_blocks() {
    if !is_aarch64() || !has_cc() {
        return;
    }
    run_xxh3_main_loop_case("four_blocks", 0x1319_8A2E_0370_7344, &sample_data(32));
}

#[test]
fn test_xxh3_main_loop_e2e_sixteen_blocks() {
    if !is_aarch64() || !has_cc() {
        return;
    }
    run_xxh3_main_loop_case("sixteen_blocks", 0xA409_3822_299F_31D0, &sample_data(128));
}

#[test]
fn test_xxh3_main_loop_e2e_zero_blocks() {
    if !is_aarch64() || !has_cc() {
        return;
    }
    run_xxh3_main_loop_case("zero_blocks", 0x082E_FA98_EC4E_6C89, &[]);
}
