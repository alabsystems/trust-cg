// trust-cg-codegen/tests/xxh3_medium_long_trust_ir.rs - focused xxh3 medium/>128 trust_ir coverage
//
// Test harness: Copyright 2026 Andrew Yates | Apache-2.0
// xxHash-derived algorithm material, constants, default secret, and vectors:
// Copyright (c) 2012-2021 Yann Collet | BSD-2-Clause
// See third_party/vendor/xxhash-LICENSE.
//
// Part of #654 - Add medium/long-input trust_ir coverage for compiled fingerprinting.

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{BinOp, Inst, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

const XXH_PRIME64_1: u64 = 0x9E37_79B1_85EB_CA87;
const PRIME_MX1: u64 = 0x1656_6791_9E37_79F9;
const MASK32: u64 = 0xFFFF_FFFF;
const XXH3_SECRET_SIZE_MIN: usize = 136;
const XXH3_MIDSIZE_STARTOFFSET: usize = 3;
const XXH3_MIDSIZE_LASTOFFSET: usize = 17;

const MEDIUM32_EXPECTED: u64 = 0x8320_1AC8_C869_7F03;
const LONG160_EXPECTED: u64 = 0x7BA0_86C0_C1E5_0E6B;

/// xxh3 default secret from xxHash v0.8.2.
const XXH3_SECRET: [u8; 192] = [
    0xb8, 0xfe, 0x6c, 0x39, 0x23, 0xa4, 0x4b, 0xbe, 0x7c, 0x01, 0x81, 0x2c, 0xf7, 0x21, 0xad, 0x1c,
    0xde, 0xd4, 0x6d, 0xe9, 0x83, 0x90, 0x97, 0xdb, 0x72, 0x40, 0xa4, 0xa4, 0xb7, 0xb3, 0x67, 0x1f,
    0xcb, 0x79, 0xe6, 0x4e, 0xcc, 0xc0, 0xe5, 0x78, 0x82, 0x5a, 0xd0, 0x7d, 0xcc, 0xff, 0x72, 0x21,
    0xb8, 0x08, 0x46, 0x74, 0xf7, 0x43, 0x24, 0x8e, 0xe0, 0x35, 0x90, 0xe6, 0x81, 0x3a, 0x26, 0x4c,
    0x3c, 0x28, 0x52, 0xbb, 0x91, 0xc3, 0x00, 0xcb, 0x88, 0xd0, 0x65, 0x8b, 0x1b, 0x53, 0x2e, 0xa3,
    0x71, 0x64, 0x48, 0x97, 0xa2, 0x0d, 0xf9, 0x4e, 0x38, 0x19, 0xef, 0x46, 0xa9, 0xde, 0xac, 0xd8,
    0xa8, 0xfa, 0x76, 0x3f, 0xe3, 0x9c, 0x34, 0x3f, 0xf9, 0xdc, 0xbb, 0xc7, 0xc7, 0x0b, 0x4f, 0x1d,
    0x8a, 0x51, 0xe0, 0x4b, 0xcd, 0xb4, 0x59, 0x31, 0xc8, 0x9f, 0x7e, 0xc9, 0xd9, 0x78, 0x73, 0x64,
    0xea, 0xc5, 0xac, 0x83, 0x34, 0xd3, 0xeb, 0xc3, 0xc5, 0x81, 0xa0, 0xff, 0xfa, 0x13, 0x63, 0xeb,
    0x17, 0x0d, 0xdd, 0x51, 0xb7, 0xf0, 0xda, 0x49, 0xd3, 0x16, 0x55, 0x26, 0x29, 0xd4, 0x68, 0x9e,
    0x2b, 0x16, 0xbe, 0x58, 0x7d, 0x47, 0xa1, 0xfc, 0x8f, 0xf8, 0xb8, 0xd1, 0x7a, 0xd0, 0x31, 0xce,
    0x45, 0xcb, 0x3a, 0x8f, 0x95, 0x16, 0x04, 0x28, 0xaf, 0xd7, 0xfb, 0xca, 0xbb, 0x4b, 0x40, 0x7e,
];

const C_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>

extern uint64_t xxh3_64_medium32(const void* data);
extern uint64_t xxh3_64_len160(const void* data);

static void fill(uint8_t* buf, unsigned long n, uint8_t salt) {
    for (unsigned long i = 0; i < n; i++) {
        buf[i] = (uint8_t)((i * 37u + salt + (i >> 1)) & 0xffu);
    }
}

int main(void) {
    uint8_t medium[32];
    uint8_t long_input[160];
    fill(medium, sizeof(medium), 0x11);
    fill(long_input, sizeof(long_input), 0x5a);

    printf("%016llx\n", (unsigned long long)xxh3_64_medium32(medium));
    printf("%016llx\n", (unsigned long long)xxh3_64_len160(long_input));
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
    let dir = std::env::temp_dir().join(format!("trust_cg_xxh3_medium_long_{test_name}"));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    dir
}

fn cleanup(dir: &Path) {
    let _ = fs::remove_dir_all(dir);
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
        .arg("-Wl,-no_pie")
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

fn run_binary(binary: &Path) -> (i32, String) {
    let output = Command::new(binary).output().expect("run binary");
    (
        output.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&output.stdout).to_string(),
    )
}

fn compile_module(module: &trust_ir::Module, opt_level: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level,
        parallel: false,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("compile xxh3 medium/long module");
    assert!(
        !result.object_code.is_empty(),
        "compiled object must be non-empty"
    );
    result.object_code
}

fn assert_valid_macho(bytes: &[u8], ctx: &str) {
    assert!(
        bytes.len() >= 4,
        "{ctx}: object too small ({})",
        bytes.len()
    );
    assert_eq!(
        &bytes[..4],
        &[0xCF, 0xFA, 0xED, 0xFE],
        "{ctx}: invalid Mach-O magic"
    );
}

fn secret_u64(offset: usize) -> u64 {
    u64::from_le_bytes(XXH3_SECRET[offset..offset + 8].try_into().unwrap())
}

fn read_u64(data: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(data[offset..offset + 8].try_into().unwrap())
}

fn sample_data(nbytes: usize, salt: u8) -> Vec<u8> {
    (0..nbytes)
        .map(|i| {
            (i as u8)
                .wrapping_mul(37)
                .wrapping_add(salt)
                .wrapping_add((i >> 1) as u8)
        })
        .collect()
}

fn xxh3_avalanche_ref(mut h: u64) -> u64 {
    h ^= h >> 37;
    h = h.wrapping_mul(PRIME_MX1);
    h ^= h >> 32;
    h
}

fn mul128_fold64_ref(lhs: u64, rhs: u64) -> u64 {
    let product = (lhs as u128).wrapping_mul(rhs as u128);
    (product as u64) ^ ((product >> 64) as u64)
}

fn xxh3_mix16b_ref(data: &[u8], data_offset: usize, secret_offset: usize) -> u64 {
    let input_lo = read_u64(data, data_offset);
    let input_hi = read_u64(data, data_offset + 8);
    mul128_fold64_ref(
        input_lo ^ secret_u64(secret_offset),
        input_hi ^ secret_u64(secret_offset + 8),
    )
}

fn xxh3_len32_ref(data: &[u8]) -> u64 {
    assert_eq!(data.len(), 32);
    let mut acc = (data.len() as u64).wrapping_mul(XXH_PRIME64_1);
    acc = acc.wrapping_add(xxh3_mix16b_ref(data, 0, 0));
    acc = acc.wrapping_add(xxh3_mix16b_ref(data, 16, 16));
    xxh3_avalanche_ref(acc)
}

fn xxh3_len160_ref(data: &[u8]) -> u64 {
    assert_eq!(data.len(), 160);
    let mut acc = (data.len() as u64).wrapping_mul(XXH_PRIME64_1);
    for i in 0..8 {
        acc = acc.wrapping_add(xxh3_mix16b_ref(data, 16 * i, 16 * i));
    }

    let mut acc_end = xxh3_mix16b_ref(
        data,
        data.len() - 16,
        XXH3_SECRET_SIZE_MIN - XXH3_MIDSIZE_LASTOFFSET,
    );
    acc = xxh3_avalanche_ref(acc);

    let nb_rounds = data.len() / 16;
    for i in 8..nb_rounds {
        acc_end = acc_end.wrapping_add(xxh3_mix16b_ref(
            data,
            16 * i,
            16 * (i - 8) + XXH3_MIDSIZE_STARTOFFSET,
        ));
    }

    xxh3_avalanche_ref(acc.wrapping_add(acc_end))
}

fn c64(fb: &mut FunctionBuilder<'_>, value: u64) -> ValueId {
    fb.iconst(Ty::I64, value as i128)
}

fn xor64(fb: &mut FunctionBuilder<'_>, lhs: ValueId, rhs: ValueId) -> ValueId {
    fb.binop(BinOp::Xor, Ty::I64, lhs, rhs)
}

fn and64(fb: &mut FunctionBuilder<'_>, lhs: ValueId, rhs: ValueId) -> ValueId {
    fb.binop(BinOp::And, Ty::I64, lhs, rhs)
}

fn lshr64(fb: &mut FunctionBuilder<'_>, lhs: ValueId, rhs: ValueId) -> ValueId {
    fb.binop(BinOp::LShr, Ty::I64, lhs, rhs)
}

fn load64_at(fb: &mut FunctionBuilder<'_>, base: ValueId, offset: usize) -> ValueId {
    let offset = c64(fb, offset as u64);
    let ptr = fb.gep(Ty::I8, base, vec![offset]);
    fb.load(Ty::I64, ptr)
}

fn emit_xxh3_avalanche(fb: &mut FunctionBuilder<'_>, h: ValueId) -> ValueId {
    let c37 = c64(fb, 37);
    let h_shr37 = lshr64(fb, h, c37);
    let h1 = xor64(fb, h, h_shr37);

    let prime = c64(fb, PRIME_MX1);
    let h2 = fb.mul(Ty::I64, h1, prime);

    let c32 = c64(fb, 32);
    let h_shr32 = lshr64(fb, h2, c32);
    xor64(fb, h2, h_shr32)
}

fn emit_mul128_fold64(fb: &mut FunctionBuilder<'_>, lhs: ValueId, rhs: ValueId) -> ValueId {
    let mask = c64(fb, MASK32);
    let c32 = c64(fb, 32);

    let lhs_lo = and64(fb, lhs, mask);
    let lhs_hi = lshr64(fb, lhs, c32);
    let rhs_lo = and64(fb, rhs, mask);
    let rhs_hi = lshr64(fb, rhs, c32);

    let lo_lo = fb.mul(Ty::I64, lhs_lo, rhs_lo);
    let lo_hi = fb.mul(Ty::I64, lhs_lo, rhs_hi);
    let hi_lo = fb.mul(Ty::I64, lhs_hi, rhs_lo);
    let hi_hi = fb.mul(Ty::I64, lhs_hi, rhs_hi);

    let low = fb.mul(Ty::I64, lhs, rhs);
    let lo_lo_hi = lshr64(fb, lo_lo, c32);
    let lo_hi_low = and64(fb, lo_hi, mask);
    let hi_lo_low = and64(fb, hi_lo, mask);
    let middle_a = fb.add(Ty::I64, lo_lo_hi, lo_hi_low);
    let middle = fb.add(Ty::I64, middle_a, hi_lo_low);
    let carry = lshr64(fb, middle, c32);

    let lo_hi_hi = lshr64(fb, lo_hi, c32);
    let hi_lo_hi = lshr64(fb, hi_lo, c32);
    let high_a = fb.add(Ty::I64, hi_hi, lo_hi_hi);
    let high_b = fb.add(Ty::I64, high_a, hi_lo_hi);
    let high = fb.add(Ty::I64, high_b, carry);

    xor64(fb, low, high)
}

fn emit_mix16b(
    fb: &mut FunctionBuilder<'_>,
    data: ValueId,
    data_offset: usize,
    secret_offset: usize,
) -> ValueId {
    let input_lo = load64_at(fb, data, data_offset);
    let input_hi = load64_at(fb, data, data_offset + 8);
    let secret_lo = c64(fb, secret_u64(secret_offset));
    let secret_hi = c64(fb, secret_u64(secret_offset + 8));
    let lhs = xor64(fb, input_lo, secret_lo);
    let rhs = xor64(fb, input_hi, secret_hi);
    emit_mul128_fold64(fb, lhs, rhs)
}

fn emit_xxh3_len32(fb: &mut FunctionBuilder<'_>, data: ValueId) -> ValueId {
    let len = c64(fb, 32);
    let prime = c64(fb, XXH_PRIME64_1);
    let acc0 = fb.mul(Ty::I64, len, prime);
    let mix0 = emit_mix16b(fb, data, 0, 0);
    let acc1 = fb.add(Ty::I64, acc0, mix0);
    let mix1 = emit_mix16b(fb, data, 16, 16);
    let acc2 = fb.add(Ty::I64, acc1, mix1);
    emit_xxh3_avalanche(fb, acc2)
}

fn emit_xxh3_len160(fb: &mut FunctionBuilder<'_>, data: ValueId) -> ValueId {
    let len = c64(fb, 160);
    let prime = c64(fb, XXH_PRIME64_1);
    let mut acc = fb.mul(Ty::I64, len, prime);
    for i in 0..8 {
        let mix = emit_mix16b(fb, data, 16 * i, 16 * i);
        acc = fb.add(Ty::I64, acc, mix);
    }

    let mut acc_end = emit_mix16b(
        fb,
        data,
        160 - 16,
        XXH3_SECRET_SIZE_MIN - XXH3_MIDSIZE_LASTOFFSET,
    );
    acc = emit_xxh3_avalanche(fb, acc);

    for i in 8..10 {
        let mix = emit_mix16b(fb, data, 16 * i, 16 * (i - 8) + XXH3_MIDSIZE_STARTOFFSET);
        acc_end = fb.add(Ty::I64, acc_end, mix);
    }

    let acc_all = fb.add(Ty::I64, acc, acc_end);
    emit_xxh3_avalanche(fb, acc_all)
}

fn build_xxh3_medium_long_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("xxh3_medium_long_fixture");
    let ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);

    {
        let mut fb = mb.function("xxh3_64_medium32", ty);
        let entry = fb.create_block();
        let data = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        let result = emit_xxh3_len32(&mut fb, data);
        fb.ret(vec![result]);
        fb.build();
    }

    {
        let mut fb = mb.function("xxh3_64_len160", ty);
        let entry = fb.create_block();
        let data = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        let result = emit_xxh3_len160(&mut fb, data);
        fb.ret(vec![result]);
        fb.build();
    }

    mb.build()
}

fn assert_no_trust_ir_calls(module: &trust_ir::Module) {
    for func in &module.functions {
        for block in &func.blocks {
            for node in &block.body {
                assert!(
                    !matches!(node.inst, Inst::Call { .. }),
                    "{} contains an extern/helper call",
                    func.name
                );
            }
        }
    }
}

fn hex_lines(values: &[u64]) -> String {
    let mut out = String::new();
    for value in values {
        writeln!(&mut out, "{value:016x}").expect("write hex line");
    }
    out
}

fn run_e2e_case(opt_level: OptLevel, test_name: &str) {
    let medium = sample_data(32, 0x11);
    let long_input = sample_data(160, 0x5a);
    let expected = hex_lines(&[xxh3_len32_ref(&medium), xxh3_len160_ref(&long_input)]);

    let module = build_xxh3_medium_long_module();
    assert_no_trust_ir_calls(&module);
    let obj_bytes = compile_module(&module, opt_level);
    assert_valid_macho(&obj_bytes, test_name);

    let dir = make_test_dir(test_name);
    let obj_path = write_object_file(&dir, "xxh3_medium_long.o", &obj_bytes);
    let driver_path = write_c_driver(&dir, "driver.c", C_DRIVER);
    let binary = link_with_cc(&dir, &driver_path, &obj_path, "xxh3_medium_long_test");
    let (exit_code, stdout) = run_binary(&binary);
    assert_eq!(exit_code, 0, "{test_name}: binary failed with {stdout:?}");
    assert_eq!(stdout, expected, "{test_name}: stdout mismatch");
    cleanup(&dir);
}

#[test]
fn test_xxh3_medium_long_reference_vectors() {
    let medium = sample_data(32, 0x11);
    let long_input = sample_data(160, 0x5a);

    assert_eq!(xxh3_len32_ref(&medium), MEDIUM32_EXPECTED);
    assert_eq!(xxh3_len160_ref(&long_input), LONG160_EXPECTED);
}

#[test]
fn test_xxh3_medium_long_compiles_o0_o2() {
    let module = build_xxh3_medium_long_module();
    assert_no_trust_ir_calls(&module);

    let obj_o0 = compile_module(&module, OptLevel::O0);
    assert_valid_macho(&obj_o0, "xxh3 medium/long O0");

    let obj_o2 = compile_module(&module, OptLevel::O2);
    assert_valid_macho(&obj_o2, "xxh3 medium/long O2");
}

#[test]
fn test_xxh3_medium_long_e2e_o0_o2() {
    if !is_aarch64() || !has_cc() {
        return;
    }

    run_e2e_case(OptLevel::O0, "o0");
    run_e2e_case(OptLevel::O2, "o2");
}
