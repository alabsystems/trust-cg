// trust-cg-codegen/tests/jit_ay_simplex_pivot.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ay simplex pivot hot-path JIT smoke test.
//
// Part of #485 — ay consumes Trust Codegen as a JIT backend for its simplex solver
// (see `~/ay/crates/ay-jit/src/simplex_jit.rs` for the i64 fast-path
// analogue). This test targets the f64 pivot-row-normalization step, which
// is what drives the general LP path: given a pointer to a row of doubles
// and a runtime pivot-column index, divide every column by the pivot value
// so that `row[pivot_col] == 1.0` afterwards.
//
// Exercises:
// - FP register-offset load (LdrRO with D-register destination + X-register
//   base + X-register index, packed extend = LSL #3 for 8-byte stride)
// - FP compile-time-offset load/store (LdrRI / StrRI with D-register)
// - FP divide (FdivRR)
// - End-to-end JIT compile + call via extern "C" fn-ptr

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::jit::{JitCompiler, JitConfig};
use trust_cg_ir::function::{MachFunction, Signature, Type};
use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::{D0, D1, FP, LR, SpecialReg, X0, X1, X8, X9};

#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(C)]
struct SparseTerm {
    var: i64,
    coeff: i64,
}

#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(C)]
struct SparsePivotRow {
    terms: [SparseTerm; 4],
    bias: i64,
    checksum: i64,
}

fn build_pivot_normalize_4col() -> MachFunction {
    let sig = Signature::new(vec![Type::Ptr, Type::I64], vec![]);
    let mut func = MachFunction::new("pivot_normalize_4col".to_string(), sig);
    let entry = func.entry;

    // LDR D0, [X0, X1, LSL #3]  — D0 = row[pivot_col]
    let ldr_pv = MachInst::new(
        AArch64Opcode::LdrRO,
        vec![
            MachOperand::PReg(D0),
            MachOperand::PReg(X0),
            MachOperand::PReg(X1),
            MachOperand::Imm(7), // (option=0b011 LSL) << 1 | S=1 -> shift by 3 bits (*8)
        ],
    );
    let id = func.push_inst(ldr_pv);
    func.append_inst(entry, id);

    for j in 0..4i64 {
        let ldr = MachInst::new(
            AArch64Opcode::LdrRI,
            vec![
                MachOperand::PReg(D1),
                MachOperand::PReg(X0),
                MachOperand::Imm(j * 8),
            ],
        );
        let id = func.push_inst(ldr);
        func.append_inst(entry, id);

        let fdiv = MachInst::new(
            AArch64Opcode::FdivRR,
            vec![
                MachOperand::PReg(D1),
                MachOperand::PReg(D1),
                MachOperand::PReg(D0),
            ],
        );
        let id = func.push_inst(fdiv);
        func.append_inst(entry, id);

        let str_ = MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::PReg(D1),
                MachOperand::PReg(X0),
                MachOperand::Imm(j * 8),
            ],
        );
        let id = func.push_inst(str_);
        func.append_inst(entry, id);
    }

    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let id = func.push_inst(ret);
    func.append_inst(entry, id);

    func
}

fn append_inst(func: &mut MachFunction, opcode: AArch64Opcode, operands: Vec<MachOperand>) {
    let id = func.push_inst(MachInst::new(opcode, operands));
    func.append_inst(func.entry, id);
}

fn append_ldr_x(func: &mut MachFunction, dst: trust_cg_ir::regs::PReg, offset: i64) {
    append_inst(
        func,
        AArch64Opcode::LdrRI,
        vec![
            MachOperand::PReg(dst),
            MachOperand::PReg(X0),
            MachOperand::Imm(offset),
        ],
    );
}

fn append_str_x(func: &mut MachFunction, src: trust_cg_ir::regs::PReg, offset: i64) {
    append_inst(
        func,
        AArch64Opcode::StrRI,
        vec![
            MachOperand::PReg(src),
            MachOperand::PReg(X0),
            MachOperand::Imm(offset),
        ],
    );
}

fn build_sparse_pivot_row_update_4term() -> MachFunction {
    let sig = Signature::new(vec![Type::Ptr, Type::I64], vec![Type::I64]);
    let mut func = MachFunction::new("ay_sparse_pivot_row_update_4term".to_string(), sig);

    append_inst(
        &mut func,
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(X9), MachOperand::Imm(0)],
    );

    for coeff_offset in [8, 24, 40, 56] {
        append_ldr_x(&mut func, X8, coeff_offset);
        append_inst(
            &mut func,
            AArch64Opcode::MulRR,
            vec![
                MachOperand::PReg(X8),
                MachOperand::PReg(X8),
                MachOperand::PReg(X1),
            ],
        );
        append_str_x(&mut func, X8, coeff_offset);
        append_inst(
            &mut func,
            AArch64Opcode::AddRR,
            vec![
                MachOperand::PReg(X9),
                MachOperand::PReg(X9),
                MachOperand::PReg(X8),
            ],
        );
    }

    append_ldr_x(&mut func, X8, 64);
    append_inst(
        &mut func,
        AArch64Opcode::AddRR,
        vec![
            MachOperand::PReg(X9),
            MachOperand::PReg(X9),
            MachOperand::PReg(X8),
        ],
    );
    append_str_x(&mut func, X9, 72);
    append_inst(
        &mut func,
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(X0), MachOperand::PReg(X9)],
    );
    append_inst(&mut func, AArch64Opcode::Ret, vec![]);

    func
}

fn build_sparse_pivot_entry() -> MachFunction {
    let sig = Signature::new(vec![Type::Ptr, Type::I64], vec![Type::I64]);
    let mut func = MachFunction::new("ay_sparse_pivot_entry".to_string(), sig);

    append_inst(
        &mut func,
        AArch64Opcode::StpPreIndex,
        vec![
            MachOperand::PReg(FP),
            MachOperand::PReg(LR),
            MachOperand::Special(SpecialReg::SP),
            MachOperand::Imm(-16),
        ],
    );
    append_inst(
        &mut func,
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol(
            "ay_sparse_pivot_row_update_4term".to_string(),
        )],
    );
    append_inst(
        &mut func,
        AArch64Opcode::LdpPostIndex,
        vec![
            MachOperand::PReg(FP),
            MachOperand::PReg(LR),
            MachOperand::Special(SpecialReg::SP),
            MachOperand::Imm(16),
        ],
    );
    append_inst(&mut func, AArch64Opcode::Ret, vec![]);

    func
}

fn host_sparse_pivot_update(row: &mut SparsePivotRow, scale: i64) -> i64 {
    let mut checksum = 0;
    for term in &mut row.terms {
        term.coeff *= scale;
        checksum += term.coeff;
    }
    checksum += row.bias;
    row.checksum = checksum;
    checksum
}

#[test]
fn test_jit_simplex_pivot_normalize_basic() {
    let jit = JitCompiler::new(JitConfig::default());
    let ext: HashMap<String, *const u8> = HashMap::new();
    let buf = jit
        .compile_raw(&[build_pivot_normalize_4col()], &ext)
        .expect("compile_raw should succeed for pivot_normalize_4col");

    let mut row: [f64; 4] = [2.0, 4.0, 8.0, 16.0];
    let pivot_col: i64 = 0;

    let f: unsafe extern "C" fn(*mut f64, i64) = unsafe {
        buf.get_fn_bound::<unsafe extern "C" fn(*mut f64, i64)>("pivot_normalize_4col")
            .expect("should find symbol")
    }
    .into_inner();

    unsafe {
        f(row.as_mut_ptr(), pivot_col);
    }

    assert_eq!(row[0], 1.0);
    assert_eq!(row[1], 2.0);
    assert_eq!(row[2], 4.0);
    assert_eq!(row[3], 8.0);
}

#[test]
fn test_jit_simplex_pivot_normalize_different_pivot_col() {
    let jit = JitCompiler::new(JitConfig::default());
    let ext: HashMap<String, *const u8> = HashMap::new();
    let buf = jit
        .compile_raw(&[build_pivot_normalize_4col()], &ext)
        .expect("compile_raw should succeed for pivot_normalize_4col");

    let mut row: [f64; 4] = [10.0, 5.0, 20.0, 40.0];
    let pivot_col: i64 = 1;

    let f: unsafe extern "C" fn(*mut f64, i64) = unsafe {
        buf.get_fn_bound::<unsafe extern "C" fn(*mut f64, i64)>("pivot_normalize_4col")
            .expect("should find symbol")
    }
    .into_inner();

    unsafe {
        f(row.as_mut_ptr(), pivot_col);
    }

    assert_eq!(row[0], 2.0);
    assert_eq!(row[1], 1.0);
    assert_eq!(row[2], 4.0);
    assert_eq!(row[3], 8.0);
}

#[test]
fn test_jit_simplex_pivot_matches_host_semantics() {
    let jit = JitCompiler::new(JitConfig::default());
    let ext: HashMap<String, *const u8> = HashMap::new();
    let buf = jit
        .compile_raw(&[build_pivot_normalize_4col()], &ext)
        .expect("compile_raw should succeed for pivot_normalize_4col");

    let f: unsafe extern "C" fn(*mut f64, i64) = unsafe {
        buf.get_fn_bound::<unsafe extern "C" fn(*mut f64, i64)>("pivot_normalize_4col")
            .expect("should find symbol")
    }
    .into_inner();

    let mut row: [f64; 4] = [1.0, 3.0, 7.0, 13.0];
    let pivot_col: i64 = 0;
    unsafe {
        f(row.as_mut_ptr(), pivot_col);
    }
    assert_eq!(row, [1.0, 3.0, 7.0, 13.0]);

    let expected: [f64; 4] = [3.0 / 3.0, 9.0 / 3.0, 27.0 / 3.0, 81.0 / 3.0];
    let mut row: [f64; 4] = [3.0, 9.0, 27.0, 81.0];
    let pivot_col: i64 = 0;
    unsafe {
        f(row.as_mut_ptr(), pivot_col);
    }
    assert_eq!(row, expected);
}

#[test]
fn test_jit_ay_sparse_pivot_cross_call_updates_aggregate() {
    let jit = JitCompiler::new(JitConfig::default());
    let ext: HashMap<String, *const u8> = HashMap::new();
    let funcs = vec![
        build_sparse_pivot_entry(),
        build_sparse_pivot_row_update_4term(),
    ];
    let buf = jit
        .compile_raw(&funcs, &ext)
        .expect("compile_raw should succeed for ay sparse pivot cross-call");

    assert!(
        buf.symbol_count() >= 2,
        "JIT buffer should contain both sparse pivot functions"
    );

    let f: unsafe extern "C" fn(*mut SparsePivotRow, i64) -> i64 = unsafe {
        buf.get_fn_bound::<unsafe extern "C" fn(*mut SparsePivotRow, i64) -> i64>(
            "ay_sparse_pivot_entry",
        )
        .expect("should find ay sparse pivot entry symbol")
    }
    .into_inner();

    let cases = [
        (
            SparsePivotRow {
                terms: [
                    SparseTerm { var: 2, coeff: 3 },
                    SparseTerm { var: 5, coeff: -7 },
                    SparseTerm { var: 11, coeff: 13 },
                    SparseTerm { var: 17, coeff: 19 },
                ],
                bias: 23,
                checksum: 0,
            },
            2,
        ),
        (
            SparsePivotRow {
                terms: [
                    SparseTerm { var: 1, coeff: -4 },
                    SparseTerm { var: 4, coeff: 8 },
                    SparseTerm { var: 9, coeff: -12 },
                    SparseTerm { var: 16, coeff: 20 },
                ],
                bias: -5,
                checksum: 99,
            },
            -3,
        ),
    ];

    for (mut row, scale) in cases {
        let mut expected = row;
        let expected_checksum = host_sparse_pivot_update(&mut expected, scale);
        let actual_checksum = unsafe { f(&mut row, scale) };

        assert_eq!(actual_checksum, expected_checksum);
        assert_eq!(row, expected);
    }
}
