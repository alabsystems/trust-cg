// trust-cg-codegen/tests/aarch64_v4i32_vector_shift.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! End-to-end AArch64 lowering of lane-wise `<4 x i32>` shifts.
//!
//! A *uniform-constant* lane-wise shift (`BinOp::{Shl,LShr,AShr}` whose RHS is a
//! `pack_lanes` of one constant) lowers to a single NEON SIMD shift-by-immediate
//! `SHL/USHR/SSHR.4S`, whose semantics are SMT-verified by
//! `proof_vector_{shl,ushr,sshr}_4s` and whose binary encoding is checked
//! against the system assembler in `aarch64/encoding_neon.rs`.
//!
//! These tests drive the *whole* AArch64 pipeline (adapter -> isel -> regalloc
//! -> frame -> encode) and assert the verified instruction word lands in the
//! emitted machine code. Variable/non-uniform shifts additionally exercise
//! result flow structurally and compare linked native execution against a C
//! reference over edge-case lane values and shift counts.

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_cg_ir::regs::RegClass;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::isel::{AArch64Opcode, ISelFunction, ISelOperand, InstructionSelector};
use trust_ir::BinOp;
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, FuncTyId,
    Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, Ty as TrustIrTy,
    ValueId,
};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn v4i32_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::I32), 4)
}

/// Add `fn name(src: *v4i32, counts: *v4i32, out: *v4i32)`.
fn add_variable_shift_function(module: &mut TrustIrModule, func_id: u32, name: &str, op: BinOp) {
    let v4i32 = v4i32_ty();
    let ft = FuncTy {
        params: vec![TrustIrTy::Ptr, TrustIrTy::Ptr, TrustIrTy::Ptr],
        returns: vec![],
        is_vararg: false,
    };
    let ft_id: FuncTyId = module.add_func_type(ft);
    let mut func = TrustIrFunction::new(FuncId::new(func_id), name, ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (v(0), TrustIrTy::Ptr),
            (v(1), TrustIrTy::Ptr),
            (v(2), TrustIrTy::Ptr),
        ],
        body: vec![
            InstrNode::new(Inst::Load {
                ty: v4i32.clone(),
                ptr: v(0),
                align: None,
                volatile: false,
            })
            .with_result(v(10)),
            InstrNode::new(Inst::Load {
                ty: v4i32.clone(),
                ptr: v(1),
                align: None,
                volatile: false,
            })
            .with_result(v(11)),
            InstrNode::new(Inst::BinOp {
                op,
                ty: v4i32.clone(),
                lhs: v(10),
                rhs: v(11),
            })
            .with_result(v(12)),
            InstrNode::new(Inst::Store {
                ty: v4i32,
                ptr: v(2),
                value: v(12),
                align: None,
                volatile: false,
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module.add_function(func);
}

fn build_variable_shift_module(name: &str, op: BinOp) -> TrustIrModule {
    let mut module = TrustIrModule::new(format!("{name}_module"));
    add_variable_shift_function(&mut module, 0, name, op);
    module
}

fn select_aarch64(module: &TrustIrModule) -> ISelFunction {
    let func = module
        .functions
        .first()
        .expect("variable-shift module has one function");
    let (lir_func, _) =
        trust_cg_lower::translate_function(func, module).expect("adapter must lower shift module");
    let mut isel = InstructionSelector::new(lir_func.name.clone(), lir_func.signature.clone());
    isel.seed_value_types(&lir_func.value_types);
    isel.lower_formal_arguments(&lir_func.signature, lir_func.entry_block)
        .expect("formal arguments must lower");

    let mut block_order: Vec<Block> = lir_func.blocks.keys().copied().collect();
    block_order.sort_by_key(|block| {
        if *block == lir_func.entry_block {
            0
        } else {
            block.0 + 1
        }
    });
    for block in block_order {
        let lir_block = &lir_func.blocks[&block];
        isel.select_block_with_source_locs(block, &lir_block.instructions, &lir_block.source_locs)
            .expect("variable packed shift must select");
    }
    isel.finalize()
}

/// Build `fn shift(p_in: *v4i32, p_out: *v4i32) { *p_out = (*p_in) OP <count;4>; }`.
fn build_uniform_const_shift_module(name: &str, op: BinOp, count: i128) -> TrustIrModule {
    let v4i32 = v4i32_ty();
    let mut module = TrustIrModule::new(format!("{name}_module"));
    let ft = FuncTy {
        params: vec![TrustIrTy::Ptr, TrustIrTy::Ptr],
        returns: vec![],
        is_vararg: false,
    };
    let ft_id: FuncTyId = module.add_func_type(ft);
    let mut func = TrustIrFunction::new(FuncId::new(0), name, ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(v(0), TrustIrTy::Ptr), (v(1), TrustIrTy::Ptr)],
        body: vec![
            InstrNode::new(Inst::Load {
                ty: v4i32.clone(),
                ptr: v(0),
                align: None,
                volatile: false,
            })
            .with_result(v(10)),
            InstrNode::new(Inst::Const {
                ty: TrustIrTy::I32,
                value: Constant::Int(count),
            })
            .with_result(v(11)),
            InstrNode::new(Inst::DialectOp(Box::new(
                trust_ir::dialect::vector::pack_lanes(v4i32.clone(), [v(11), v(11), v(11), v(11)]),
            )))
            .with_result(v(12)),
            InstrNode::new(Inst::BinOp {
                op,
                ty: v4i32.clone(),
                lhs: v(10),
                rhs: v(12),
            })
            .with_result(v(13)),
            InstrNode::new(Inst::Store {
                ty: v4i32,
                ptr: v(1),
                value: v(13),
                align: None,
                volatile: false,
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module.add_function(func);
    module
}

/// True if `code` contains any 4-byte little-endian NEON SIMD shift-by-immediate
/// word for the 4S arrangement matching `op`/`shift`, ignoring the Rn/Rd fields.
///
/// `op_base` is the instruction word with Rn=Rd=0; we mask off bits [9:0]
/// (Rn:Rd) and compare.
fn contains_neon_shift_4s(code: &[u8], op_base: u32) -> bool {
    let mask = !0x3FFu32; // ignore Rn (bits 9:5) and Rd (bits 4:0)
    code.windows(4).any(|w| {
        let word = u32::from_le_bytes([w[0], w[1], w[2], w[3]]);
        (word & mask) == (op_base & mask)
    })
}

#[test]
fn aarch64_uniform_const_v4i32_shifts_emit_verified_neon_simd_immediates() {
    // (op, count, op_base) where op_base is the SHL/USHR/SSHR.4S word with
    // Rn=Rd=0, exactly as validated against clang in encoding_neon.rs.
    //   SHL  v0.4s, v0.4s, #count   -> 0x4F20_5400 | ((32+count) << 16)
    //   USHR v0.4s, v0.4s, #count   -> 0x6F00_0400 | ((64-count) << 16)
    //   SSHR v0.4s, v0.4s, #count   -> 0x4F00_0400 | ((64-count) << 16)
    let cases: &[(BinOp, i128, u32)] = &[
        (BinOp::Shl, 6, 0x4F00_5400 | ((32 + 6) << 16)),
        (BinOp::LShr, 2, 0x6F00_0400 | ((64 - 2) << 16)),
        (BinOp::AShr, 4, 0x4F00_0400 | ((64 - 4) << 16)),
    ];

    for (op, count, op_base) in cases {
        let module = build_uniform_const_shift_module("v4i32_shift", *op, *count);
        let compiler = Compiler::new(CompilerConfig {
            opt_level: OptLevel::O0,
            target: Target::Aarch64,
            ..CompilerConfig::default()
        });
        let result = compiler.compile(&module).unwrap_or_else(|e| {
            panic!("AArch64 uniform-const {op:?} #{count} must compile end-to-end: {e:?}")
        });
        assert!(
            contains_neon_shift_4s(&result.object_code, *op_base),
            "AArch64 uniform-const {op:?} #{count} must emit NEON SIMD shift-by-immediate \
             (op_base={op_base:#010X})"
        );
    }
}

#[test]
fn aarch64_variable_v4i32_shifts_preserve_lane_and_result_flow() {
    let cases = [
        (BinOp::Shl, AArch64Opcode::LslRR),
        (BinOp::LShr, AArch64Opcode::LsrRR),
        (BinOp::AShr, AArch64Opcode::AsrRR),
    ];

    for (op, scalar_opcode) in cases {
        let module = build_variable_shift_module("v4i32_variable_shift", op);
        let selected = select_aarch64(&module);
        let block = &selected.blocks[&selected.block_order[0]];
        let shifts: Vec<usize> = block
            .insts
            .iter()
            .enumerate()
            .filter_map(|(index, inst)| (inst.opcode == scalar_opcode).then_some(index))
            .collect();
        assert_eq!(
            shifts.len(),
            4,
            "{op:?} must select exactly one scalar shift per lane"
        );

        let last_shift = *shifts.last().expect("four shifts have a last element");
        let (reload_index, result_reg) = block
            .insts
            .iter()
            .enumerate()
            .skip(last_shift + 1)
            .find_map(|(index, inst)| {
                if inst.opcode != AArch64Opcode::LdrRI {
                    return None;
                }
                match inst.operands.first() {
                    Some(ISelOperand::VReg(reg)) if reg.class == RegClass::Fpr128 => {
                        Some((index, *reg))
                    }
                    _ => None,
                }
            })
            .expect("lane results must be reloaded as one V128 result");
        assert!(
            block.insts.iter().skip(reload_index + 1).any(|inst| {
                inst.opcode == AArch64Opcode::StrRI
                    && matches!(
                        inst.operands.first(),
                        Some(ISelOperand::VReg(reg)) if *reg == result_reg
                    )
            }),
            "{op:?} final V128 reload must flow to the caller-visible output store"
        );
    }
}

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
        && Command::new("cc")
            .arg("--version")
            .output()
            .is_ok_and(|output| output.status.success())
}

fn link_and_run_aarch64_object(test_name: &str, object: &[u8], driver: &str) {
    if !can_link_and_run_aarch64_macho() {
        eprintln!("SKIP: AArch64 Mach-O link/run requires Apple silicon and cc");
        return;
    }

    let dir = std::env::temp_dir().join(format!(
        "trust_cg_{test_name}_{}_{}",
        std::process::id(),
        object.len()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test directory");
    let object_path = dir.join("shifts.o");
    let driver_path = dir.join("driver.c");
    let binary_path = dir.join("shift_test");
    fs::write(&object_path, object).expect("write AArch64 object");
    fs::write(&driver_path, driver).expect("write C reference driver");

    let linked = Command::new("cc")
        .args(["-o"])
        .arg(&binary_path)
        .arg(&driver_path)
        .arg(&object_path)
        .output()
        .expect("start cc");
    assert!(
        linked.status.success(),
        "link failed:\n{}",
        String::from_utf8_lossy(&linked.stderr)
    );
    let ran = Command::new(&binary_path)
        .output()
        .expect("run linked fixture");
    let _ = fs::remove_dir_all(&dir);
    assert!(
        ran.status.success(),
        "differential fixture failed with {:?}:\nstdout:\n{}\nstderr:\n{}",
        ran.status.code(),
        String::from_utf8_lossy(&ran.stdout),
        String::from_utf8_lossy(&ran.stderr)
    );
}

fn compile_aarch64_module(module: &TrustIrModule, opt_level: OptLevel) -> Vec<u8> {
    Compiler::new(CompilerConfig {
        opt_level,
        target: Target::Aarch64,
        ..CompilerConfig::default()
    })
    .compile(module)
    .expect("variable packed shifts must compile through AArch64 codegen")
    .object_code
}

const VARIABLE_SHIFT_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>

extern void _v4i32_ishl(const uint32_t *, const uint32_t *, uint32_t *);
extern void _v4i32_ushr(const uint32_t *, const uint32_t *, uint32_t *);
extern void _v4i32_sshr(const uint32_t *, const uint32_t *, uint32_t *);

static uint32_t ref_ashr(uint32_t value, uint32_t count) {
    if (count == 0) return value;
    uint32_t result = value >> count;
    if (value & UINT32_C(0x80000000))
        result |= UINT32_MAX << (32 - count);
    return result;
}

static int check_case(const uint32_t value[4], const uint32_t count[4], int base) {
    uint32_t got[4] = {0, 0, 0, 0};
    _v4i32_ishl(value, count, got);
    for (int lane = 0; lane < 4; ++lane)
        if (got[lane] != (value[lane] << count[lane])) return base + lane;

    _v4i32_ushr(value, count, got);
    for (int lane = 0; lane < 4; ++lane)
        if (got[lane] != (value[lane] >> count[lane])) return base + 4 + lane;

    _v4i32_sshr(value, count, got);
    for (int lane = 0; lane < 4; ++lane)
        if (got[lane] != ref_ashr(value[lane], count[lane])) return base + 8 + lane;
    return 0;
}

int main(void) {
    const uint32_t values[][4] = {
        {UINT32_C(1), UINT32_C(2), UINT32_C(4), UINT32_C(8)},
        {UINT32_C(0x80000000), UINT32_C(0xffffffff),
         UINT32_C(0x7fffffff), UINT32_C(0x87654321)},
        {UINT32_C(0x01234567), UINT32_C(0xfedcba98),
         UINT32_C(0x40000001), UINT32_C(0xc0000000)}
    };
    const uint32_t counts[][4] = {
        {UINT32_C(0), UINT32_C(1), UINT32_C(2), UINT32_C(3)},
        {UINT32_C(31), UINT32_C(16), UINT32_C(7), UINT32_C(1)},
        {UINT32_C(4), UINT32_C(0), UINT32_C(30), UINT32_C(15)}
    };
    for (int i = 0; i < 3; ++i) {
        int failure = check_case(values[i], counts[i], 10 + i * 16);
        if (failure) {
            fprintf(stderr, "case %d failed at code %d\n", i, failure);
            return failure;
        }
    }
    return 0;
}
"#;

#[test]
fn aarch64_variable_v4i32_shifts_match_c_at_runtime() {
    let mut module = TrustIrModule::new("v4i32_variable_shift_runtime");
    add_variable_shift_function(&mut module, 0, "_v4i32_ishl", BinOp::Shl);
    add_variable_shift_function(&mut module, 1, "_v4i32_ushr", BinOp::LShr);
    add_variable_shift_function(&mut module, 2, "_v4i32_sshr", BinOp::AShr);

    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let object = compile_aarch64_module(&module, opt_level);
        link_and_run_aarch64_object(
            &format!("variable_v4i32_shift_{opt_level:?}"),
            &object,
            VARIABLE_SHIFT_DRIVER,
        );
    }
}
