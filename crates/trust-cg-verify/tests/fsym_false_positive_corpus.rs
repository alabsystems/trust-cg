// Symbolic execution: real-function false-positive corpus gate
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Bounded fsym corpus gate for #377.
//!
//! The corpus is hand-built trust_ir, but each entry is shaped like a real Trust Codegen
//! function family already used elsewhere in the project: hash mixers, record
//! stack traffic, bounded loops, switch dispatch, branch arguments, and public
//! API pointer/arithmetic inputs. The gate runs through the public scanner plus
//! summary path and fails on every concrete UB diagnostic.

use trust_cg_verify::fsym_summary::{FsymSummary, FsymSummaryCounters};
use trust_cg_verify::fsym_trust_ir::{
    FSYM_TRUST_IR_MAX_SWITCH_CASES, FsymTrustIrDiagnosticKind, FsymTrustIrSkipReason,
};
use trust_ir::{
    BinOp, Block, BlockId, Constant, FuncId, FuncTy, FuncTyId, Function, ICmpOp, Inst, InstrNode,
    Module, SwitchCase, Ty, UnOp, ValueId,
};

const EXPECTED_FUNCTIONS: usize = 25;
const EXPECTED_SCANNED: usize = 23;
const EXPECTED_SKIPPED: usize = 2;
const EXPECTED_UNKNOWN: usize = 3;
const MAX_FALSE_POSITIVE_BASIS_POINTS: usize = 500;
const EXPECTED_UNKNOWN_REASON: &str = "no witness found in evaluator; escalate to SMT";

#[derive(Debug, Clone, Copy)]
struct ExpectedUnknown {
    function: &'static str,
    kind: FsymTrustIrDiagnosticKind,
    reason: &'static str,
}

#[derive(Debug, Clone, Copy)]
struct ExpectedSkip {
    function: &'static str,
    reason: FsymTrustIrSkipReason,
    detail: &'static str,
}

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn bb(index: u32, body: Vec<InstrNode>) -> Block {
    block(index, vec![], body)
}

fn block(index: u32, params: Vec<(ValueId, Ty)>, body: Vec<InstrNode>) -> Block {
    Block {
        id: BlockId::new(index),
        params,
        body,
    }
}

fn const_int(result: u32, ty: Ty, value: i128) -> InstrNode {
    InstrNode::new(Inst::Const {
        ty,
        value: Constant::Int(value),
    })
    .with_result(v(result))
}

fn const_bool(result: u32, value: bool) -> InstrNode {
    InstrNode::new(Inst::Const {
        ty: Ty::Bool,
        value: Constant::Bool(value),
    })
    .with_result(v(result))
}

fn ret(value: u32) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: vec![v(value)],
    })
}

fn br(target: u32, args: &[u32]) -> InstrNode {
    InstrNode::new(Inst::Br {
        target: BlockId::new(target),
        args: args.iter().copied().map(v).collect(),
    })
}

fn condbr(
    cond: u32,
    then_target: u32,
    then_args: &[u32],
    else_target: u32,
    else_args: &[u32],
) -> InstrNode {
    InstrNode::new(Inst::CondBr {
        cond: v(cond),
        then_target: BlockId::new(then_target),
        then_args: then_args.iter().copied().map(v).collect(),
        else_target: BlockId::new(else_target),
        else_args: else_args.iter().copied().map(v).collect(),
    })
}

fn bin(result: u32, op: BinOp, ty: Ty, lhs: u32, rhs: u32) -> InstrNode {
    InstrNode::new(Inst::BinOp {
        op,
        ty,
        lhs: v(lhs),
        rhs: v(rhs),
    })
    .with_result(v(result))
}

fn icmp(result: u32, op: ICmpOp, ty: Ty, lhs: u32, rhs: u32) -> InstrNode {
    InstrNode::new(Inst::ICmp {
        op,
        ty,
        lhs: v(lhs),
        rhs: v(rhs),
    })
    .with_result(v(result))
}

fn alloca(result: u32, ty: Ty, count: Option<u32>) -> InstrNode {
    InstrNode::new(Inst::Alloca {
        ty,
        count: count.map(v),
        align: None,
    })
    .with_result(v(result))
}

fn gep(result: u32, pointee_ty: Ty, base: u32, indices: &[u32]) -> InstrNode {
    InstrNode::new(Inst::GEP {
        pointee_ty,
        base: v(base),
        indices: indices.iter().copied().map(v).collect(),
        inbounds: false,
    })
    .with_result(v(result))
}

fn load(result: u32, ty: Ty, ptr: u32) -> InstrNode {
    InstrNode::new(Inst::Load {
        ty,
        ptr: v(ptr),
        volatile: false,
        align: None,
    })
    .with_result(v(result))
}

fn store(ty: Ty, ptr: u32, value: u32) -> InstrNode {
    InstrNode::new(Inst::Store {
        ty,
        ptr: v(ptr),
        value: v(value),
        volatile: false,
        align: None,
    })
}

fn add_function(
    module: &mut Module,
    name: &str,
    params: Vec<(ValueId, Ty)>,
    returns: Vec<Ty>,
    blocks: Vec<Block>,
) {
    let func_ty = FuncTyId::new(module.func_types.len() as u32);
    module.func_types.push(FuncTy {
        params: params.iter().map(|(_, ty)| ty.clone()).collect(),
        returns,
        is_vararg: false,
    });

    let mut function = Function::new(
        FuncId::new(module.functions.len() as u32),
        name,
        func_ty,
        BlockId::new(0),
    );
    function.blocks = blocks;
    if let Some(entry) = function
        .blocks
        .iter_mut()
        .find(|block| block.id == BlockId::new(0))
    {
        entry.params = params;
    }
    module.functions.push(function);
}

fn add_single_block(
    module: &mut Module,
    name: &str,
    params: Vec<(ValueId, Ty)>,
    returns: Vec<Ty>,
    body: Vec<InstrNode>,
) {
    add_function(module, name, params, returns, vec![bb(0, body)]);
}

// The xxHash-derived avalanche, constants, and secret fragments used by this
// corpus are BSD-2-Clause; see third_party/vendor/xxhash-LICENSE.
fn add_xxh3_avalanche64(module: &mut Module) {
    add_single_block(
        module,
        "xxh3_avalanche64",
        vec![(v(0), Ty::U64)],
        vec![Ty::U64],
        vec![
            const_int(1, Ty::U64, 37),
            bin(2, BinOp::LShr, Ty::U64, 0, 1),
            bin(3, BinOp::Xor, Ty::U64, 0, 2),
            const_int(4, Ty::U64, 0x1656_6791_9E37_79F9_u64 as i128),
            bin(5, BinOp::Mul, Ty::U64, 3, 4),
            const_int(6, Ty::U64, 32),
            bin(7, BinOp::LShr, Ty::U64, 5, 6),
            bin(8, BinOp::Xor, Ty::U64, 5, 7),
            ret(8),
        ],
    );
}

fn add_murmur3_fmix32(module: &mut Module) {
    add_single_block(
        module,
        "murmur3_fmix32",
        vec![(v(0), Ty::U32)],
        vec![Ty::U32],
        vec![
            const_int(1, Ty::U32, 16),
            bin(2, BinOp::LShr, Ty::U32, 0, 1),
            bin(3, BinOp::Xor, Ty::U32, 0, 2),
            const_int(4, Ty::U32, 0x85EB_CA6B),
            bin(5, BinOp::Mul, Ty::U32, 3, 4),
            const_int(6, Ty::U32, 13),
            bin(7, BinOp::LShr, Ty::U32, 5, 6),
            bin(8, BinOp::Xor, Ty::U32, 5, 7),
            ret(8),
        ],
    );
}

fn add_fingerprint_mix16b_constants(module: &mut Module) {
    add_single_block(
        module,
        "fingerprint_mix16b_constants",
        vec![],
        vec![Ty::U64],
        vec![
            const_int(0, Ty::U64, 0x0123_4567_89AB_CDEF),
            const_int(1, Ty::U64, 0xB8FE_6C39_23A4_4BBE_u64 as i128),
            const_int(2, Ty::U64, 0xFEDC_BA98_7654_3210_u64 as i128),
            const_int(3, Ty::U64, 0x7C01_812C_F721_AD1C),
            bin(4, BinOp::Xor, Ty::U64, 0, 1),
            bin(5, BinOp::Xor, Ty::U64, 2, 3),
            bin(6, BinOp::Mul, Ty::U64, 4, 5),
            const_int(7, Ty::U64, 33),
            bin(8, BinOp::LShr, Ty::U64, 6, 7),
            bin(9, BinOp::Xor, Ty::U64, 6, 8),
            ret(9),
        ],
    );
}

fn add_ratio_percent_constants(module: &mut Module) {
    add_single_block(
        module,
        "ratio_percent_constants",
        vec![],
        vec![Ty::I64],
        vec![
            const_int(0, Ty::I64, 84),
            const_int(1, Ty::I64, 100),
            bin(2, BinOp::Mul, Ty::I64, 0, 1),
            const_int(3, Ty::I64, 7),
            bin(4, BinOp::SDiv, Ty::I64, 2, 3),
            ret(4),
        ],
    );
}

fn add_clamp_i64_nonnegative(module: &mut Module) {
    add_function(
        module,
        "clamp_i64_nonnegative",
        vec![(v(0), Ty::I64)],
        vec![Ty::I64],
        vec![
            block(
                0,
                vec![],
                vec![
                    const_int(1, Ty::I64, 0),
                    icmp(2, ICmpOp::Slt, Ty::I64, 0, 1),
                    condbr(2, 1, &[], 2, &[]),
                ],
            ),
            bb(1, vec![const_int(10, Ty::I64, 0), ret(10)]),
            bb(2, vec![ret(0)]),
        ],
    );
}

fn add_max_i64_select(module: &mut Module) {
    add_single_block(
        module,
        "max_i64_select",
        vec![(v(0), Ty::I64), (v(1), Ty::I64)],
        vec![Ty::I64],
        vec![
            icmp(2, ICmpOp::Sgt, Ty::I64, 0, 1),
            InstrNode::new(Inst::Select {
                ty: Ty::I64,
                cond: v(2),
                then_val: v(0),
                else_val: v(1),
            })
            .with_result(v(3)),
            ret(3),
        ],
    );
}

fn add_stack_record_sum4(module: &mut Module) {
    add_single_block(
        module,
        "stack_record_sum4",
        vec![],
        vec![Ty::I64],
        vec![
            const_int(0, Ty::I64, 4),
            alloca(1, Ty::I64, Some(0)),
            const_int(2, Ty::I64, 0),
            const_int(3, Ty::I64, 1),
            const_int(4, Ty::I64, 2),
            const_int(5, Ty::I64, 3),
            gep(10, Ty::I64, 1, &[2]),
            gep(11, Ty::I64, 1, &[3]),
            gep(12, Ty::I64, 1, &[4]),
            gep(13, Ty::I64, 1, &[5]),
            const_int(20, Ty::I64, 11),
            const_int(21, Ty::I64, 13),
            const_int(22, Ty::I64, 17),
            const_int(23, Ty::I64, 19),
            store(Ty::I64, 10, 20),
            store(Ty::I64, 11, 21),
            store(Ty::I64, 12, 22),
            store(Ty::I64, 13, 23),
            load(30, Ty::I64, 10),
            load(31, Ty::I64, 13),
            bin(32, BinOp::Add, Ty::I64, 30, 31),
            ret(32),
        ],
    );
}

fn add_aligned_pair_store(module: &mut Module) {
    add_single_block(
        module,
        "aligned_pair_store",
        vec![],
        vec![Ty::U64],
        vec![
            const_int(0, Ty::U64, 2),
            alloca(1, Ty::U64, Some(0)),
            const_int(2, Ty::U64, 0xAA55),
            const_int(3, Ty::U64, 1),
            gep(4, Ty::U64, 1, &[3]),
            const_int(5, Ty::U64, 0x55AA),
            store(Ty::U64, 1, 2),
            store(Ty::U64, 4, 5),
            ret(2),
        ],
    );
}

fn add_gep_stack_second_slot(module: &mut Module) {
    add_single_block(
        module,
        "gep_stack_second_slot",
        vec![],
        vec![Ty::I64],
        vec![
            const_int(0, Ty::I64, 2),
            alloca(1, Ty::I64, Some(0)),
            const_int(2, Ty::I64, 1),
            gep(3, Ty::I64, 1, &[2]),
            const_int(4, Ty::I64, 123),
            store(Ty::I64, 3, 4),
            load(5, Ty::I64, 3),
            ret(5),
        ],
    );
}

fn add_bounded_loop_countdown_sum4(module: &mut Module) {
    add_function(
        module,
        "bounded_loop_countdown_sum4",
        vec![],
        vec![Ty::I64],
        vec![
            bb(
                0,
                vec![
                    const_int(0, Ty::I64, 0),
                    const_int(1, Ty::I64, 0),
                    br(1, &[0, 1]),
                ],
            ),
            block(
                1,
                vec![(v(10), Ty::I64), (v(11), Ty::I64)],
                vec![
                    const_int(12, Ty::I64, 4),
                    icmp(13, ICmpOp::Slt, Ty::I64, 10, 12),
                    condbr(13, 2, &[], 3, &[11]),
                ],
            ),
            bb(
                2,
                vec![
                    bin(20, BinOp::Add, Ty::I64, 11, 10),
                    const_int(21, Ty::I64, 1),
                    bin(22, BinOp::Add, Ty::I64, 10, 21),
                    br(1, &[22, 20]),
                ],
            ),
            block(3, vec![(v(30), Ty::I64)], vec![ret(30)]),
        ],
    );
}

fn add_bytecode_dispatch_small_switch(module: &mut Module) {
    add_function(
        module,
        "bytecode_dispatch_small_switch",
        vec![],
        vec![Ty::I64],
        vec![
            bb(
                0,
                vec![
                    const_int(0, Ty::U32, 2),
                    InstrNode::new(Inst::Switch {
                        value: v(0),
                        default: BlockId::new(3),
                        default_args: vec![],
                        cases: vec![
                            SwitchCase {
                                value: Constant::Int(0),
                                target: BlockId::new(1),
                                args: vec![],
                            },
                            SwitchCase {
                                value: Constant::Int(1),
                                target: BlockId::new(2),
                                args: vec![],
                            },
                        ],
                        exhaustive_enum_unreachable: false,
                    }),
                ],
            ),
            bb(1, vec![const_int(10, Ty::I64, 10), ret(10)]),
            bb(2, vec![const_int(20, Ty::I64, 20), ret(20)]),
            bb(3, vec![const_int(30, Ty::I64, 30), ret(30)]),
        ],
    );
}

fn add_branch_arg_load_alloca(module: &mut Module) {
    add_function(
        module,
        "branch_arg_load_alloca",
        vec![],
        vec![Ty::I64],
        vec![
            bb(
                0,
                vec![
                    const_bool(0, true),
                    alloca(1, Ty::I64, None),
                    const_int(2, Ty::I64, 77),
                    store(Ty::I64, 1, 2),
                    condbr(0, 1, &[1], 2, &[]),
                ],
            ),
            block(
                1,
                vec![(v(10), Ty::Ptr)],
                vec![load(11, Ty::I64, 10), ret(11)],
            ),
            bb(2, vec![const_int(20, Ty::I64, 0), ret(20)]),
        ],
    );
}

fn add_negate_small_constant(module: &mut Module) {
    add_single_block(
        module,
        "negate_small_constant",
        vec![],
        vec![Ty::I64],
        vec![
            const_int(0, Ty::I64, 42),
            InstrNode::new(Inst::UnOp {
                op: UnOp::Neg,
                ty: Ty::I64,
                operand: v(0),
            })
            .with_result(v(1)),
            ret(1),
        ],
    );
}

fn add_shift_mask_index(module: &mut Module) {
    add_single_block(
        module,
        "shift_mask_index",
        vec![(v(0), Ty::U64)],
        vec![Ty::U64],
        vec![
            const_int(1, Ty::U64, 63),
            bin(2, BinOp::And, Ty::U64, 0, 1),
            const_int(3, Ty::U64, 1),
            bin(4, BinOp::Shl, Ty::U64, 3, 2),
            ret(4),
        ],
    );
}

fn add_rolling_hash_four_constants(module: &mut Module) {
    add_single_block(
        module,
        "rolling_hash_four_constants",
        vec![],
        vec![Ty::U64],
        vec![
            const_int(0, Ty::U64, 1469598103934665603_u64 as i128),
            const_int(1, Ty::U64, 1099511628211),
            const_int(2, Ty::U64, 0x61),
            bin(3, BinOp::Xor, Ty::U64, 0, 2),
            bin(4, BinOp::Mul, Ty::U64, 3, 1),
            const_int(5, Ty::U64, 0x62),
            bin(6, BinOp::Xor, Ty::U64, 4, 5),
            bin(7, BinOp::Mul, Ty::U64, 6, 1),
            ret(7),
        ],
    );
}

fn add_revert_bits32_constant(module: &mut Module) {
    add_single_block(
        module,
        "revert_bits32_constant",
        vec![],
        vec![Ty::U32],
        vec![
            const_int(0, Ty::U32, 0x0123_4567),
            const_int(1, Ty::U32, 1),
            bin(2, BinOp::LShr, Ty::U32, 0, 1),
            const_int(3, Ty::U32, 0x5555_5555),
            bin(4, BinOp::And, Ty::U32, 2, 3),
            bin(5, BinOp::And, Ty::U32, 0, 3),
            bin(6, BinOp::Shl, Ty::U32, 5, 1),
            bin(7, BinOp::Or, Ty::U32, 4, 6),
            ret(7),
        ],
    );
}

fn add_bitcount_parallel32_constant(module: &mut Module) {
    add_single_block(
        module,
        "bitcount_parallel32_constant",
        vec![],
        vec![Ty::U32],
        vec![
            const_int(0, Ty::U32, 0xF0F0_A5A5),
            const_int(1, Ty::U32, 1),
            bin(2, BinOp::LShr, Ty::U32, 0, 1),
            const_int(3, Ty::U32, 0x5555_5555),
            bin(4, BinOp::And, Ty::U32, 2, 3),
            bin(5, BinOp::Sub, Ty::U32, 0, 4),
            const_int(6, Ty::U32, 2),
            bin(7, BinOp::LShr, Ty::U32, 5, 6),
            const_int(8, Ty::U32, 0x3333_3333),
            bin(9, BinOp::And, Ty::U32, 7, 8),
            bin(10, BinOp::And, Ty::U32, 5, 8),
            bin(11, BinOp::Add, Ty::U32, 9, 10),
            ret(11),
        ],
    );
}

fn add_lowercase_ascii_classify(module: &mut Module) {
    add_single_block(
        module,
        "lowercase_ascii_classify",
        vec![(v(0), Ty::U32)],
        vec![Ty::U32],
        vec![
            const_int(1, Ty::U32, 65),
            icmp(2, ICmpOp::Uge, Ty::U32, 0, 1),
            const_int(3, Ty::U32, 90),
            icmp(4, ICmpOp::Ule, Ty::U32, 0, 3),
            bin(5, BinOp::And, Ty::Bool, 2, 4),
            const_int(6, Ty::U32, 32),
            bin(7, BinOp::Or, Ty::U32, 0, 6),
            InstrNode::new(Inst::Select {
                ty: Ty::U32,
                cond: v(5),
                then_val: v(7),
                else_val: v(0),
            })
            .with_result(v(8)),
            ret(8),
        ],
    );
}

fn add_sieve_index_constant_window(module: &mut Module) {
    add_single_block(
        module,
        "sieve_index_constant_window",
        vec![],
        vec![Ty::I64],
        vec![
            const_int(0, Ty::I64, 8),
            alloca(1, Ty::I64, Some(0)),
            const_int(2, Ty::I64, 3),
            gep(3, Ty::I64, 1, &[2]),
            const_int(4, Ty::I64, 1),
            store(Ty::I64, 3, 4),
            load(5, Ty::I64, 3),
            ret(5),
        ],
    );
}

fn add_ary3_unrolled_update4(module: &mut Module) {
    add_single_block(
        module,
        "ary3_unrolled_update4",
        vec![],
        vec![Ty::I64],
        vec![
            const_int(0, Ty::I64, 4),
            alloca(1, Ty::I64, Some(0)),
            const_int(2, Ty::I64, 0),
            const_int(3, Ty::I64, 1),
            const_int(4, Ty::I64, 2),
            const_int(5, Ty::I64, 3),
            gep(10, Ty::I64, 1, &[2]),
            gep(11, Ty::I64, 1, &[3]),
            gep(12, Ty::I64, 1, &[4]),
            gep(13, Ty::I64, 1, &[5]),
            const_int(20, Ty::I64, 1),
            const_int(21, Ty::I64, 2),
            const_int(22, Ty::I64, 3),
            const_int(23, Ty::I64, 4),
            store(Ty::I64, 10, 20),
            store(Ty::I64, 11, 21),
            store(Ty::I64, 12, 22),
            store(Ty::I64, 13, 23),
            load(30, Ty::I64, 10),
            load(31, Ty::I64, 13),
            bin(32, BinOp::Add, Ty::I64, 30, 31),
            ret(32),
        ],
    );
}

fn add_score_accumulate_signed_delta(module: &mut Module) {
    add_single_block(
        module,
        "score_accumulate_signed_delta",
        vec![(v(0), Ty::I64), (v(1), Ty::I64)],
        vec![Ty::I64],
        vec![bin(2, BinOp::Add, Ty::I64, 0, 1), ret(2)],
    );
}

fn add_runtime_ratio_symbolic_divisor(module: &mut Module) {
    add_single_block(
        module,
        "runtime_ratio_symbolic_divisor",
        vec![(v(0), Ty::I64)],
        vec![Ty::I64],
        vec![
            const_int(1, Ty::I64, 100),
            bin(2, BinOp::SDiv, Ty::I64, 1, 0),
            ret(2),
        ],
    );
}

fn add_public_buffer_read_symbolic_ptr(module: &mut Module) {
    add_single_block(
        module,
        "public_buffer_read_symbolic_ptr",
        vec![(v(0), Ty::Ptr)],
        vec![Ty::I64],
        vec![load(1, Ty::I64, 0), ret(1)],
    );
}

fn add_work_queue_poll_unbounded_loop(module: &mut Module) {
    add_function(
        module,
        "work_queue_poll_unbounded_loop",
        vec![(v(0), Ty::I64)],
        vec![Ty::I64],
        vec![
            bb(0, vec![br(1, &[0])]),
            block(
                1,
                vec![(v(10), Ty::I64)],
                vec![
                    const_int(11, Ty::I64, 1),
                    bin(12, BinOp::Add, Ty::I64, 10, 11),
                    br(1, &[12]),
                ],
            ),
        ],
    );
}

fn add_bytecode_dispatch_large_switch(module: &mut Module) {
    add_function(
        module,
        "bytecode_dispatch_large_switch",
        vec![],
        vec![Ty::I64],
        vec![
            bb(
                0,
                vec![
                    const_int(0, Ty::U32, 3),
                    InstrNode::new(Inst::Switch {
                        value: v(0),
                        default: BlockId::new(1),
                        default_args: vec![],
                        cases: (0..=FSYM_TRUST_IR_MAX_SWITCH_CASES)
                            .map(|index| SwitchCase {
                                value: Constant::Int(index as i128),
                                target: BlockId::new(1),
                                args: vec![],
                            })
                            .collect(),
                        exhaustive_enum_unreachable: false,
                    }),
                ],
            ),
            bb(1, vec![const_int(1, Ty::I64, 0), ret(1)]),
        ],
    );
}

fn real_function_false_positive_corpus() -> Module {
    let mut module = Module::new("fsym_real_function_false_positive_corpus");

    add_xxh3_avalanche64(&mut module);
    add_murmur3_fmix32(&mut module);
    add_fingerprint_mix16b_constants(&mut module);
    add_ratio_percent_constants(&mut module);
    add_clamp_i64_nonnegative(&mut module);
    add_max_i64_select(&mut module);
    add_stack_record_sum4(&mut module);
    add_aligned_pair_store(&mut module);
    add_gep_stack_second_slot(&mut module);
    add_bounded_loop_countdown_sum4(&mut module);
    add_bytecode_dispatch_small_switch(&mut module);
    add_branch_arg_load_alloca(&mut module);
    add_negate_small_constant(&mut module);
    add_shift_mask_index(&mut module);
    add_rolling_hash_four_constants(&mut module);
    add_revert_bits32_constant(&mut module);
    add_bitcount_parallel32_constant(&mut module);
    add_lowercase_ascii_classify(&mut module);
    add_sieve_index_constant_window(&mut module);
    add_ary3_unrolled_update4(&mut module);
    add_score_accumulate_signed_delta(&mut module);
    add_runtime_ratio_symbolic_divisor(&mut module);
    add_public_buffer_read_symbolic_ptr(&mut module);
    add_work_queue_poll_unbounded_loop(&mut module);
    add_bytecode_dispatch_large_switch(&mut module);

    module
}

fn expected_unknowns() -> Vec<ExpectedUnknown> {
    vec![
        ExpectedUnknown {
            function: "public_buffer_read_symbolic_ptr",
            kind: FsymTrustIrDiagnosticKind::NullDeref,
            reason: EXPECTED_UNKNOWN_REASON,
        },
        ExpectedUnknown {
            function: "runtime_ratio_symbolic_divisor",
            kind: FsymTrustIrDiagnosticKind::Arithmetic,
            reason: EXPECTED_UNKNOWN_REASON,
        },
        ExpectedUnknown {
            function: "score_accumulate_signed_delta",
            kind: FsymTrustIrDiagnosticKind::Arithmetic,
            reason: EXPECTED_UNKNOWN_REASON,
        },
    ]
}

fn expected_skips() -> Vec<ExpectedSkip> {
    vec![
        ExpectedSkip {
            function: "bytecode_dispatch_large_switch",
            reason: FsymTrustIrSkipReason::Switch,
            detail: "bb0 switch has 9 case(s), over fsym bound 8",
        },
        ExpectedSkip {
            function: "work_queue_poll_unbounded_loop",
            reason: FsymTrustIrSkipReason::Loop,
            detail: "loop header bb1 is not a conditional static-bound check",
        },
    ]
}

fn counter_line(functions: usize, counters: FsymSummaryCounters) -> String {
    format!(
        "fsym corpus: functions={functions} scanned={} skipped={} unknown={} concrete_ub={}",
        counters.scanned, counters.skipped, counters.unknown, counters.concrete_ub
    )
}

fn false_positive_basis_points(counters: FsymSummaryCounters) -> usize {
    if counters.scanned == 0 {
        return 10_000;
    }
    counters.concrete_ub * 10_000 / counters.scanned
}

fn concrete_ub_details(summary: &FsymSummary) -> String {
    let mut details = Vec::new();
    for function in &summary.functions {
        for diagnostic in &function.diagnostics {
            details.push(format!(
                "concrete_ub kind={:?} function={} bb{} inst{} message={}",
                diagnostic.kind,
                diagnostic.function,
                diagnostic.block,
                diagnostic.inst_index,
                diagnostic.message
            ));
        }
    }
    details.join("\n")
}

#[test]
fn fsym_false_positive_corpus_reports_no_concrete_ub_with_typed_accounting() {
    let module = real_function_false_positive_corpus();
    let summary = FsymSummary::scan_trust_ir_module(&module);
    let counters = summary.counters();
    let counters_text = counter_line(module.functions.len(), counters);

    println!("{counters_text}");
    for function in &summary.functions {
        if let Some(skip) = &function.skip {
            println!(
                "skip function={} reason={:?} detail={}",
                skip.function, skip.reason, skip.detail
            );
        }
        for unknown in &function.unknown_obligations {
            println!(
                "unknown kind={:?} function={} reason={}",
                unknown.kind, unknown.function, unknown.reason
            );
        }
    }

    assert_eq!(
        module.functions.len(),
        EXPECTED_FUNCTIONS,
        "{counters_text}"
    );
    assert_eq!(counters.scanned, EXPECTED_SCANNED, "{counters_text}");
    assert_eq!(counters.skipped, EXPECTED_SKIPPED, "{counters_text}");
    assert_eq!(counters.unknown, EXPECTED_UNKNOWN, "{counters_text}");
    assert_eq!(
        counters.concrete_ub,
        0,
        "{counters_text}\n{}",
        concrete_ub_details(&summary)
    );
    assert!(
        false_positive_basis_points(counters) <= MAX_FALSE_POSITIVE_BASIS_POINTS,
        "{counters_text}\nfalse_positive_basis_points={} max={MAX_FALSE_POSITIVE_BASIS_POINTS}",
        false_positive_basis_points(counters)
    );

    for expected in expected_unknowns() {
        let unknown = summary
            .functions
            .iter()
            .flat_map(|function| function.unknown_obligations.iter())
            .find(|unknown| unknown.function == expected.function && unknown.kind == expected.kind)
            .unwrap_or_else(|| panic!("{counters_text}\nmissing expected unknown: {expected:?}"));
        assert_eq!(unknown.reason, expected.reason, "{counters_text}");
        assert!(
            unknown.candidate_expression.is_some(),
            "{counters_text}\nexpected solver candidate text for {expected:?}"
        );
        assert!(
            unknown.solver_candidate.is_some(),
            "{counters_text}\nexpected typed solver candidate for {expected:?}"
        );
    }

    for expected in expected_skips() {
        let skip = summary
            .functions
            .iter()
            .filter_map(|function| function.skip.as_ref())
            .find(|skip| skip.function == expected.function)
            .unwrap_or_else(|| panic!("{counters_text}\nmissing expected skip: {expected:?}"));
        assert_eq!(skip.reason, expected.reason, "{counters_text}");
        assert_eq!(skip.detail, expected.detail, "{counters_text}");
    }
}
