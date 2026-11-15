// trust-cg-verify/tests/support/trap_guard_fixtures.rs - LIR guard fixtures (L04-P12)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! One small LIR function per exact guard carrier shape, each guarding its
//! own parameters (so the replayed LIR records every guard operand's type),
//! prepared through the real AArch64 pipeline. Shared by the trap-guard
//! obligation tests and the promotion census, which must also compile against
//! a tree without the trap-guard module (it uses no new API).

#![allow(dead_code)]

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::{MachFunction, OverflowOp, pack_overflow_tag};
use trust_cg_lower::Type as LirType;
use trust_cg_lower::function::{BasicBlock, Function as LirFunction, Signature as LirSignature};
use trust_cg_lower::instructions::{Block as LirBlock, Instruction, Opcode, Value};

pub const TRIPLE: &str = "aarch64-unknown-linux-gnu";

fn inst(opcode: Opcode, args: Vec<u32>, results: Vec<u32>) -> Instruction {
    Instruction {
        opcode,
        args: args.into_iter().map(Value).collect(),
        results: results.into_iter().map(Value).collect(),
    }
}

/// `name(v0: params[0], v1: params[1], ...) -> returns` with one entry block.
fn function(
    name: &str,
    params: Vec<LirType>,
    returns: Vec<LirType>,
    body: Vec<Instruction>,
) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        LirSignature {
            params: params.clone(),
            returns,
        },
    );
    func.entry_block = LirBlock(0);
    func.block_order = vec![LirBlock(0)];
    func.blocks.insert(
        LirBlock(0),
        BasicBlock {
            params: params
                .into_iter()
                .enumerate()
                .map(|(i, ty)| (Value(i as u32), ty))
                .collect(),
            instructions: body,
            ..Default::default()
        },
    );
    func
}

/// One guard fixture: a stable name and its LIR function.
pub struct Fixture {
    pub name: String,
    pub lir: LirFunction,
}

/// Every exact guard carrier kind, width and expansion idiom.
pub fn fixtures() -> Vec<Fixture> {
    let mut out = Vec::new();
    let mut push = |name: &str, lir: LirFunction| {
        out.push(Fixture {
            name: name.to_string(),
            lir,
        });
    };
    for (name, ty, div) in [
        ("div_zero_udiv_i64", LirType::I64, Opcode::Udiv),
        ("div_zero_sdiv_i32", LirType::I32, Opcode::Sdiv),
    ] {
        push(
            name,
            function(
                name,
                vec![ty.clone(), ty.clone()],
                vec![ty],
                vec![
                    inst(Opcode::GuardDivZero { obligation: None }, vec![1], vec![]),
                    inst(div, vec![0, 1], vec![2]),
                    inst(Opcode::Return, vec![2], vec![]),
                ],
            ),
        );
    }
    push(
        "null_load_i64",
        function(
            "null_load_i64",
            vec![LirType::I64],
            vec![LirType::I64],
            vec![
                inst(Opcode::GuardNull { obligation: None }, vec![0], vec![]),
                inst(
                    Opcode::Load {
                        ty: LirType::I64,
                        align: None,
                    },
                    vec![0],
                    vec![1],
                ),
                inst(Opcode::Return, vec![1], vec![]),
            ],
        ),
    );
    for (name, ty, bitwidth, shift) in [
        ("shift_range_ishl_i32", LirType::I32, 32u16, Opcode::Ishl),
        ("shift_range_ushr_i64", LirType::I64, 64u16, Opcode::Ushr),
    ] {
        push(
            name,
            function(
                name,
                vec![ty.clone(), ty.clone()],
                vec![ty],
                vec![
                    inst(
                        Opcode::GuardShiftRange {
                            bitwidth,
                            obligation: None,
                        },
                        vec![1],
                        vec![],
                    ),
                    inst(shift, vec![0, 1], vec![2]),
                    inst(Opcode::Return, vec![2], vec![]),
                ],
            ),
        );
    }
    for (name, bound) in [
        ("bounds_const_10", 10u64),
        ("bounds_const_0x1234", 0x1234),
        ("bounds_const_0x123456", 0x12_3456),
    ] {
        push(
            name,
            function(
                name,
                vec![LirType::I64],
                vec![LirType::I64],
                vec![
                    inst(
                        Opcode::GuardBoundsCheck {
                            bound,
                            obligation: None,
                        },
                        vec![0, 0],
                        vec![],
                    ),
                    inst(Opcode::Return, vec![0], vec![]),
                ],
            ),
        );
    }
    push(
        "bounds_dyn_i64",
        function(
            "bounds_dyn_i64",
            vec![LirType::I64, LirType::I64],
            vec![LirType::I64],
            vec![
                inst(
                    Opcode::GuardBoundsCheckDyn { obligation: None },
                    vec![0, 0, 1],
                    vec![],
                ),
                inst(Opcode::Return, vec![0], vec![]),
            ],
        ),
    );
    for (name, op, width, value) in [
        (
            "overflow_sadd_i32",
            OverflowOp::SignedAdd,
            32u16,
            Opcode::Iadd,
        ),
        ("overflow_sadd_i64", OverflowOp::SignedAdd, 64, Opcode::Iadd),
        ("overflow_ssub_i32", OverflowOp::SignedSub, 32, Opcode::Isub),
        ("overflow_ssub_i64", OverflowOp::SignedSub, 64, Opcode::Isub),
        (
            "overflow_uadd_i32",
            OverflowOp::UnsignedAdd,
            32,
            Opcode::Iadd,
        ),
        (
            "overflow_uadd_i64",
            OverflowOp::UnsignedAdd,
            64,
            Opcode::Iadd,
        ),
        (
            "overflow_usub_i32",
            OverflowOp::UnsignedSub,
            32,
            Opcode::Isub,
        ),
        (
            "overflow_usub_i64",
            OverflowOp::UnsignedSub,
            64,
            Opcode::Isub,
        ),
        ("overflow_smul_i64", OverflowOp::SignedMul, 64, Opcode::Imul),
        (
            "overflow_umul_i64",
            OverflowOp::UnsignedMul,
            64,
            Opcode::Imul,
        ),
    ] {
        let ty = if width == 32 {
            LirType::I32
        } else {
            LirType::I64
        };
        push(
            name,
            function(
                name,
                vec![ty.clone(), ty.clone()],
                vec![ty],
                vec![
                    inst(value, vec![0, 1], vec![2]),
                    inst(
                        Opcode::GuardOverflow {
                            op_tag: pack_overflow_tag(op, width),
                            obligation: None,
                        },
                        vec![0, 1],
                        vec![],
                    ),
                    inst(Opcode::Return, vec![2], vec![]),
                ],
            ),
        );
    }
    push(
        "source_trap",
        function(
            "source_trap",
            vec![],
            vec![],
            vec![inst(Opcode::Trap, vec![], vec![])],
        ),
    );
    out
}

/// The fixture prepared (selection through branch resolution) at `opt`.
pub fn prepare(fixture: &Fixture, opt: OptLevel) -> MachFunction {
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: opt,
        verify: false,
        ..PipelineConfig::for_target(TRIPLE)
    });
    pipeline
        .prepare_function_with_metrics(&fixture.lir, None)
        .map(|(prepared, _)| prepared)
        .unwrap_or_else(|e| panic!("{}: prepare at {opt:?}: {e}", fixture.name))
}

/// The optimization levels the promotion census prepares every fixture at.
pub const LEVELS: [OptLevel; 2] = [OptLevel::O0, OptLevel::O2];

/// Every optimization level: the obligation tests prepare at all four.
pub const ALL_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// Bounds guards on a 32-bit index (a W register): an imm12, a MOVZ and a
/// MOVZ+MOVK bound, and a 32-bit length. Each returns its index.
pub fn i32_index_bounds() -> Vec<Fixture> {
    let mut out = Vec::new();
    for (name, bound) in [
        ("bounds_const_10_i32", 10u64),
        ("bounds_const_0x1234_i32", 0x1234),
        ("bounds_const_0x123456_i32", 0x12_3456),
    ] {
        out.push(Fixture {
            name: name.to_string(),
            lir: function(
                name,
                vec![LirType::I32],
                vec![LirType::I32],
                vec![
                    inst(
                        Opcode::GuardBoundsCheck {
                            bound,
                            obligation: None,
                        },
                        vec![0, 0],
                        vec![],
                    ),
                    inst(Opcode::Return, vec![0], vec![]),
                ],
            ),
        });
    }
    out.push(Fixture {
        name: "bounds_dyn_i32".to_string(),
        lir: function(
            "bounds_dyn_i32",
            vec![LirType::I32, LirType::I32],
            vec![LirType::I32],
            vec![
                inst(
                    Opcode::GuardBoundsCheckDyn { obligation: None },
                    vec![0, 0, 1],
                    vec![],
                ),
                inst(Opcode::Return, vec![0], vec![]),
            ],
        ),
    });
    out
}

/// Two adjacent constant bounds guards, `index0 <u 10` then `index1 <u 20`,
/// returning `index0`.
pub fn two_bounds() -> Fixture {
    let guard = |bound, index| {
        inst(
            Opcode::GuardBoundsCheck {
                bound,
                obligation: None,
            },
            vec![index, index],
            vec![],
        )
    };
    Fixture {
        name: "two_bounds".to_string(),
        lir: function(
            "two_bounds",
            vec![LirType::I64, LirType::I64],
            vec![LirType::I64],
            vec![
                guard(10, 0),
                guard(20, 1),
                inst(Opcode::Return, vec![0], vec![]),
            ],
        ),
    }
}

/// `Assert v0` on a parameter of type `ty`, then return.
pub fn assert_on(ty: LirType) -> Fixture {
    let name = format!("assert_{ty:?}").to_lowercase();
    Fixture {
        lir: function(
            &name,
            vec![ty],
            vec![],
            vec![
                inst(Opcode::Assert, vec![0], vec![]),
                inst(Opcode::Return, vec![], vec![]),
            ],
        ),
        name,
    }
}

/// A divide-by-zero guard on a narrow (`I16`) divisor before an unsigned
/// division: the carrier reads a W register the source value is narrower
/// than.
pub fn div_zero_i16() -> Fixture {
    Fixture {
        name: "div_zero_udiv_i16".to_string(),
        lir: function(
            "div_zero_udiv_i16",
            vec![LirType::I16, LirType::I16],
            vec![LirType::I16],
            vec![
                inst(Opcode::GuardDivZero { obligation: None }, vec![1], vec![]),
                inst(Opcode::Udiv, vec![0, 1], vec![2]),
                inst(Opcode::Return, vec![2], vec![]),
            ],
        ),
    }
}

/// Which guard a [`wrapped_narrow`] fixture puts on its wrapped value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WrappedGuard {
    /// `y / w`, guarded by `GuardDivZero w`.
    DivZero,
    /// `y << w`, guarded by `GuardShiftRange { bitwidth } w`.
    ShiftRange,
    /// `return w`, guarded by `GuardBoundsCheck { bound: 10 } (w, w)`.
    Bounds,
    /// `return w`, guarded by `GuardBoundsCheckDyn (w, w, y)`: the wrapped
    /// value is the index, `y` the length.
    BoundsDynIndex,
    /// `return y`, guarded by `GuardBoundsCheckDyn (y, y, w)`: `y` is the
    /// index, the wrapped value the length.
    BoundsDynLength,
}

/// `f(x: ty, y: ty) -> ty` over `w = x.wrapping_add(1)` (an `I8` or `I16`
/// add, whose 32-bit register is not masked to the narrow width), with the
/// guard on `w`: at `x = MAX` the narrow value of `w` is 0.
pub fn wrapped_narrow(ty: LirType, guard: WrappedGuard) -> Fixture {
    let name = format!("wrapped_{guard:?}_{ty:?}").to_lowercase();
    let bitwidth: u16 = if ty == LirType::I8 { 8 } else { 16 };
    let mut body = vec![
        inst(
            Opcode::Iconst {
                ty: ty.clone(),
                imm: 1,
            },
            vec![],
            vec![2],
        ),
        inst(Opcode::Iadd, vec![0, 2], vec![3]),
    ];
    match guard {
        WrappedGuard::DivZero => {
            body.push(inst(
                Opcode::GuardDivZero { obligation: None },
                vec![3],
                vec![],
            ));
            body.push(inst(Opcode::Udiv, vec![1, 3], vec![4]));
            body.push(inst(Opcode::Return, vec![4], vec![]));
        }
        WrappedGuard::ShiftRange => {
            body.push(inst(
                Opcode::GuardShiftRange {
                    bitwidth,
                    obligation: None,
                },
                vec![3],
                vec![],
            ));
            body.push(inst(Opcode::Ishl, vec![1, 3], vec![4]));
            body.push(inst(Opcode::Return, vec![4], vec![]));
        }
        WrappedGuard::Bounds => {
            body.push(inst(
                Opcode::GuardBoundsCheck {
                    bound: 10,
                    obligation: None,
                },
                vec![3, 3],
                vec![],
            ));
            body.push(inst(Opcode::Return, vec![3], vec![]));
        }
        WrappedGuard::BoundsDynIndex => {
            body.push(inst(
                Opcode::GuardBoundsCheckDyn { obligation: None },
                vec![3, 3, 1],
                vec![],
            ));
            body.push(inst(Opcode::Return, vec![3], vec![]));
        }
        WrappedGuard::BoundsDynLength => {
            body.push(inst(
                Opcode::GuardBoundsCheckDyn { obligation: None },
                vec![1, 1, 3],
                vec![],
            ));
            body.push(inst(Opcode::Return, vec![1], vec![]));
        }
    }
    Fixture {
        lir: function(&name, vec![ty.clone(), ty.clone()], vec![ty], body),
        name,
    }
}

/// `name(params) -> returns` with one block per entry of `blocks`, block 0
/// the entry (taking the parameters) and laid out in order.
fn multi_block(
    name: &str,
    params: Vec<LirType>,
    returns: Vec<LirType>,
    blocks: Vec<Vec<Instruction>>,
) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        LirSignature {
            params: params.clone(),
            returns,
        },
    );
    func.entry_block = LirBlock(0);
    for (index, body) in blocks.into_iter().enumerate() {
        func.blocks.insert(
            LirBlock(index as u32),
            BasicBlock {
                params: if index == 0 {
                    params
                        .iter()
                        .cloned()
                        .enumerate()
                        .map(|(i, ty)| (Value(i as u32), ty))
                        .collect()
                } else {
                    Vec::new()
                },
                instructions: body,
                ..Default::default()
            },
        );
        func.block_order.push(LirBlock(index as u32));
    }
    func
}

/// `ctrap(v0: I64) -> I64 { if v0 == 0 { trap } v0 }`: a source `Trap`
/// reached through a conditional branch.
pub fn conditional_trap() -> Fixture {
    use trust_cg_lower::instructions::IntCC;
    Fixture {
        name: "ctrap".to_string(),
        lir: multi_block(
            "ctrap",
            vec![LirType::I64],
            vec![LirType::I64],
            vec![
                vec![
                    inst(
                        Opcode::Iconst {
                            ty: LirType::I64,
                            imm: 0,
                        },
                        vec![],
                        vec![1],
                    ),
                    inst(Opcode::Icmp { cond: IntCC::Equal }, vec![0, 1], vec![2]),
                    inst(
                        Opcode::Brif {
                            cond: Value(2),
                            then_dest: LirBlock(1),
                            else_dest: LirBlock(2),
                        },
                        vec![2],
                        vec![],
                    ),
                ],
                vec![inst(Opcode::Trap, vec![], vec![])],
                vec![inst(Opcode::Return, vec![0], vec![])],
            ],
        ),
    }
}

/// `limited(limit: I64) -> I64 { ext(limit) }` requesting the U10
/// stack-limit check on `limit` with the trap as its overflow action: the
/// call needs a frame, so frame insertion emits the check and the overflow
/// block's `BRK #0x534c`.
pub fn stack_limited() -> Fixture {
    use trust_cg_lower::function::{StackLimitOverflow, StackLimitRequest, StackLimitSource};
    let mut lir = function(
        "stack_limited",
        vec![LirType::I64],
        vec![LirType::I64],
        vec![
            inst(
                Opcode::Call {
                    name: "trap_guard_ext".to_string(),
                    binding: Default::default(),
                },
                vec![0],
                vec![1],
            ),
            inst(Opcode::Return, vec![1], vec![]),
        ],
    );
    lir.stack_limit = Some(StackLimitRequest {
        param: 0,
        source: StackLimitSource::Value,
        overflow: StackLimitOverflow::Trap,
    });
    Fixture {
        name: "stack_limited".to_string(),
        lir,
    }
}

/// `v0 / Iconst(ty, imm)` behind a divide-by-zero guard on the constant.
pub fn div_zero_by_constant(ty: LirType, imm: i64) -> Fixture {
    let name = format!("div_zero_by_{ty:?}_{imm}").to_lowercase();
    Fixture {
        lir: function(
            &name,
            vec![ty.clone()],
            vec![ty.clone()],
            vec![
                inst(Opcode::Iconst { ty, imm }, vec![], vec![1]),
                inst(Opcode::GuardDivZero { obligation: None }, vec![1], vec![]),
                inst(Opcode::Udiv, vec![0, 1], vec![2]),
                inst(Opcode::Return, vec![2], vec![]),
            ],
        ),
        name,
    }
}
