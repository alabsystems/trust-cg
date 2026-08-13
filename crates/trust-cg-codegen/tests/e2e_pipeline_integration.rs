// trust-cg-codegen/tests/e2e_pipeline_integration.rs - End-to-end pipeline integration tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Integration tests exercising the full compilation path from trust_ir to Mach-O
// with coverage of:
//   - Simple arithmetic (add, sub, mul, bitwise)
//   - Control flow (branches, multi-block, loops)
//   - Proof annotations (NoOverflow, InBounds, NonZeroDivisor)
//   - Pipeline configuration (O0 vs O2 vs O3, dispatch verification, debug info)
//   - Compiler API (structured results, metrics, tracing, proof certificates)
//   - Module-level compilation
//   - Error paths (empty module, invalid configuration)
//
// Part of #404 — End-to-end compilation pipeline integration tests

use trust_cg_codegen::compiler::{CompileError, Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::pipeline::{DispatchVerifyMode, OptLevel, Pipeline, PipelineConfig};

use trust_ir::ProofAnnotation;
use trust_ir::{BinOp, ICmpOp, Inst, InstrNode};
use trust_ir::{
    Block as TrustIrBlock, Constant, FuncTy, Function as TrustIrFunction, Module as TrustIrModule,
    Ty,
};
use trust_ir::{BlockId, FuncId, FuncTyId, ValueId};

// ---------------------------------------------------------------------------
// Test infrastructure
// ---------------------------------------------------------------------------

/// Verify that bytes begin with a valid Mach-O 64-bit magic number.
fn assert_valid_macho(bytes: &[u8], context: &str) {
    assert!(
        bytes.len() >= 4,
        "{}: object file too small ({} bytes)",
        context,
        bytes.len()
    );
    assert_eq!(
        &bytes[0..4],
        &[0xCF, 0xFA, 0xED, 0xFE],
        "{}: invalid Mach-O magic",
        context
    );
}

/// Extract the MH_OBJECT filetype field from the Mach-O header.
fn macho_filetype(bytes: &[u8]) -> u32 {
    u32::from_le_bytes([bytes[12], bytes[13], bytes[14], bytes[15]])
}

/// Compile a trust_ir function through the full pipeline via the Pipeline API.
fn compile_trust_ir_via_pipeline(
    trust_ir_func: &TrustIrFunction,
    module: &TrustIrModule,
    opt_level: OptLevel,
) -> Result<Vec<u8>, String> {
    let config = PipelineConfig {
        opt_level,
        emit_debug: false,
        ..Default::default()
    };
    let pipeline = Pipeline::new(config);
    let ir_func = prepare_trust_ir_via_pipeline(trust_ir_func, module, opt_level)?;
    pipeline
        .compile_module(&[ir_func])
        .map_err(|e| format!("pipeline error: {}", e))
}

/// Prepare a trust_ir function through ISel, proof propagation, optimization, and
/// register allocation, returning the machine IR before Mach-O emission.
fn prepare_trust_ir_via_pipeline(
    trust_ir_func: &TrustIrFunction,
    module: &TrustIrModule,
    opt_level: OptLevel,
) -> Result<trust_cg_ir::MachFunction, String> {
    prepare_trust_ir_with_metrics_via_pipeline(trust_ir_func, module, opt_level)
        .map(|(func, _)| func)
}

fn prepare_trust_ir_with_metrics_via_pipeline(
    trust_ir_func: &TrustIrFunction,
    module: &TrustIrModule,
    opt_level: OptLevel,
) -> Result<
    (
        trust_cg_ir::MachFunction,
        trust_cg_codegen::pipeline::PreparationMetrics,
    ),
    String,
> {
    let (lir_func, proof_ctx) = trust_cg_lower::translate_function(trust_ir_func, module)
        .map_err(|e| format!("adapter error: {}", e))?;

    let config = PipelineConfig {
        opt_level,
        emit_debug: false,
        ..Default::default()
    };
    let pipeline = Pipeline::new(config);
    pipeline
        .prepare_function_with_metrics(&lir_func, Some(&proof_ctx))
        .map_err(|e| format!("pipeline error: {}", e))
}

// ---------------------------------------------------------------------------
// trust_ir function builders
// ---------------------------------------------------------------------------

/// fn simple_add(a: i64, b: i64) -> i64 { a + b }
fn build_simple_add() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "simple_add", ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(func.clone());
    (func, module)
}

/// fn simple_sub(a: i64, b: i64) -> i64 { a - b }
fn build_simple_sub() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(1), "simple_sub", ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(func.clone());
    (func, module)
}

/// fn mul_vals(a: i64, b: i64) -> i64 { a * b }
fn build_mul() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(2), "mul_vals", ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(func.clone());
    (func, module)
}

/// fn return_const() -> i64 { 42 }
fn build_return_const() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(3), "return_const", ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(42),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    }];
    module.add_function(func.clone());
    (func, module)
}

/// fn max_val(a: i64, b: i64) -> i64 { if a > b { a } else { b } }
///
/// Three blocks: entry with branch, two return blocks.
fn build_max_val() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(4), "max_val", ft_id, BlockId::new(0));
    func.blocks = vec![
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sgt,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(2),
                    then_target: BlockId::new(1),
                    then_args: vec![],
                    else_target: BlockId::new(2),
                    else_args: vec![],
                }),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            })],
        },
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            })],
        },
    ];
    module.add_function(func.clone());
    (func, module)
}

/// fn count_down(n: i64) -> i64
///
/// Loop: sum = 0, i = n; while (i > 0) { sum += i; i -= 1 }; return sum
fn build_count_down() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(5), "count_down", ft_id, BlockId::new(0));
    func.blocks = vec![
        // bb0 (entry): init sum=0, jump to loop header
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(1), ValueId::new(0)],
                }),
            ],
        },
        // bb1 (loop header): params(sum, i)
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![(ValueId::new(10), Ty::I64), (ValueId::new(11), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(12)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I64,
                    lhs: ValueId::new(11),
                    rhs: ValueId::new(12),
                })
                .with_result(ValueId::new(13)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(13),
                    then_target: BlockId::new(2),
                    then_args: vec![ValueId::new(10)],
                    else_target: BlockId::new(3),
                    else_args: vec![],
                }),
            ],
        },
        // bb2 (exit): return sum
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![(ValueId::new(20), Ty::I64)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(20)],
            })],
        },
        // bb3 (loop body): sum += i, i -= 1, loop back
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(10),
                    rhs: ValueId::new(11),
                })
                .with_result(ValueId::new(14)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(15)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I64,
                    lhs: ValueId::new(11),
                    rhs: ValueId::new(15),
                })
                .with_result(ValueId::new(16)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(14), ValueId::new(16)],
                }),
            ],
        },
    ];
    module.add_function(func.clone());
    (func, module)
}

/// fn proven_add(a: i64, b: i64) -> i64 { a + b }
///
/// Same as simple_add but with a producer-owned NoOverflow annotation on the
/// add instruction.  Until an independent replay capability is wired, the
/// annotation is report metadata and must not authorize a machine rewrite.
fn build_add_with_no_overflow_proof() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(6), "proven_add", ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2))
            .with_proof(ProofAnnotation::NoOverflow),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(func.clone());
    (func, module)
}

/// fn bounded_add(a: i64, b: i64) -> i64 { a + b }
///
/// The result has a bounded-output/range proof. This is not an array-bounds
/// proof and must never be converted to machine-level InBounds.
fn build_add_with_bounded_output_proof() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(16), "bounded_add", ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2))
            .with_proof(ProofAnnotation::BoundedOutput { lo: 0.0, hi: 255.0 }),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(func.clone());
    (func, module)
}

/// fn proven_extract(a: [i64; 8], i: i64) -> i64 { a[i] }
///
/// The ExtractElement carries an InBounds claim. This materializes an exact
/// runtime bounds guard.  O2 must retain it while replay authority is absent.
fn build_array_extract_with_in_bounds_proof() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let elem_ty = module.add_type(Ty::I64);
    let array_ty = Ty::Array(elem_ty, 8);
    let ft_id = module.add_func_type(FuncTy {
        params: vec![array_ty.clone(), Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(18), "proven_extract", ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), array_ty), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::ExtractElement {
                ty: Ty::I64,
                array: ValueId::new(0),
                index: ValueId::new(1),
            })
            .with_result(ValueId::new(2))
            .with_proof(ProofAnnotation::InBounds),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(func.clone());
    (func, module)
}

/// fn proven_div(a: i64, b: i64) -> i64 { a / b }
///
/// Division with NonZeroDivisor proof annotation on the divisor.
fn build_div_with_nonzero_proof() -> (TrustIrFunction, TrustIrModule) {
    build_div_rem_with_nonzero_proof(7, "proven_div", BinOp::SDiv)
}

fn build_div_rem_with_nonzero_proof(
    func_id: u32,
    name: &str,
    op: BinOp,
) -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(func_id), name, ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2))
            .with_proof(ProofAnnotation::DivNonZero),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(func.clone());
    (func, module)
}

/// fn proven_lshr(a: i64, amount: i64) -> i64 { a >> amount }
///
/// Shift with ShiftInRange proof annotation on the shift amount.
fn build_shift_with_in_range_proof() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(17), "proven_lshr", ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::LShr,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2))
            .with_proof(ProofAnnotation::ShiftInRange),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(func.clone());
    (func, module)
}

/// fn pure_add(a: i64, b: i64) -> i64 { a + b }
///
/// Function-level Pure proof annotation, which enables aggressive CSE/LICM
/// and potentially GPU/ANE dispatch.
fn build_pure_function() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(8), "pure_add", ft_id, BlockId::new(0));
    func.proofs = vec![ProofAnnotation::Pure];
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(func.clone());
    (func, module)
}

/// fn diamond(a: i64, b: i64) -> i64
///
/// Diamond control flow: entry -> if/else -> merge -> return.
///   bb0: cmp a > b, condbr -> bb1 (a+1), bb2 (b+1)
///   bb1: result = a + 1, br -> bb3
///   bb2: result = b + 1, br -> bb3
///   bb3: return result
fn build_diamond_cfg() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(9), "diamond", ft_id, BlockId::new(0));
    func.blocks = vec![
        // bb0: compare and branch
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sgt,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(2),
                    then_target: BlockId::new(1),
                    then_args: vec![],
                    else_target: BlockId::new(2),
                    else_args: vec![],
                }),
            ],
        },
        // bb1: result = a + 1
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(3),
                })
                .with_result(ValueId::new(4)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(3),
                    args: vec![ValueId::new(4)],
                }),
            ],
        },
        // bb2: result = b + 1
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(5)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(1),
                    rhs: ValueId::new(5),
                })
                .with_result(ValueId::new(6)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(3),
                    args: vec![ValueId::new(6)],
                }),
            ],
        },
        // bb3 (merge): return result
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![(ValueId::new(10), Ty::I64)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(10)],
            })],
        },
    ];
    module.add_function(func.clone());
    (func, module)
}

// ===========================================================================
// TEST 1: Simple arithmetic — add, sub, mul all produce valid Mach-O
// ===========================================================================

#[test]
fn test_pipeline_arithmetic_ops_produce_valid_macho() {
    let functions: Vec<(&str, TrustIrFunction, TrustIrModule)> = vec![
        {
            let (f, m) = build_simple_add();
            ("simple_add", f, m)
        },
        {
            let (f, m) = build_simple_sub();
            ("simple_sub", f, m)
        },
        {
            let (f, m) = build_mul();
            ("mul_vals", f, m)
        },
        {
            let (f, m) = build_return_const();
            ("return_const", f, m)
        },
    ];

    for (name, trust_ir_func, module) in &functions {
        let obj_bytes = compile_trust_ir_via_pipeline(trust_ir_func, module, OptLevel::O0)
            .unwrap_or_else(|e| panic!("{}: compilation failed: {}", name, e));

        assert_valid_macho(&obj_bytes, name);
        assert_eq!(
            macho_filetype(&obj_bytes),
            1, // MH_OBJECT
            "{}: filetype should be MH_OBJECT (1)",
            name
        );
        assert!(
            obj_bytes.len() > 100,
            "{}: object file suspiciously small ({} bytes)",
            name,
            obj_bytes.len()
        );
    }
}

// ===========================================================================
// TEST 2: Multi-block control flow — branch, if/else, diamond
// ===========================================================================

#[test]
fn test_pipeline_multi_block_control_flow() {
    let (trust_ir_func, module) = build_max_val();
    let obj_bytes = compile_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O0)
        .expect("max_val should compile through full pipeline");

    assert_valid_macho(&obj_bytes, "max_val");

    // Multi-block function should produce larger code than single-block
    let (rc_func, rc_module) = build_return_const();
    let single_block = compile_trust_ir_via_pipeline(&rc_func, &rc_module, OptLevel::O0)
        .expect("return_const should compile");

    // max_val (3 blocks, compare + branch + 2 returns) should have more
    // code than return_const (1 block, const + return).
    // We check text section sizes via the object file sizes as a proxy.
    // max_val has branching logic so it should be non-trivially larger.
    assert!(
        obj_bytes.len() >= single_block.len(),
        "Multi-block function should produce at least as much code as single-block"
    );
}

// ===========================================================================
// TEST 3: Diamond CFG — merge point with block parameters
// ===========================================================================

#[test]
fn test_pipeline_diamond_cfg_compiles() {
    let (trust_ir_func, module) = build_diamond_cfg();

    let obj_bytes = compile_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O0)
        .expect("diamond CFG should compile through full pipeline");

    assert_valid_macho(&obj_bytes, "diamond");

    // Also verify the LIR structure has the expected 4 blocks.
    let (lir_func, _proof_ctx) = trust_cg_lower::translate_function(&trust_ir_func, &module)
        .expect("adapter should translate diamond");
    assert_eq!(
        lir_func.blocks.len(),
        4,
        "diamond should have 4 blocks (entry, if, else, merge)"
    );
}

// ===========================================================================
// TEST 4: Loop — backward branch with block parameters
// ===========================================================================

#[test]
fn test_pipeline_loop_compiles() {
    let (trust_ir_func, module) = build_count_down();

    let obj_bytes = compile_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O0)
        .expect("count_down loop should compile through full pipeline");

    assert_valid_macho(&obj_bytes, "count_down");

    // count_down has 4 blocks (entry, loop header, exit, loop body).
    let (lir_func, _) = trust_cg_lower::translate_function(&trust_ir_func, &module)
        .expect("adapter should translate count_down");
    assert!(
        lir_func.blocks.len() >= 4,
        "count_down should have at least 4 blocks, got {}",
        lir_func.blocks.len()
    );
}

// ===========================================================================
// TEST 5: Proof annotations — NoOverflow compiles and preserves semantics
// ===========================================================================

#[test]
fn test_pipeline_proof_annotation_no_overflow() {
    let (trust_ir_func, module) = build_add_with_no_overflow_proof();

    // The function should compile successfully, but the producer-owned claim
    // is not behavior authority.
    let obj_bytes = compile_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O2)
        .expect("proven_add with NoOverflow should compile at O2");

    assert_valid_macho(&obj_bytes, "proven_add");

    // Verify the proof context was extracted by the adapter.
    let (_, proof_ctx) = trust_cg_lower::translate_function(&trust_ir_func, &module)
        .expect("adapter should translate proven_add");
    assert!(
        !proof_ctx.value_proofs.is_empty(),
        "proof context should contain extracted NoOverflow proof"
    );
}

#[test]
fn test_pipeline_no_overflow_claim_remains_report_only_without_replay_authority() {
    let (trust_ir_func, module) = build_add_with_no_overflow_proof();

    let ir_func = prepare_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O0)
        .expect("proven_add should prepare with proof annotations");

    assert!(
        ir_func
            .insts
            .iter()
            .all(|inst| inst.proof != Some(trust_cg_ir::ProofAnnotation::NoSignedOverflow)),
        "a public NoOverflow label must not become machine-level rewrite authority"
    );
    let (_, proof_ctx) = trust_cg_lower::translate_function(&trust_ir_func, &module)
        .expect("adapter should preserve report-only proof metadata");
    assert!(
        !proof_ctx.value_proofs.is_empty(),
        "the claim should remain observable for reporting/replay binding"
    );
}

#[test]
fn test_pipeline_bounded_output_proof_does_not_bind_as_in_bounds() {
    let (trust_ir_func, module) = build_add_with_bounded_output_proof();
    let (_, proof_ctx) = trust_cg_lower::translate_function(&trust_ir_func, &module)
        .expect("adapter should translate bounded_add");

    assert!(
        proof_ctx
            .value_proofs
            .values()
            .flatten()
            .any(|proof| matches!(proof, trust_cg_lower::Proof::InRange { lo: 0, hi: 255 })),
        "adapter should preserve BoundedOutput as an InRange proof"
    );

    let ir_func = prepare_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O0)
        .expect("bounded_add should prepare successfully");
    let machine_proofs: Vec<_> = ir_func.insts.iter().filter_map(|inst| inst.proof).collect();

    assert!(
        !machine_proofs.contains(&trust_cg_ir::ProofAnnotation::InBounds),
        "BoundedOutput/InRange facts must not masquerade as InBounds machine proofs"
    );
    assert!(
        machine_proofs.is_empty(),
        "range proofs have no single machine ProofAnnotation carrier yet"
    );
}

#[test]
fn test_pipeline_in_bounds_claim_keeps_exact_runtime_guard_without_replay_authority() {
    let (trust_ir_func, module) = build_array_extract_with_in_bounds_proof();
    let (_, proof_ctx) = trust_cg_lower::translate_function(&trust_ir_func, &module)
        .expect("adapter should translate proven_extract");

    assert!(
        proof_ctx.value_proofs.values().flatten().any(|proof| {
            matches!(
                proof,
                trust_cg_lower::Proof::ExactInBounds {
                    base: trust_cg_lower::instructions::Value(0),
                    index: trust_cg_lower::instructions::Value(1),
                    bound: 8
                }
            )
        }),
        "adapter should preserve InBounds as an exact base/index/bound proof"
    );

    let o0_func = prepare_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O0)
        .expect("proven_extract should prepare at O0");
    assert!(
        o0_func.blocks.iter().any(|block| {
            block.insts.iter().any(|id| {
                let inst = o0_func.inst(*id);
                inst.opcode == trust_cg_ir::AArch64Opcode::CmpRI
                    && inst.operands.last() == Some(&trust_cg_ir::MachOperand::Imm(8))
            })
        }),
        "O0 should retain the bounds check as an expanded index < 8 runtime guard"
    );
    assert!(
        o0_func.blocks.iter().any(|block| {
            block
                .insts
                .iter()
                .any(|id| o0_func.inst(*id).opcode == trust_cg_ir::AArch64Opcode::Brk)
        }),
        "O0 expanded bounds guard should trap on failure"
    );
    assert!(
        o0_func.blocks.iter().any(|block| {
            block
                .insts
                .iter()
                .any(|id| o0_func.inst(*id).opcode == trust_cg_ir::AArch64Opcode::LdrRI)
        }),
        "test fixture should still lower the array extract to a load"
    );

    let (o2_func, o2_metrics) =
        prepare_trust_ir_with_metrics_via_pipeline(&trust_ir_func, &module, OptLevel::O2)
            .expect("proven_extract should prepare at O2");
    assert!(
        o2_func.blocks.iter().any(|block| {
            block.insts.iter().any(|id| {
                let inst = o2_func.inst(*id);
                inst.opcode == trust_cg_ir::AArch64Opcode::CmpRI
                    && inst.operands.last() == Some(&trust_cg_ir::MachOperand::Imm(8))
            })
        }),
        "O2 must retain the exact index < 8 runtime check without replay authority"
    );
    assert!(
        o2_func.blocks.iter().any(|block| {
            block
                .insts
                .iter()
                .any(|id| o2_func.inst(*id).opcode == trust_cg_ir::AArch64Opcode::Brk)
        }),
        "O2 must retain the bounds-failure trap without replay authority"
    );
    assert!(
        o2_metrics.proof_optimization_certificates.is_empty(),
        "no applied certificate may be minted from a producer-owned label"
    );
}

// ===========================================================================
// TEST 6: Proof annotations — NonZeroDivisor compiles
// ===========================================================================

#[test]
fn test_pipeline_proof_annotation_non_zero_divisor() {
    let (trust_ir_func, module) = build_div_with_nonzero_proof();

    let o0_func = prepare_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O0)
        .expect("proven_div should prepare with proof annotations");
    assert!(
        o0_func.blocks.iter().any(|block| {
            block
                .insts
                .iter()
                .any(|id| o0_func.inst(*id).opcode == trust_cg_ir::AArch64Opcode::SDiv)
        }),
        "test fixture should lower to an SDiv instruction"
    );
    // #64: assert the GUARD SHAPE, not a cleared proof-metadata field. The
    // proof-only `TrapDivZeroIfZero divisor` carrier is EXPANDED before encoding
    // into a sound conditional-trap sequence: `CBNZ divisor, +2; BRK #1` (skip the
    // trap when the divisor is non-zero, trap when it is zero). Expansion CLEARS
    // the `proof` annotation (the carrier became real code), so the old assertion
    // that the CmpRI's `proof == Some(NonZeroDivisor)` survives O0 over-asserted on
    // metadata. The guard itself is sound and present as the CBNZ+BRK shape.
    assert!(
        o0_func.blocks.iter().any(|block| {
            block.insts.windows(2).any(|pair| {
                let guard = o0_func.inst(pair[0]);
                let trap = o0_func.inst(pair[1]);
                guard.opcode == trust_cg_ir::AArch64Opcode::Cbnz
                    && trap.opcode == trust_cg_ir::AArch64Opcode::Brk
            })
        }),
        "O0 should emit a sound div-zero guard SHAPE (CBNZ divisor,+2; BRK)"
    );

    let o2_func = prepare_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O2)
        .expect("proven_div with NonZeroDivisor should prepare at O2");
    assert!(
        o2_func.blocks.iter().any(|block| {
            block
                .insts
                .iter()
                .any(|id| o2_func.inst(*id).opcode == trust_cg_ir::AArch64Opcode::SDiv)
        }),
        "O2 should retain the signed divide"
    );
    // A producer-owned label cannot discharge the runtime guard.  O2 must keep
    // the same exact CBNZ+BRK shape as O0 until independent replay is wired.
    assert!(
        o2_func.blocks.iter().any(|block| {
            block.insts.windows(2).any(|pair| {
                o2_func.inst(pair[0]).opcode == trust_cg_ir::AArch64Opcode::Cbnz
                    && o2_func.inst(pair[1]).opcode == trust_cg_ir::AArch64Opcode::Brk
            })
        }),
        "O2 must retain the div-zero guard shape without replay authority"
    );

    let obj_bytes = compile_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O2)
        .expect("proven_div with NonZeroDivisor should compile at O2");

    assert_valid_macho(&obj_bytes, "proven_div");
}

#[test]
fn test_pipeline_proof_annotation_non_zero_divisor_covers_div_and_rem() {
    let cases = [
        (BinOp::SDiv, trust_cg_ir::AArch64Opcode::SDiv, "proven_sdiv"),
        (BinOp::UDiv, trust_cg_ir::AArch64Opcode::UDiv, "proven_udiv"),
        (BinOp::SRem, trust_cg_ir::AArch64Opcode::SDiv, "proven_srem"),
        (BinOp::URem, trust_cg_ir::AArch64Opcode::UDiv, "proven_urem"),
    ];

    for (idx, (op, expected_div_opcode, name)) in cases.into_iter().enumerate() {
        let (trust_ir_func, module) = build_div_rem_with_nonzero_proof(70 + idx as u32, name, op);

        let o0_func = prepare_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O0)
            .expect("proven div/rem should prepare at O0");
        let o0_div = o0_func
            .blocks
            .iter()
            .flat_map(|block| block.insts.iter())
            .map(|id| o0_func.inst(*id))
            .find(|inst| inst.opcode == expected_div_opcode)
            .unwrap_or_else(|| panic!("{name}: O0 should lower to the expected div opcode"));
        let o0_divisor = o0_div
            .operands
            .get(2)
            .unwrap_or_else(|| panic!("{name}: O0 div should carry a divisor operand"));
        // #64: assert the GUARD SHAPE checking the EXACT divisor, not a cleared
        // proof field. The `TrapDivZeroIfZero divisor` carrier expands to
        // `CBNZ divisor, +2; BRK #1` (skip the trap iff the divisor is non-zero);
        // expansion CLEARS the proof annotation. The guard's soundness is that the
        // CBNZ tests the SAME divisor operand the div consumes, immediately ahead
        // of the BRK trap — that is what we pin here.
        assert!(
            o0_func.blocks.iter().any(|block| {
                block.insts.windows(2).any(|pair| {
                    let guard = o0_func.inst(pair[0]);
                    let trap = o0_func.inst(pair[1]);
                    guard.opcode == trust_cg_ir::AArch64Opcode::Cbnz
                        && guard.operands.first() == Some(o0_divisor)
                        && trap.opcode == trust_cg_ir::AArch64Opcode::Brk
                })
            }),
            "{name}: O0 should CBNZ the exact divisor operand before BRK (sound div-zero guard)"
        );
        if matches!(op, BinOp::SRem | BinOp::URem) {
            assert!(
                o0_func.blocks.iter().any(|block| {
                    block.insts.windows(2).any(|pair| {
                        let div = o0_func.inst(pair[0]);
                        let msub = o0_func.inst(pair[1]);
                        div.opcode == expected_div_opcode
                            && msub.opcode == trust_cg_ir::AArch64Opcode::Msub
                            && msub.operands.len() == 4
                            && msub.operands[1] == div.operands[0]
                            && msub.operands[2] == div.operands[2]
                            && msub.operands[3] == div.operands[1]
                    })
                }),
                "{name}: O0 rem should retain MSUB dst, quotient, divisor, dividend shape"
            );
        }

        let o2_func = prepare_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O2)
            .expect("proven div/rem should prepare at O2");
        assert!(
            o2_func.blocks.iter().any(|block| {
                block
                    .insts
                    .iter()
                    .any(|id| o2_func.inst(*id).opcode == expected_div_opcode)
            }),
            "{name}: O2 should keep the arithmetic instruction"
        );
        // The producer-owned label is report-only: O2 must retain the exact
        // divisor guard until an independent replay capability authorizes it.
        assert!(
            o2_func.blocks.iter().any(|block| {
                block.insts.windows(2).any(|pair| {
                    let guard = o2_func.inst(pair[0]);
                    let trap = o2_func.inst(pair[1]);
                    guard.opcode == trust_cg_ir::AArch64Opcode::Cbnz
                        && guard.operands.first() == Some(o0_divisor)
                        && trap.opcode == trust_cg_ir::AArch64Opcode::Brk
                })
            }),
            "{name}: O2 must retain the exact div-zero guard without replay authority"
        );

        let obj_bytes = compile_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O2)
            .expect("proven div/rem should compile at O2");
        assert_valid_macho(&obj_bytes, name);
    }
}

#[test]
fn test_pipeline_proof_annotation_valid_shift() {
    let (trust_ir_func, module) = build_shift_with_in_range_proof();

    let o0_func = prepare_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O0)
        .expect("proven_lshr should prepare with proof annotations");
    assert!(
        o0_func.blocks.iter().any(|block| {
            block
                .insts
                .iter()
                .any(|id| o0_func.inst(*id).opcode == trust_cg_ir::AArch64Opcode::LsrRR)
        }),
        "test fixture should lower to an LsrRR instruction"
    );
    // #64: assert the GUARD SHAPE, not a cleared proof-metadata field. The
    // proof-only `TrapShiftRangeIfOOB` carrier is EXPANDED before encoding into a
    // sound conditional-trap sequence: `CMP amount, #bitwidth; B.LO +2; BRK #1`.
    // Expansion CLEARS the `proof` annotation (the carrier became real code), so
    // the old assertion that `cmp.proof == Some(ValidShift)` survives O0 was an
    // over-assertion on metadata. The guard itself is sound and present: a CmpRI
    // of the shift amount against the bitwidth immediate, immediately followed by
    // a conditional branch (skip-if-in-range) and a BRK trap.
    assert!(
        o0_func.blocks.iter().any(|block| {
            block.insts.windows(3).any(|triple| {
                let cmp = o0_func.inst(triple[0]);
                let skip = o0_func.inst(triple[1]);
                let trap = o0_func.inst(triple[2]);
                cmp.opcode == trust_cg_ir::AArch64Opcode::CmpRI
                    && cmp.operands.last() == Some(&trust_cg_ir::MachOperand::Imm(64))
                    && skip.opcode == trust_cg_ir::AArch64Opcode::BCond
                    && skip.operands.first()
                        == Some(&trust_cg_ir::MachOperand::Imm(i64::from(
                            trust_cg_ir::CondCode::LO.encoding(),
                        )))
                    && trap.opcode == trust_cg_ir::AArch64Opcode::Brk
            })
        }),
        "O0 should emit a sound shift-range guard SHAPE (CMP amount,#64; B.LO +2; BRK)"
    );

    let o2_func = prepare_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O2)
        .expect("proven_lshr with ValidShift should prepare at O2");
    assert!(
        o2_func.blocks.iter().any(|block| {
            block
                .insts
                .iter()
                .any(|id| o2_func.inst(*id).opcode == trust_cg_ir::AArch64Opcode::LsrRR)
        }),
        "O2 should retain the shift"
    );
    // A producer-owned label is not authority. O2 must retain the exact
    // CMP+B.LO+BRK runtime check.
    assert!(
        o2_func.blocks.iter().any(|block| {
            block.insts.windows(3).any(|triple| {
                let cmp = o2_func.inst(triple[0]);
                let skip = o2_func.inst(triple[1]);
                let trap = o2_func.inst(triple[2]);
                cmp.opcode == trust_cg_ir::AArch64Opcode::CmpRI
                    && cmp.operands.last() == Some(&trust_cg_ir::MachOperand::Imm(64))
                    && skip.opcode == trust_cg_ir::AArch64Opcode::BCond
                    && trap.opcode == trust_cg_ir::AArch64Opcode::Brk
            })
        }),
        "O2 must retain the shift-range guard shape without replay authority"
    );

    let obj_bytes = compile_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O2)
        .expect("proven_lshr with ValidShift should compile at O2");

    assert_valid_macho(&obj_bytes, "proven_lshr");
}

#[test]
fn test_compiler_metrics_surface_non_zero_divisor_proof_optimization() {
    let (_, module) = build_div_with_nonzero_proof();
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O2,
        parallel: false,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile(&module)
        .expect("proven_div should compile through public compiler API");
    let metrics = result.metrics.proof_optimizations;

    assert_eq!(
        metrics.certificate_count,
        result.proof_optimization_certificates.len()
    );
    assert_eq!(metrics.applied_count, 0);
    assert_eq!(metrics.rejected_count, 0);
    assert_eq!(metrics.certificate_count, 0);
    assert_eq!(metrics.guard_eliminated_count, 0);
    assert_eq!(metrics.guard_rejected_count, 0);
    assert_eq!(metrics.non_zero_divisor_guard_eliminated_count, 0);
    assert_eq!(metrics.valid_shift_guard_eliminated_count, 0);
}

#[test]
fn test_compiler_metrics_surface_valid_shift_proof_optimization() {
    let (_, module) = build_shift_with_in_range_proof();
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O2,
        parallel: false,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile(&module)
        .expect("proven_lshr should compile through public compiler API");
    let metrics = result.metrics.proof_optimizations;

    assert_eq!(
        metrics.certificate_count,
        result.proof_optimization_certificates.len()
    );
    assert_eq!(metrics.applied_count, 0);
    assert_eq!(metrics.rejected_count, 0);
    assert_eq!(metrics.certificate_count, 0);
    assert_eq!(metrics.guard_eliminated_count, 0);
    assert_eq!(metrics.guard_rejected_count, 0);
    assert_eq!(metrics.non_zero_divisor_guard_eliminated_count, 0);
    assert_eq!(metrics.valid_shift_guard_eliminated_count, 0);
}

#[cfg(target_arch = "aarch64")]
#[test]
fn test_jit_metrics_surface_proof_optimization_summary() {
    let (_, module) = build_div_with_nonzero_proof();
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O2,
        target: trust_cg_codegen::Target::Aarch64,
        parallel: false,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile_module_to_jit(&module, &std::collections::HashMap::new())
        .expect("proven_div should compile through public JIT API");
    let metrics = result.metrics.proof_optimizations;

    assert_eq!(
        metrics.certificate_count,
        result.proof_optimization_certificates.len()
    );
    assert_eq!(metrics.applied_count, 0);
    assert_eq!(metrics.rejected_count, 0);
    assert_eq!(metrics.certificate_count, 0);
    assert_eq!(metrics.guard_eliminated_count, 0);
    assert_eq!(metrics.non_zero_divisor_guard_eliminated_count, 0);
}

#[test]
fn test_exact_guard_annotation_cannot_drive_proof_optimization_without_replay() {
    use trust_cg_ir::function::{MachFunction, Signature, Type};
    use trust_cg_ir::inst::{AArch64Opcode, MachInst};
    use trust_cg_ir::operand::MachOperand;
    use trust_cg_ir::regs::{RegClass, VReg};
    use trust_cg_opt::pass_manager::MachinePass;
    use trust_cg_opt::proof_opts::ProofOptimization;

    let sig = Signature::new(vec![Type::I64], vec![Type::I64]);
    let mut func = MachFunction::new("guarded_div".to_string(), sig);
    let divisor = VReg::new(0, RegClass::Gpr64);
    let cmp_id = func.push_inst(
        MachInst::new(
            AArch64Opcode::CmpRI,
            vec![MachOperand::VReg(divisor), MachOperand::Imm(0)],
        )
        .with_proof(trust_cg_ir::ProofAnnotation::NonZeroDivisor),
    );
    let trap_id = func.push_inst(MachInst::new(AArch64Opcode::TrapDivZero, vec![]));
    let ret_id = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(func.entry, cmp_id);
    func.append_inst(func.entry, trap_id);
    func.append_inst(func.entry, ret_id);

    let mut pass = ProofOptimization::new();
    assert!(
        !pass.run(&mut func),
        "public proof labels must not authorize rewrites"
    );
    assert_eq!(pass.stats().divzero_checks_eliminated, 0);
    assert!(
        func.blocks[func.entry.0 as usize]
            .insts
            .iter()
            .any(|id| func.inst(*id).opcode == AArch64Opcode::TrapDivZero),
        "the runtime guard must survive without independently replayed authority"
    );
}

// ===========================================================================
// TEST 7: Proof annotations — Pure function-level proof
// ===========================================================================

#[test]
fn test_pipeline_proof_annotation_pure_function() {
    let (trust_ir_func, module) = build_pure_function();

    // A function-level Pure proof enables aggressive CSE/LICM.
    let obj_bytes = compile_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O2)
        .expect("pure_add with Pure annotation should compile at O2");

    assert_valid_macho(&obj_bytes, "pure_add");

    // Verify function-level proofs are accessible.
    assert_eq!(trust_ir_func.proofs.len(), 1);
    assert_eq!(trust_ir_func.proofs[0], ProofAnnotation::Pure);
}

// ===========================================================================
// TEST 8: Optimization levels — O0, O1, O2, O3 all produce valid output
// ===========================================================================

#[test]
fn test_pipeline_all_optimization_levels() {
    let (trust_ir_func, module) = build_count_down(); // Use a non-trivial function with loops

    for opt_level in &[OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let obj_bytes = compile_trust_ir_via_pipeline(&trust_ir_func, &module, *opt_level)
            .unwrap_or_else(|e| panic!("count_down at {:?} failed: {}", opt_level, e));

        assert_valid_macho(&obj_bytes, &format!("count_down@{:?}", opt_level));
        assert_eq!(
            macho_filetype(&obj_bytes),
            1,
            "filetype should be MH_OBJECT at {:?}",
            opt_level
        );
    }
}

// ===========================================================================
// TEST 9: Compiler API — structured compilation result
// ===========================================================================

#[test]
fn test_compiler_api_compile_ir_function() {
    let mut ir_func = trust_cg_codegen::pipeline::build_add_test_function();
    let compiler = Compiler::default_o2();

    let result = compiler
        .compile_ir_function(&mut ir_func)
        .expect("compile_ir_function should succeed");

    // Verify structured result fields.
    assert!(
        !result.object_code.is_empty(),
        "should produce Mach-O bytes"
    );
    assert_valid_macho(&result.object_code, "compiler_api_add");
    assert_eq!(result.metrics.function_count, 1);
    assert!(result.metrics.code_size_bytes > 0);
    assert!(result.metrics.instruction_count > 0);
    assert!(
        result.trace.is_none(),
        "trace should be None with default config"
    );
    assert!(result.proofs.is_none(), "proofs should be None by default");
}

// ===========================================================================
// TEST 10: Compiler API — tracing enabled
// ===========================================================================

#[test]
fn test_compiler_api_with_tracing() {
    let mut ir_func = trust_cg_codegen::pipeline::build_add_test_function();

    let compiler = Compiler::new(CompilerConfig {
        trace_level: CompilerTraceLevel::Full,
        ..CompilerConfig::default()
    });

    let result = compiler
        .compile_ir_function(&mut ir_func)
        .expect("compile with tracing should succeed");

    assert!(
        result.trace.is_some(),
        "trace should be present at Full level"
    );
    let trace = result.trace.unwrap();
    assert!(!trace.entries.is_empty(), "trace should have phase entries");
    assert!(
        trace.entries[0].phase.contains("compile"),
        "first trace entry should be compilation phase"
    );
}

// ===========================================================================
// TEST 11: Compiler API — direct prebuilt-IR proof promotion is fail-closed
// ===========================================================================

#[test]
fn test_compiler_api_proofs_require_exact_emission_inventory() {
    let mut ir_func = trust_cg_codegen::pipeline::build_add_test_function();

    let compiler = Compiler::new(CompilerConfig {
        emit_proofs: true,
        ..CompilerConfig::default()
    });

    let error = compiler
        .compile_ir_function(&mut ir_func)
        .expect_err("direct prebuilt-IR proof promotion needs an exact emitted-object inventory");

    match error {
        CompileError::ProofPromotionRejected { reason, .. } => {
            assert!(
                reason.contains("compact-unwind relocations")
                    && reason.contains("exact emitted object/plan"),
                "unexpected proof-promotion rejection: {reason}"
            );
        }
        other => panic!("expected typed ProofPromotionRejected, got {other}"),
    }
}

// ===========================================================================
// TEST 12: Compiler API — module-level compilation
// ===========================================================================

/// Build a multi-function module with all func_types properly registered.
/// Each function builder creates its own module with its own FuncTyId(0), so
/// we cannot simply add functions from separate builders into a new empty module.
/// Instead, we register all needed func_types in the shared module and
/// reassign FuncTyIds accordingly.
fn build_multi_function_module(
    name: &str,
    builders: &[fn() -> (TrustIrFunction, TrustIrModule)],
) -> TrustIrModule {
    let mut module = TrustIrModule::new(name);
    // Track registered func_types to deduplicate
    let mut registered_fts: Vec<FuncTy> = Vec::new();

    for builder in builders {
        let (mut func, src_module) = builder();
        // Look up the func_type from the source module
        let src_ft = &src_module.func_types[func.ty.index() as usize];
        // Check if we already registered an equivalent func_type
        let new_ft_id = if let Some(pos) = registered_fts.iter().position(|ft| ft == src_ft) {
            FuncTyId::new(pos as u32)
        } else {
            let id = module.add_func_type(src_ft.clone());
            registered_fts.push(src_ft.clone());
            id
        };
        func.ty = new_ft_id;
        module.add_function(func);
    }
    module
}

#[test]
fn test_compiler_api_compile_module() {
    let module =
        build_multi_function_module("test_module", &[build_simple_add, build_return_const]);

    let compiler = Compiler::default_o2();
    let result = compiler
        .compile(&module)
        .expect("module compilation should succeed");

    assert!(!result.object_code.is_empty());
    assert_valid_macho(&result.object_code, "module_compilation");
    assert_eq!(
        result.metrics.function_count, 2,
        "should report 2 functions compiled"
    );
}

// ===========================================================================
// TEST 13: Error path — empty module
// ===========================================================================

#[test]
fn test_compiler_api_empty_module_error() {
    let module = TrustIrModule::new("empty_module");
    let compiler = Compiler::default_o2();

    let result = compiler.compile(&module);
    assert!(result.is_err(), "empty module should produce an error");

    match result.unwrap_err() {
        CompileError::EmptyModule => {} // expected
        other => panic!("Expected EmptyModule error, got: {:?}", other),
    }
}

// ===========================================================================
// TEST 14: Dispatch verification — FallbackOnFailure mode
// ===========================================================================

#[test]
fn test_pipeline_dispatch_verify_fallback_mode() {
    let config = PipelineConfig {
        opt_level: OptLevel::O2,
        emit_debug: false,
        verify_dispatch: DispatchVerifyMode::FallbackOnFailure,
        ..Default::default()
    };

    let pipeline = Pipeline::new(config);
    assert_eq!(
        pipeline.config.verify_dispatch,
        DispatchVerifyMode::FallbackOnFailure
    );

    // Compile a function through this pipeline configuration.
    let (trust_ir_func, module) = build_simple_add();
    let (lir_func, _) = trust_cg_lower::translate_function(&trust_ir_func, &module)
        .expect("adapter should translate simple_add");

    let obj_bytes = pipeline
        .compile_function(&lir_func)
        .expect("FallbackOnFailure mode should compile successfully");
    assert_valid_macho(&obj_bytes, "dispatch_fallback");
}

// ===========================================================================
// TEST 15: Dispatch verification — Off mode
// ===========================================================================

#[test]
fn test_pipeline_dispatch_verify_off_mode() {
    let config = PipelineConfig {
        opt_level: OptLevel::O0,
        emit_debug: false,
        verify_dispatch: DispatchVerifyMode::Off,
        ..Default::default()
    };

    let pipeline = Pipeline::new(config);
    let (trust_ir_func, module) = build_simple_add();
    let (lir_func, _) = trust_cg_lower::translate_function(&trust_ir_func, &module)
        .expect("adapter should translate simple_add");

    let obj_bytes = pipeline
        .compile_function(&lir_func)
        .expect("Off mode should compile successfully");
    assert_valid_macho(&obj_bytes, "dispatch_off");
}

// ===========================================================================
// TEST 16: Pipeline with debug info enabled
// ===========================================================================

#[test]
fn test_pipeline_with_debug_info() {
    let config = PipelineConfig {
        opt_level: OptLevel::O0,
        emit_debug: true,
        verify_dispatch: DispatchVerifyMode::Off,
        ..Default::default()
    };

    let pipeline = Pipeline::new(config);
    let (trust_ir_func, module) = build_simple_add();
    let (lir_func, _) = trust_cg_lower::translate_function(&trust_ir_func, &module)
        .expect("adapter should translate simple_add");

    let obj_bytes = pipeline
        .compile_function(&lir_func)
        .expect("pipeline with debug info should compile successfully");

    assert_valid_macho(&obj_bytes, "debug_info");

    // With debug info enabled, the object file should be larger due to
    // DWARF sections (__debug_info, __debug_abbrev, __debug_str, __debug_line).
    let config_no_debug = PipelineConfig {
        opt_level: OptLevel::O0,
        emit_debug: false,
        verify_dispatch: DispatchVerifyMode::Off,
        ..Default::default()
    };
    let pipeline_no_debug = Pipeline::new(config_no_debug);
    let (lir_func2, _) = trust_cg_lower::translate_function(&trust_ir_func, &module)
        .expect("adapter should translate simple_add again");
    let obj_bytes_no_debug = pipeline_no_debug
        .compile_function(&lir_func2)
        .expect("pipeline without debug should compile");

    assert!(
        obj_bytes.len() > obj_bytes_no_debug.len(),
        "debug info should increase object file size ({} vs {} bytes)",
        obj_bytes.len(),
        obj_bytes_no_debug.len()
    );
}

// ===========================================================================
// TEST 17: Proof-annotated function remains compilable at O0 and O2
// ===========================================================================

#[test]
fn test_report_only_proof_annotation_compiles_at_o0_and_o2() {
    // Compile the same function (with a producer-owned proof claim) at O0 and
    // O2. Ordinary proof-independent optimizations may still change code size;
    // the claim itself is not rewrite authority.
    let (trust_ir_func, module) = build_add_with_no_overflow_proof();

    let obj_o0 = compile_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O0)
        .expect("proven_add at O0 should compile");
    let obj_o2 = compile_trust_ir_via_pipeline(&trust_ir_func, &module, OptLevel::O2)
        .expect("proven_add at O2 should compile");

    assert_valid_macho(&obj_o0, "proven_add@O0");
    assert_valid_macho(&obj_o2, "proven_add@O2");

    // Both should be valid Mach-O. The O2 version may have different code
    // size due to optimizations, but both must be structurally valid.
    // (Exact size comparison depends on which optimizations fire.)
}

// ===========================================================================
// TEST 18: Compiler config — all optimization levels produce valid metrics
// ===========================================================================

#[test]
fn test_compiler_api_optimization_pass_metrics() {
    let mut ir_func = trust_cg_codegen::pipeline::build_add_test_function();

    // O0 should report 0 optimization passes.
    let compiler_o0 = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        ..CompilerConfig::default()
    });
    let result_o0 = compiler_o0
        .compile_ir_function(&mut ir_func)
        .expect("O0 should compile");
    assert_eq!(
        result_o0.metrics.optimization_passes_run, 0,
        "O0 should run 0 optimization passes"
    );

    // O2 should report > 0 optimization passes.
    let mut ir_func2 = trust_cg_codegen::pipeline::build_add_test_function();
    let compiler_o2 = Compiler::default_o2();
    let result_o2 = compiler_o2
        .compile_ir_function(&mut ir_func2)
        .expect("O2 should compile");
    assert!(
        result_o2.metrics.optimization_passes_run > 0,
        "O2 should run optimization passes, got {}",
        result_o2.metrics.optimization_passes_run
    );
}

// ===========================================================================
// TEST 19: Pipeline default config validates
// ===========================================================================

#[test]
fn test_pipeline_default_config() {
    let config = PipelineConfig::default();
    assert_eq!(config.opt_level, OptLevel::O2);
    assert!(!config.emit_debug);
    assert_eq!(
        config.verify_dispatch,
        DispatchVerifyMode::FallbackOnFailure
    );
}

// ===========================================================================
// TEST 20: compile_to_object convenience function
// ===========================================================================

#[test]
fn test_compile_to_object_convenience() {
    use trust_cg_codegen::pipeline::compile_to_object;

    let (trust_ir_func, module) = build_simple_add();
    let (lir_func, _) = trust_cg_lower::translate_function(&trust_ir_func, &module)
        .expect("adapter should translate simple_add");

    let obj_bytes =
        compile_to_object(&lir_func, OptLevel::O2).expect("compile_to_object should succeed");

    assert_valid_macho(&obj_bytes, "compile_to_object");
    assert_eq!(macho_filetype(&obj_bytes), 1);
}

// ===========================================================================
// TEST 21: Multi-function module — all functions emitted in single .o
// ===========================================================================

/// Parse the Mach-O string table to extract all symbol name strings.
/// This is a minimal parser that finds the LC_SYMTAB load command,
/// reads the string table offset/size, and extracts null-terminated strings.
fn extract_macho_symbol_names(bytes: &[u8]) -> Vec<String> {
    // Mach-O 64-bit header: magic(4) + cputype(4) + cpusubtype(4) + filetype(4)
    //                       + ncmds(4) + sizeofcmds(4) + flags(4) + reserved(4) = 32 bytes
    let ncmds = u32::from_le_bytes([bytes[16], bytes[17], bytes[18], bytes[19]]) as usize;
    let mut offset = 32; // after mach_header_64

    let mut symtab_offset = 0u32;
    let mut symtab_nsyms = 0u32;
    let mut strtab_offset = 0u32;
    let mut strtab_size = 0u32;

    // Find LC_SYMTAB (cmd == 2)
    for _ in 0..ncmds {
        if offset + 8 > bytes.len() {
            break;
        }
        let cmd = u32::from_le_bytes([
            bytes[offset],
            bytes[offset + 1],
            bytes[offset + 2],
            bytes[offset + 3],
        ]);
        let cmdsize = u32::from_le_bytes([
            bytes[offset + 4],
            bytes[offset + 5],
            bytes[offset + 6],
            bytes[offset + 7],
        ]) as usize;

        if cmd == 2 {
            // LC_SYMTAB: cmd(4) + cmdsize(4) + symoff(4) + nsyms(4) + stroff(4) + strsize(4)
            symtab_offset = u32::from_le_bytes([
                bytes[offset + 8],
                bytes[offset + 9],
                bytes[offset + 10],
                bytes[offset + 11],
            ]);
            symtab_nsyms = u32::from_le_bytes([
                bytes[offset + 12],
                bytes[offset + 13],
                bytes[offset + 14],
                bytes[offset + 15],
            ]);
            strtab_offset = u32::from_le_bytes([
                bytes[offset + 16],
                bytes[offset + 17],
                bytes[offset + 18],
                bytes[offset + 19],
            ]);
            strtab_size = u32::from_le_bytes([
                bytes[offset + 20],
                bytes[offset + 21],
                bytes[offset + 22],
                bytes[offset + 23],
            ]);
            break;
        }
        offset += cmdsize;
    }

    let mut names = Vec::new();
    if symtab_nsyms == 0 || strtab_size == 0 {
        return names;
    }

    // Each nlist_64 entry is 16 bytes: n_strx(4) + n_type(1) + n_sect(1) + n_desc(2) + n_value(8)
    let nlist_size = 16usize;
    for i in 0..symtab_nsyms as usize {
        let nlist_off = symtab_offset as usize + i * nlist_size;
        if nlist_off + 4 > bytes.len() {
            break;
        }
        let n_strx = u32::from_le_bytes([
            bytes[nlist_off],
            bytes[nlist_off + 1],
            bytes[nlist_off + 2],
            bytes[nlist_off + 3],
        ]) as usize;

        let str_start = strtab_offset as usize + n_strx;
        if str_start >= bytes.len() {
            continue;
        }
        // Read null-terminated string
        let str_end = bytes[str_start..].iter().position(|&b| b == 0).unwrap_or(0) + str_start;
        if str_end > str_start
            && let Ok(name) = std::str::from_utf8(&bytes[str_start..str_end])
        {
            names.push(name.to_string());
        }
    }

    names
}

#[test]
fn test_multi_function_module_all_functions_emitted() {
    // Build a module with three functions using the shared-module builder.
    let module = build_multi_function_module(
        "multi_func_module",
        &[build_simple_add, build_simple_sub, build_return_const],
    );

    let compiler = Compiler::default_o2();
    let result = compiler
        .compile(&module)
        .expect("multi-function module should compile");

    // Basic validity.
    assert!(!result.object_code.is_empty());
    assert_valid_macho(&result.object_code, "multi_func_module");
    assert_eq!(
        result.metrics.function_count, 3,
        "should report 3 functions compiled"
    );

    // Verify all function symbols are present in the Mach-O symbol table.
    let symbol_names = extract_macho_symbol_names(&result.object_code);
    assert!(
        symbol_names.contains(&"_simple_add".to_string()),
        "symbol table should contain _simple_add. Found: {:?}",
        symbol_names
    );
    assert!(
        symbol_names.contains(&"_simple_sub".to_string()),
        "symbol table should contain _simple_sub. Found: {:?}",
        symbol_names
    );
    assert!(
        symbol_names.contains(&"_return_const".to_string()),
        "symbol table should contain _return_const. Found: {:?}",
        symbol_names
    );
}

// ===========================================================================
// TEST 22: Multi-function module — different from single-function output
// ===========================================================================

#[test]
fn test_multi_function_module_differs_from_single() {
    // A module with two functions should produce different (and larger)
    // output than a module with one function.
    let module_one = build_multi_function_module("one_func", &[build_simple_add]);

    let module_two =
        build_multi_function_module("two_func", &[build_simple_add, build_return_const]);

    let compiler = Compiler::default_o2();
    let result_one = compiler
        .compile(&module_one)
        .expect("single-function module");
    let result_two = compiler.compile(&module_two).expect("two-function module");

    assert!(
        result_two.object_code.len() > result_one.object_code.len(),
        "two-function module ({} bytes) should be larger than single-function ({} bytes)",
        result_two.object_code.len(),
        result_one.object_code.len(),
    );

    // Verify the two-function module has both symbols.
    let symbols = extract_macho_symbol_names(&result_two.object_code);
    assert!(symbols.contains(&"_simple_add".to_string()));
    assert!(symbols.contains(&"_return_const".to_string()));

    // The single-function module should only have one symbol.
    let symbols_one = extract_macho_symbol_names(&result_one.object_code);
    assert!(symbols_one.contains(&"_simple_add".to_string()));
    assert!(
        !symbols_one.contains(&"_return_const".to_string()),
        "single-function module should not contain _return_const"
    );
}
