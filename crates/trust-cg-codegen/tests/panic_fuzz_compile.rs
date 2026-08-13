// trust-cg-codegen/tests/panic_fuzz_compile.rs
// Property-based panic-fuzz harness for `Pipeline::compile_function`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Part of #387 (proptest panic-fuzz) / Part of #372 (Crash-free codegen).
//
// Reference: `designs/2026-04-18-crash-free-codegen-plan.md` §5 (proptest
// as primary defense) and §6 (per-crate harness).
//
// Contract under test: for *any* trust_ir function, the full end-to-end
// compilation pipeline (`translate_function` -> `Pipeline::compile_function`)
// must either return `Ok(Vec<u8>)` or `Err(..)` — it must NEVER panic,
// abort, or debug-overflow. This is the integration-level totality test;
// the per-stage harnesses (`panic_fuzz_lower`, `panic_fuzz_encode`) cover
// each boundary individually.
//
// Run:
//   cargo test -p trust-cg-codegen --test panic_fuzz_compile
// Increase case count via env:
//   PROPTEST_CASES=100000 cargo test -p trust-cg-codegen --test panic_fuzz_compile

use std::panic;

use proptest::prelude::*;
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction,
    ICmpOp, Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
};

// ---------------------------------------------------------------------------
// Shape spec (mirrors the structure used by panic_fuzz_lower so the two
// harnesses share a generator shape and shrink to the same minimal cases).
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum InstKind {
    Const(i64),
    BinOp(BinOp),
    ICmp(ICmpOp),
    Return,
    Br(u32),
    CondBr(u32, u32),
}

#[derive(Debug, Clone)]
struct BlockSpec {
    insts: Vec<InstKind>,
}

#[derive(Debug, Clone)]
struct FuncSpec {
    num_params: u8,
    blocks: Vec<BlockSpec>,
}

#[derive(Debug, Clone)]
enum VectorLoweringShape {
    V2I64AddSub {
        op: BinOp,
        lhs: [i64; 2],
        rhs: [i64; 2],
    },
    V4I32Shift {
        op: BinOp,
        lhs: [i32; 4],
        rhs: [u8; 4],
    },
}

// ---------------------------------------------------------------------------
// Strategies
// ---------------------------------------------------------------------------

fn binop_strategy() -> impl Strategy<Value = BinOp> {
    prop_oneof![
        Just(BinOp::Add),
        Just(BinOp::Sub),
        Just(BinOp::Mul),
        Just(BinOp::And),
        Just(BinOp::Or),
        Just(BinOp::Xor),
        Just(BinOp::Shl),
        Just(BinOp::LShr),
        Just(BinOp::AShr),
    ]
}

fn icmp_strategy() -> impl Strategy<Value = ICmpOp> {
    prop_oneof![
        Just(ICmpOp::Eq),
        Just(ICmpOp::Ne),
        Just(ICmpOp::Slt),
        Just(ICmpOp::Sle),
        Just(ICmpOp::Ult),
        Just(ICmpOp::Ule),
    ]
}

fn inst_kind_strategy(block_count: u32) -> impl Strategy<Value = InstKind> {
    prop_oneof![
        (-1000i64..=1000i64).prop_map(InstKind::Const),
        binop_strategy().prop_map(InstKind::BinOp),
        icmp_strategy().prop_map(InstKind::ICmp),
        Just(InstKind::Return),
        (0u32..block_count.max(1)).prop_map(InstKind::Br),
        (0u32..block_count.max(1), 0u32..block_count.max(1))
            .prop_map(|(a, b)| InstKind::CondBr(a, b)),
    ]
}

fn block_spec_strategy(block_count: u32) -> impl Strategy<Value = BlockSpec> {
    prop::collection::vec(inst_kind_strategy(block_count), 0..=5)
        .prop_map(|insts| BlockSpec { insts })
}

fn func_spec_strategy() -> impl Strategy<Value = FuncSpec> {
    // #447 closed: the pipeline's post-ISel debug-only connectivity check
    // no longer panics on legal multi-block shapes with zero inter-block
    // edges (e.g. all blocks terminating with `Return`). The generator is
    // widened back to 1..=3 blocks now that those inputs are tolerated.
    (1usize..=3usize).prop_flat_map(|nb| {
        let bc = nb as u32;
        (
            0u8..=2,
            prop::collection::vec(block_spec_strategy(bc), nb..=nb),
        )
            .prop_map(|(num_params, blocks)| FuncSpec { num_params, blocks })
    })
}

fn opt_level_strategy() -> impl Strategy<Value = OptLevel> {
    prop_oneof![
        Just(OptLevel::O0),
        Just(OptLevel::O1),
        Just(OptLevel::O2),
        Just(OptLevel::O3),
    ]
}

fn v2i64_add_sub_strategy() -> impl Strategy<Value = VectorLoweringShape> {
    (
        prop_oneof![Just(BinOp::Add), Just(BinOp::Sub)],
        (-1000i64..=1000, -1000i64..=1000),
        (-1000i64..=1000, -1000i64..=1000),
    )
        .prop_map(
            |(op, (lhs0, lhs1), (rhs0, rhs1))| VectorLoweringShape::V2I64AddSub {
                op,
                lhs: [lhs0, lhs1],
                rhs: [rhs0, rhs1],
            },
        )
}

fn v4i32_shift_strategy() -> impl Strategy<Value = VectorLoweringShape> {
    (
        prop_oneof![Just(BinOp::Shl), Just(BinOp::LShr), Just(BinOp::AShr)],
        (
            -1000i32..=1000,
            -1000i32..=1000,
            -1000i32..=1000,
            -1000i32..=1000,
        ),
        (0u8..32, 0u8..32, 0u8..32, 0u8..32),
    )
        .prop_map(|(op, (lhs0, lhs1, lhs2, lhs3), (rhs0, rhs1, rhs2, rhs3))| {
            VectorLoweringShape::V4I32Shift {
                op,
                lhs: [lhs0, lhs1, lhs2, lhs3],
                rhs: [rhs0, rhs1, rhs2, rhs3],
            }
        })
}

fn vector_lowering_shape_strategy() -> impl Strategy<Value = VectorLoweringShape> {
    prop_oneof![v2i64_add_sub_strategy(), v4i32_shift_strategy()]
}

// ---------------------------------------------------------------------------
// Materialise a well-formed trust_ir function.
//
// Unlike the lower harness, we intentionally stay on the well-formed side
// here because (a) the adapter-level malformed totality is already covered
// by `panic_fuzz_lower`, and (b) the full pipeline is a deep stack of
// passes and we want the signal here to isolate *pipeline-internal* panics
// rather than adapter-rejected-input re-panics. "Well-formed" still
// exercises a broad shape: 1..=3 blocks, 0..=2 params, 0..=5 insts/block,
// random br/condbr targets within range, random binop/icmp chains.
// ---------------------------------------------------------------------------

fn materialise(spec: &FuncSpec) -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("_panic_fuzz_compile");
    let params: Vec<Ty> = vec![Ty::I64; spec.num_params as usize];
    let ft_id = module.add_func_type(FuncTy {
        params: params.clone(),
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let block_count = spec.blocks.len();
    let mut func = TrustIrFunction::new(FuncId::new(0), "_fuzz_fn", ft_id, BlockId::new(0));

    let mut next_vid: u32 = 1000;
    let mut alloc_vid = || -> ValueId {
        let v = ValueId::new(next_vid);
        next_vid += 1;
        v
    };

    func.blocks = Vec::with_capacity(block_count);
    for (bi, bspec) in spec.blocks.iter().enumerate() {
        let block_id = BlockId::new(bi as u32);
        let mut block_params: Vec<(ValueId, Ty)> = Vec::new();
        if bi == 0 {
            for _ in 0..spec.num_params {
                block_params.push((alloc_vid(), Ty::I64));
            }
        }

        let mut body: Vec<InstrNode> = Vec::new();
        let mut defined_i64: Vec<ValueId> = block_params.iter().map(|(v, _)| *v).collect();

        for inst in &bspec.insts {
            match inst {
                InstKind::Const(v) => {
                    let vid = alloc_vid();
                    body.push(
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(*v as i128),
                        })
                        .with_result(vid),
                    );
                    defined_i64.push(vid);
                }
                InstKind::BinOp(op) => {
                    let (lhs, rhs) = pick_two(&mut defined_i64, &mut body, &mut alloc_vid);
                    let vid = alloc_vid();
                    body.push(
                        InstrNode::new(Inst::BinOp {
                            op: *op,
                            ty: Ty::I64,
                            lhs,
                            rhs,
                        })
                        .with_result(vid),
                    );
                    defined_i64.push(vid);
                }
                InstKind::ICmp(op) => {
                    let (lhs, rhs) = pick_two(&mut defined_i64, &mut body, &mut alloc_vid);
                    let vid = alloc_vid();
                    body.push(
                        InstrNode::new(Inst::ICmp {
                            op: *op,
                            ty: Ty::I64,
                            lhs,
                            rhs,
                        })
                        .with_result(vid),
                    );
                    let _ = vid; // bool value retained only by presence in body
                }
                InstKind::Return => {
                    let ret_v = pick_one(&mut defined_i64, &mut body, &mut alloc_vid);
                    body.push(InstrNode::new(Inst::Return {
                        values: vec![ret_v],
                    }));
                }
                InstKind::Br(tgt) => {
                    let tgt = BlockId::new(*tgt % block_count.max(1) as u32);
                    body.push(InstrNode::new(Inst::Br {
                        target: tgt,
                        args: vec![],
                    }));
                }
                InstKind::CondBr(t, e) => {
                    let cond = pick_one(&mut defined_i64, &mut body, &mut alloc_vid);
                    let t = BlockId::new(*t % block_count.max(1) as u32);
                    let e = BlockId::new(*e % block_count.max(1) as u32);
                    body.push(InstrNode::new(Inst::CondBr {
                        cond,
                        then_target: t,
                        then_args: vec![],
                        else_target: e,
                        else_args: vec![],
                    }));
                }
            }
        }

        // Ensure the block has at least one terminator.
        let terminates = body
            .last()
            .map(|n| {
                matches!(
                    n.inst,
                    Inst::Return { .. } | Inst::Br { .. } | Inst::CondBr { .. }
                )
            })
            .unwrap_or(false);
        if !terminates {
            let zero_vid = alloc_vid();
            body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(zero_vid),
            );
            body.push(InstrNode::new(Inst::Return {
                values: vec![zero_vid],
            }));
        }

        func.blocks.push(TrustIrBlock {
            id: block_id,
            params: block_params,
            body,
        });
    }

    (func, module)
}

fn materialise_vector_shape(spec: &VectorLoweringShape) -> (TrustIrFunction, TrustIrModule) {
    let (ty, op, lhs, rhs): (Ty, BinOp, Vec<i128>, Vec<i128>) = match spec {
        VectorLoweringShape::V2I64AddSub { op, lhs, rhs } => (
            Ty::Vector(Box::new(Ty::I64), 2),
            *op,
            lhs.iter().map(|lane| i128::from(*lane)).collect(),
            rhs.iter().map(|lane| i128::from(*lane)).collect(),
        ),
        VectorLoweringShape::V4I32Shift { op, lhs, rhs } => (
            Ty::Vector(Box::new(Ty::I32), 4),
            *op,
            lhs.iter().map(|lane| i128::from(*lane)).collect(),
            rhs.iter().map(|lane| i128::from(*lane)).collect(),
        ),
    };

    let mut module = TrustIrModule::new("_panic_fuzz_compile_vector");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![ty.clone()],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_fuzz_vector_fn", ft_id, BlockId::new(0));

    let lhs_vid = ValueId::new(1000);
    let rhs_vid = ValueId::new(1001);
    let result_vid = ValueId::new(1002);
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: Constant::Vector(lhs.into_iter().map(Constant::Int).collect()),
            })
            .with_result(lhs_vid),
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: Constant::Vector(rhs.into_iter().map(Constant::Int).collect()),
            })
            .with_result(rhs_vid),
            InstrNode::new(Inst::BinOp {
                op,
                ty,
                lhs: lhs_vid,
                rhs: rhs_vid,
            })
            .with_result(result_vid),
            InstrNode::new(Inst::Return {
                values: vec![result_vid],
            }),
        ],
    }];

    (func, module)
}

fn pick_one<F: FnMut() -> ValueId>(
    defined: &mut Vec<ValueId>,
    body: &mut Vec<InstrNode>,
    alloc_vid: &mut F,
) -> ValueId {
    if let Some(v) = defined.last() {
        *v
    } else {
        let vid = alloc_vid();
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(vid),
        );
        defined.push(vid);
        vid
    }
}

fn pick_two<F: FnMut() -> ValueId>(
    defined: &mut Vec<ValueId>,
    body: &mut Vec<InstrNode>,
    alloc_vid: &mut F,
) -> (ValueId, ValueId) {
    let a = pick_one(defined, body, alloc_vid);
    let b = pick_one(defined, body, alloc_vid);
    (a, b)
}

// ---------------------------------------------------------------------------
// Property
// ---------------------------------------------------------------------------

fn assert_no_panic(func: &TrustIrFunction, module: &TrustIrModule, opt_level: OptLevel) {
    let f = func.clone();
    let m = module.clone();
    let result = panic::catch_unwind(panic::AssertUnwindSafe(move || {
        // Stage 1: trust_ir -> LIR
        let lir = match trust_cg_lower::translate_function(&f, &m) {
            Ok((lir_func, _)) => lir_func,
            Err(_) => return, // adapter rejected — that's fine, it didn't panic
        };
        // Stage 2: LIR -> object
        let config = PipelineConfig {
            opt_level,
            emit_debug: false,
            ..Default::default()
        };
        let pipeline = Pipeline::new(config);
        let _ = pipeline.compile_function(&lir);
    }));
    if let Err(payload) = result {
        let msg = if let Some(s) = payload.downcast_ref::<&'static str>() {
            (*s).to_string()
        } else if let Some(s) = payload.downcast_ref::<String>() {
            s.clone()
        } else {
            "<non-string panic payload>".to_string()
        };
        panic!(
            "pipeline panicked on function '{}' ({} blocks, opt={:?}): {}",
            func.name,
            func.blocks.len(),
            opt_level,
            msg,
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        // The full pipeline is materially slower than the per-stage
        // harnesses (every case runs ISel, opt, regalloc, frame, encode,
        // emit). 256 cases at O3 on a 3-block function is still <30s
        // locally; reduce via PROPTEST_CASES=32 while iterating.
        cases: std::env::var("PROPTEST_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(64),
        max_shrink_iters: 200,
        .. ProptestConfig::default()
    })]

    /// Random well-formed trust_ir compiled at a random opt level. The
    /// pipeline must either produce a Mach-O object or return a typed
    /// error — never panic.
    #[test]
    fn compile_never_panics(
        spec in func_spec_strategy(),
        opt_level in opt_level_strategy(),
    ) {
        let (func, module) = materialise(&spec);
        assert_no_panic(&func, &module, opt_level);
    }

    /// Same generator, but force O0 to exercise the low-opt dispatcher
    /// path explicitly. Kept as a separate property so a regression in
    /// just-the-O0 path is easy to read from the failure message.
    #[test]
    fn compile_never_panics_o0(spec in func_spec_strategy()) {
        let (func, module) = materialise(&spec);
        assert_no_panic(&func, &module, OptLevel::O0);
    }

    /// Targeted vector-lowering shapes: `<2 x i64>` Add/Sub and
    /// `<4 x i32>` Shl/LShr/AShr. Shift counts are generated in 0..32 so
    /// this covers the semantic in-range path; typed errors are still
    /// acceptable, but panics are not.
    #[test]
    fn compile_never_panics_vector_lowering_shapes(
        spec in vector_lowering_shape_strategy(),
        opt_level in opt_level_strategy(),
    ) {
        let (func, module) = materialise_vector_shape(&spec);
        assert_no_panic(&func, &module, opt_level);
    }
}

// ---------------------------------------------------------------------------
// Regression reproducers for known panics found by this harness
// ---------------------------------------------------------------------------
//
// These pin-down tests are hand-reduced shrinks of failing proptest cases.
// They previously pinned buggy behavior with `#[should_panic]`; they now
// assert the post-fix behavior (no panic; Ok or typed Err). See #447.

/// A multi-block function in which each block independently terminates
/// with `Return` (no `Br`/`CondBr` edges between them) previously tripped
/// a post-ISel `debug_assert!` in `pipeline.rs` ("Multi-block function
/// '…' has no successor edges"). Fixed under #447: the assertion is
/// relaxed — unreachable non-entry blocks are legal trust_ir and the pipeline
/// simply encodes them (they are harmless after DCE).
#[test]
fn regression_multi_block_no_edges_panics() {
    use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};

    // Build a 2-block function where both blocks end in Return.
    let mut module = TrustIrModule::new("_panic_fuzz_compile");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "_fuzz_fn", ft_id, BlockId::new(0));

    let mk_block = |id: u32, vid: u32| TrustIrBlock {
        id: BlockId::new(id),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(vid)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(vid)],
            }),
        ],
    };
    func.blocks = vec![mk_block(0, 1000), mk_block(1, 1001)];

    // Drive the full pipeline — must not panic. Any return value (Ok or
    // typed Err) is acceptable; only a panic would regress this fix.
    let (lir, _) = trust_cg_lower::translate_function(&func, &module)
        .expect("adapter should accept multi-block all-Return");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        emit_debug: false,
        ..Default::default()
    });
    let _ = pipeline.compile_function(&lir);
}

/// A header self-edge plus a second latch previously left LoopAnalysis with a
/// stale "preheader" that was actually inside the merged loop.  LICM moved a
/// constant into that latch after an existing compare that used it, and its X5
/// value-order net correctly panicked.  The analysis now recomputes the
/// preheader from the complete merged body and LICM independently rejects stale
/// metadata; the public optimization boundary also maps any future unwinding
/// invariant assertion to a typed `PipelineError`.
#[test]
fn regression_licm_merged_latch_stale_preheader_does_not_panic() {
    let spec = FuncSpec {
        num_params: 0,
        blocks: vec![
            BlockSpec {
                insts: vec![InstKind::CondBr(0, 1)],
            },
            BlockSpec {
                insts: vec![InstKind::ICmp(ICmpOp::Eq), InstKind::Br(0)],
            },
        ],
    };
    let (func, module) = materialise(&spec);
    assert_no_panic(&func, &module, OptLevel::O2);
}
