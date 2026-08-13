// End-to-end soundness + FIRING harness for the aarch64 pure-call cluster hoist
// (opt(aarch64) 4e2b2d88, TCG_A64_PURE_CALL_HOIST). Builds a two-function module
// — a proven-PURE callee `_sq(x) = x*x` and a driver whose loop calls `_sq(7)`
// with a loop-INVARIANT argument — compiles it through the full aarch64 pipeline
// with the hoist ENABLED, then decodes+interprets the emitted machine code and
// asserts it equals BOTH the O0 (hoist inactive) result AND the trust-ir
// interpreter oracle. Because the a64 interpreter models a real link register +
// a `__text` branch-relocation map, the cross-function `bl _sq` actually
// executes.
//
// TWO properties are probed:
//   1. CORRECTNESS: the ENABLED pass produces byte-correct code (a wrong hoist —
//      running the call on a skipped path, clobbering a live reg, capturing the
//      wrong result — diverges from the oracle here).
//   2. FIRING: with a compile-time loop bound the >=1-trip guard discharges and
//      the invariant `_sq(7)` cluster is eligible to move to the preheader. The
//      test REPORTS fire-vs-decline (O2 object structurally != O0) rather than
//      hard-asserting it: the tier's fail-closed unconditional-single-successor
//      preheader hardening legitimately declines a pipeline-rotated (guard-style)
//      preheader. Either way correctness (property 1) is hard-asserted.
//
// LONE test in its own binary: it sets `TCG_A64_PURE_CALL_HOIST` at the top with
// no other test in the binary to race the process-global env.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::env_lock;
use trust_cg_codegen::interpreter::{InterpreterValue, interpret};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{
    BinOp, BlockId, Constant, FuncId, FuncTy, ICmpOp, Inst, InstrNode, Module as M, Ty, ValueId,
};

#[path = "common/mod.rs"]
mod common;
use common::a64_interp::{A64Interp, extract_text, symbol_addrs, text_branch_relocs};

/// Two functions:
///   `i64 _sq(i64 x)      { return x * x }`                         // PURE
///   `i64 _driver(i64 _n) { t=0; for i in 0..BOUND { t += _sq(7) } return t }`
///                                                     // == BOUND * 49
///
/// `_sq` is structurally pure (BinOp + Return), so the pure-callee fixpoint
/// stamps its `Bl` with `ProofAnnotation::Pure`. The argument `7` is a constant
/// defined in the driver's entry (which dominates the loop body), so the call is
/// loop-invariant — the pure-call cluster-hoist target. BOUND is a compile-time
/// constant so the >=1-trip guard discharges.
/// `arg_val` selects the value passed to `_sq` in the loop body:
///   `3`  → the constant `7` defined in entry (loop-INVARIANT → hoist target),
///   `10` → the induction variable `i` (loop-VARIANT → hoist MUST decline; a
///          wrong hoist would compute BOUND*last² instead of Σ i²).
fn build_pure_call_loop(bound: i128, arg_val: u32) -> M {
    let mut module = M::new("pure_call_hoist_e2e");
    let ft_sq = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    // _sq(x) = x * x   (FuncId 0)
    let mut sq = trust_ir::Function::new(FuncId::new(0), "_sq", ft_sq, BlockId::new(0));
    sq.blocks = vec![trust_ir::Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];

    // _driver(_n) (FuncId 1)
    let ft_drv = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut drv = trust_ir::Function::new(FuncId::new(1), "_driver", ft_drv, BlockId::new(0));

    let c = |v: i128, r: u32| {
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(v),
        })
        .with_result(ValueId::new(r))
    };
    let add = |lhs: u32, rhs: u32, r: u32| {
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(lhs),
            rhs: ValueId::new(rhs),
        })
        .with_result(ValueId::new(r))
    };

    drv.blocks = vec![
        // bb0 entry(_n=v0): arg=7 (v3), BOUND (v4), i=0 (v5), t=0 (v6); br header(i,t)
        trust_ir::Block {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)],
            body: vec![
                c(7, 3),
                c(bound, 4),
                c(0, 5),
                c(0, 6),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(5), ValueId::new(6)],
                }),
            ],
        },
        // bb1 header(i=v10, t=v11): if i >= BOUND exit(t) else body
        trust_ir::Block {
            id: BlockId::new(1),
            params: vec![(ValueId::new(10), Ty::I64), (ValueId::new(11), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sge,
                    ty: Ty::I64,
                    lhs: ValueId::new(10),
                    rhs: ValueId::new(4),
                })
                .with_result(ValueId::new(12)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(12),
                    then_target: BlockId::new(3),
                    then_args: vec![ValueId::new(11)],
                    else_target: BlockId::new(2),
                    else_args: vec![],
                }),
            ],
        },
        // bb2 body: r = _sq(7); t2 = t + r; i2 = i + 1; br header(i2, t2)
        trust_ir::Block {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(0),
                    args: vec![ValueId::new(arg_val)],
                })
                .with_result(ValueId::new(20)),
                add(11, 20, 21), // t2 = t + r
                c(1, 22),
                add(10, 22, 23), // i2 = i + 1
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(23), ValueId::new(21)],
                }),
            ],
        },
        // bb3 exit(t=v30): return t
        trust_ir::Block {
            id: BlockId::new(3),
            params: vec![(ValueId::new(30), Ty::I64)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(30)],
            })],
        },
    ];

    module.add_function(sq);
    module.add_function(drv);
    module
}

fn compile_a64(m: &M, opt: OptLevel) -> Vec<u8> {
    let c = Compiler::new(CompilerConfig {
        opt_level: opt,
        target: Target::Aarch64,
        // This two-function module must consume the thread-local pass override
        // on the calling thread instead of dispatching it to rayon workers.
        parallel: false,
        ..CompilerConfig::default()
    });
    c.compile(m).expect("aarch64 compile").object_code
}

fn run_a64(obj: &[u8], sym: &str, arg: u64) -> u64 {
    let text = extract_text(obj);
    let addrs = symbol_addrs(obj);
    let n_value = *addrs
        .get(sym)
        .unwrap_or_else(|| panic!("symbol {sym} missing in object"));
    let entry = (n_value - text.addr) as usize;
    let mut it = A64Interp::new(text.bytes).with_branch_relocs(text_branch_relocs(obj));
    it.set_x(0, arg);
    it.run(entry).expect("a64 interp run")
}

fn oracle(m: &M, arg: i128) -> i128 {
    let out = interpret(m, "_driver", &[InterpreterValue::Int(arg)])
        .unwrap_or_else(|e| panic!("oracle: {e}"));
    out[0].as_int().expect("int result")
}

#[test]
fn a64_pure_call_hoist_output_matches_oracle_and_unhoisted() {
    // The thread-local knob is set for the whole test body and restored on
    // scope exit, including on panic.
    env_lock::with_env_overrides(&[("TCG_A64_PURE_CALL_HOIST", "1")], || {
        // (1) INVARIANT arg (constant 7): the hoist target. Σ = BOUND*49.
        //     Asserts correctness AND reports firing.
        let mut any_fired = false;
        for &bound in &[10i128, 3, 1, 25] {
            let m = build_pure_call_loop(bound, 3);
            let want = oracle(&m, 0);
            assert_eq!(want, bound * 49, "oracle invariant bound={bound}");
            any_fired |= check_pair(&m, want, bound);
        }
        println!(
            "[pure-call-hoist] invariant-arg firing across bounds: {}",
            if any_fired {
                "FIRED (O2 != O0)"
            } else {
                "declined (O2 == O0)"
            }
        );

        // (2) ADVERSARIAL: the call argument is the induction variable `i`
        //     (loop-VARIANT), so `_sq(i)` differs every iteration and the hoist
        //     MUST DECLINE. If the invariance gate wrongly let it fire, the
        //     run-once preheader would evaluate `_sq` at a single `i` and the
        //     loop would sum BOUND copies of that one square instead of Σ i² — a
        //     gross, unmissable divergence. This drives the decline path through
        //     real compilation + a64 execution, not just a hand-built
        //     MachFunction.
        for &bound in &[10i128, 4, 1, 20] {
            let m = build_pure_call_loop(bound, 10); // arg = IV
            let want = oracle(&m, 0);
            let n = bound; // Σ_{i=0}^{n-1} i² = (n-1)n(2n-1)/6
            assert_eq!(
                want,
                (n - 1) * n * (2 * n - 1) / 6,
                "oracle Σi² bound={bound}"
            );
            check_pair(&m, want, bound);
        }
    });
}

/// Compile O2 (hoist active) + O0, run both through the a64 interpreter, assert
/// each equals `want`. Returns whether the hoist fired (O2 object != O0).
fn check_pair(m: &M, want: i128, bound: i128) -> bool {
    let sym_candidates = ["__driver", "_driver"];
    let obj_o2 = compile_a64(m, OptLevel::O2);
    let obj_o0 = compile_a64(m, OptLevel::O0);
    let got_o2 = sym_candidates
        .iter()
        .find_map(|s| {
            symbol_addrs(&obj_o2)
                .get(*s)
                .map(|_| run_a64(&obj_o2, s, 0))
        })
        .expect("no _driver symbol in O2 object");
    let got_o0 = sym_candidates
        .iter()
        .find_map(|s| {
            symbol_addrs(&obj_o0)
                .get(*s)
                .map(|_| run_a64(&obj_o0, s, 0))
        })
        .expect("no _driver symbol in O0 object");
    assert_eq!(
        got_o2 as i128, want,
        "O2 result bound={bound}: got {got_o2} want {want}"
    );
    assert_eq!(
        got_o0 as i128, want,
        "O0 result bound={bound}: got {got_o0} want {want}"
    );
    obj_o2 != obj_o0
}
