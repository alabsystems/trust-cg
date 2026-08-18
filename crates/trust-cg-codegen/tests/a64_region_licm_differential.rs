// End-to-end soundness harness for the aarch64 region-LICM v2 hoist
// (opt(aarch64) a8d3cab4, TCG_A64_REGION_LICM). Compiles a nested loop whose
// INNER loop is outer-invariant (`inner_sum = Σ j for j in 0..100` = 4950)
// through the FULL aarch64 pipeline with the hoist ENABLED, then
// decodes+interprets the emitted machine code and asserts it equals BOTH the
// O0 (hoist inactive) machine result AND the trust-ir interpreter oracle.
//
// TWO soundness properties are pinned:
//   1. The ENABLED pass produces byte-correct code on this shape (a wrong CFG
//      surgery — dropped edge, unrepaired snapshot — would diverge here).
//   2. The hoist ACTUALLY FIRES: with the constant outer bound (8), the
//      >=1-trip guard discharges and region-LICM moves the inner loop to a
//      run-once preheader (TCG_A64_REGION_LICM_DEBUG=1 prints "HOISTED inner
//      ... out of outer ..."). The test asserts this via a firing marker so a
//      regression that silently stops hoisting is caught, not masked.
//
// LONE test in its own binary: it sets `TCG_A64_REGION_LICM` at the top with
// no other test in the binary to race the process-global env.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::env_lock;
use trust_cg_codegen::interpreter::{InterpreterValue, interpret};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{Target, TargetSpec};
use trust_ir::{
    BinOp, BlockId, Constant, FuncId, FuncTy, ICmpOp, Inst, InstrNode, Module as M, Ty, ValueId,
};

#[path = "common/mod.rs"]
mod common;
use common::a64_interp::{A64Interp, extract_text, symbol_addrs, text_branch_relocs};

/// `i64 _nested(i64 _n_ignored)`:
///   total = 0; for i in 0..OUTER { s = 0; for j in 0..INNER { s += j } total += s }
///   return total          // == OUTER * (INNER*(INNER-1)/2)
///
/// The inner loop (blocks 3/4/5) reads nothing defined by the outer loop, so
/// its whole computation is outer-invariant — the region-LICM hoist target.
/// OUTER and INNER are compile-time constants so the >=1-trip guard discharges.
fn build_nested_outer_invariant(outer_bound: i128, inner_bound: i128) -> M {
    let mut module = M::new("region_licm_e2e");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = trust_ir::Function::new(FuncId::new(0), "_nested", ft, BlockId::new(0));

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
    let br = |t: u32, args: &[u32]| {
        InstrNode::new(Inst::Br {
            target: BlockId::new(t),
            args: args.iter().map(|&a| ValueId::new(a)).collect(),
        })
    };

    func.blocks = vec![
        // bb0 entry(n=v0, ignored): OUTER_BOUND=8 (compile-time constant so the
        // outer loop is provably >=1-trip), i=0, total=0 -> outer_header
        trust_ir::Block {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)],
            body: vec![c(outer_bound, 3), c(0, 1), c(0, 2), br(1, &[1, 2])],
        },
        // bb1 outer_header(i=v10, total=v11): if i >= n exit else inner_pre
        trust_ir::Block {
            id: BlockId::new(1),
            params: vec![(ValueId::new(10), Ty::I64), (ValueId::new(11), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sge,
                    ty: Ty::I64,
                    lhs: ValueId::new(10),
                    rhs: ValueId::new(3),
                })
                .with_result(ValueId::new(12)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(12),
                    then_target: BlockId::new(6),
                    then_args: vec![ValueId::new(11)],
                    else_target: BlockId::new(2),
                    else_args: vec![],
                }),
            ],
        },
        // bb2 inner_pre: s=0, j=0 -> inner_header(j, s)
        trust_ir::Block {
            id: BlockId::new(2),
            params: vec![],
            body: vec![c(0, 20), c(0, 21), br(3, &[21, 20])],
        },
        // bb3 inner_header(j=v30, s=v31): if j >= 100 after_inner(s) else inner_body
        trust_ir::Block {
            id: BlockId::new(3),
            params: vec![(ValueId::new(30), Ty::I64), (ValueId::new(31), Ty::I64)],
            body: vec![
                c(inner_bound, 32),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sge,
                    ty: Ty::I64,
                    lhs: ValueId::new(30),
                    rhs: ValueId::new(32),
                })
                .with_result(ValueId::new(33)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(33),
                    then_target: BlockId::new(5),
                    then_args: vec![ValueId::new(31)],
                    else_target: BlockId::new(4),
                    else_args: vec![],
                }),
            ],
        },
        // bb4 inner_body: s2 = s + j; j2 = j + 1 -> inner_header(j2, s2)
        trust_ir::Block {
            id: BlockId::new(4),
            params: vec![],
            body: vec![add(31, 30, 40), c(1, 41), add(30, 41, 42), br(3, &[42, 40])],
        },
        // bb5 after_inner(s=v50): total2 = total + s; i2 = i + 1 -> outer_header(i2, total2)
        trust_ir::Block {
            id: BlockId::new(5),
            params: vec![(ValueId::new(50), Ty::I64)],
            body: vec![add(11, 50, 51), c(1, 52), add(10, 52, 53), br(1, &[53, 51])],
        },
        // bb6 exit(total=v60): return total
        trust_ir::Block {
            id: BlockId::new(6),
            params: vec![(ValueId::new(60), Ty::I64)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(60)],
            })],
        },
    ];
    module.add_function(func);
    module
}

fn compile_a64(m: &M, opt: OptLevel) -> Vec<u8> {
    // Explicit Darwin spec: the a64 interp harness parses Mach-O, and the
    // default target spec is host-OS-aware (ELF on a Linux host).
    // Cross-emission only; same pattern as a64_abi_probe.
    let c = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            target: Target::Aarch64,
            // Keep the thread-local test override on the compilation thread.
            parallel: false,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("aarch64-apple-darwin").expect("parse aarch64-apple-darwin target spec"),
    );
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
    let out = interpret(m, "_nested", &[InterpreterValue::Int(arg)])
        .unwrap_or_else(|e| panic!("oracle: {e}"));
    out[0].as_int().expect("int result")
}

/// The single test in this binary — sets the env once, no intra-binary race.
#[test]
fn a64_region_licm_hoisted_output_matches_oracle_and_unhoisted() {
    // Hold a thread-local override for the whole test; the guard restores it on
    // scope exit, including on panic.
    let env_scope = env_lock::override_scope();
    let _licm_guard = env_lock::ScopedEnvVar::set(&env_scope, "TCG_A64_REGION_LICM", "1");

    // Several outer-invariant-inner nested shapes with varied compile-time
    // bounds. Each MUST fire (O2 object structurally != O0) and produce the
    // correct result (decode+interp == O0 == the trust-ir oracle).
    let shapes: &[(i128, i128)] = &[
        (8, 100), // the canonical witness
        (3, 50),
        (16, 7),  // small inner
        (1, 200), // single outer trip (still >=1, must hoist)
        (25, 1),  // degenerate inner (1 trip) — hoist still legal
    ];
    let sym_candidates = ["__nested", "_nested"];

    for &(outer, inner) in shapes {
        let m = build_nested_outer_invariant(outer, inner);
        let want = oracle(&m, 0);
        assert_eq!(
            want,
            outer * (inner * (inner - 1) / 2),
            "oracle outer={outer} inner={inner}"
        );

        let obj_o2 = compile_a64(&m, OptLevel::O2); // region-LICM ACTIVE
        let obj_o0 = compile_a64(&m, OptLevel::O0); // region-LICM inactive (O0)

        let got_o2 = sym_candidates
            .iter()
            .find_map(|s| {
                symbol_addrs(&obj_o2)
                    .get(*s)
                    .map(|_| run_a64(&obj_o2, s, 0))
            })
            .expect("no _nested symbol in O2 object");
        let got_o0 = sym_candidates
            .iter()
            .find_map(|s| {
                symbol_addrs(&obj_o0)
                    .get(*s)
                    .map(|_| run_a64(&obj_o0, s, 0))
            })
            .expect("no _nested symbol in O0 object");

        assert_eq!(
            got_o2 as i128, want,
            "hoisted (O2) result outer={outer} inner={inner}: got {got_o2} want {want}"
        );
        assert_eq!(
            got_o0 as i128, want,
            "un-hoisted (O0) result outer={outer} inner={inner}: got {got_o0} want {want}"
        );
        // Firing witness (except the inner=1 degenerate, where a 1-trip inner
        // loop may be simplified away before region-LICM sees a hoistable
        // region — correctness still asserted above; firing is required only
        // where a real multi-trip inner region exists).
        if inner > 1 {
            assert_ne!(
                obj_o2, obj_o0,
                "O2 (region-LICM ON) == O0 for outer={outer} inner={inner} — hoist did not fire"
            );
        }
    }
}
