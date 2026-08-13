// trust-cg-codegen/tests/e2e_aarch64_copy_coalesce.rs
//
// Codegen-quality gate for the LinearScan copy-coalescing register hints
// (crates/trust-cg-regalloc: copy_register_hints + LinearScan hint honoring with
// the copy-point reserved-interference exemption). These bias a vreg that is
// copy-related to a fixed ABI register (formal-arg / return / call-result copies)
// onto that register, so the copy becomes an identity move `post_ra_coalesce`
// deletes — closing the redundant arg/return `mov` gap vs LLVM.
//
// Before the hints, `fn() -> i64 { 42 }` emitted `mov x1,#42 ; mov x0,x1 ; ret`
// (3 insns) and `a*b+c` emitted `mov x4,x1 ; madd x1,.. ; mov x0,x1 ; ret`
// (4 insns). The return-value copy is now eliminated (the value is produced
// directly in x0), matching clang. This test pins the emitted instruction count
// so a coalescing regression fails closed.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, Constant, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn instr_count(module: &TrustIrModule) -> usize {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O2,
        ..CompilerConfig::default()
    });
    compiler
        .compile(module)
        .expect("must compile")
        .metrics
        .instruction_count
}

/// `fn c() -> i64 { 42 }`
fn const_return_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("const_ret");
    let ft = m.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(0), "c42", ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
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
    m.add_function(f);
    m
}

/// `fn f(a,b,c) -> i64 { a*b + c }`
fn addmul_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("addmul");
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(0), "addmul", ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::I64),
            (ValueId::new(1), Ty::I64),
            (ValueId::new(2), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(3),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(4)],
            }),
        ],
    }];
    m.add_function(f);
    m
}

/// `fn f(a,b) -> i64 { a - b }`
fn sub2_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("sub2");
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(0), "sub2", ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
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
    m.add_function(f);
    m
}

/// `fn f(a,b,c) -> i64 { a + b + c }`
fn sum3_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("sum3");
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(0), "sum3", ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::I64),
            (ValueId::new(1), Ty::I64),
            (ValueId::new(2), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(3),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(4)],
            }),
        ],
    }];
    m.add_function(f);
    m
}

#[test]
fn sub2_coalesces_arg_and_return() {
    // `sub x0, x0, x1 ; ret` — both the arg-a copy and the return copy are gone
    // (a stays in x0, the sub writes x0). Matches clang. (Was 3: `mov x_,x0`.)
    // Enabled by precise incoming-argument liveness (isel append_formal_livein_uses).
    assert_eq!(
        instr_count(&sub2_module()),
        2,
        "sub2 should be `sub x0,x0,x1; ret`"
    );
}

#[test]
fn sum3_coalesces_arg_copy() {
    // `add x_,x0,x1 ; add x0,x_,x2 ; ret` — the arg-a copy is gone (a stays in
    // x0 for the first add). Matches clang. (Was 4 with a leading `mov x_,x0`.)
    assert_eq!(
        instr_count(&sum3_module()),
        3,
        "sum3 should coalesce the arg copy"
    );
}

#[test]
fn const_return_has_no_redundant_move() {
    // `mov x0, #42 ; ret` — the return-value copy is coalesced away.
    // (Was 3 with the intermediate `mov x0, x1`.)
    assert_eq!(
        instr_count(&const_return_module()),
        2,
        "const-return should coalesce the result into x0 (mov #imm + ret)",
    );
}

#[test]
fn addmul_coalesces_return_copy() {
    // `madd x0, x0, x1, x2 ; ret` — BOTH the arg-a copy and the return copy are
    // gone; the madd reads a in x0 and writes the result to x0. Matches clang's
    // optimal 2-instruction lowering. (Was 4 with a leading `mov x_,x0` and a
    // trailing `mov x0,x1`; then 3 once the return copy coalesced; now 2 once
    // `Madd`/`Msub` were added to the backward-def coalescer's retargetable set,
    // letting the madd write x0 directly — the arg copy is no longer needed.)
    assert_eq!(
        instr_count(&addmul_module()),
        2,
        "addmul should coalesce to `madd x0,x0,x1,x2 ; ret`",
    );
}
