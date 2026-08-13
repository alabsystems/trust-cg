// trust-cg-codegen/tests/e2e_aarch64_i128_overflow.rs
//
// End-to-end (compile -> link -> RUN on this aarch64-apple-darwin host) coverage
// for i128/u128 checked-overflow add/sub (`Inst::Overflow`).
//
// Before this, `Inst::Overflow` fail-closed for every 128-bit type ("need
// 256-bit multiply"). Checked ADD/SUB, however, need no 256-bit product: they
// decompose into the same width-generic bit-pattern fallback the I8/I16/I32
// path already uses, over already-lowered+proven i128 primitives — Iadd/Isub
// (ADDS+ADC register pair), i128 Icmp, and i128 Bxor/Bnot/Band (register-pair
// logic). This test pins the real runtime behaviour at the boundaries
// (i128::MAX, i128::MIN, u128::MAX) where the overflow flag and the wrapped
// value actually differ from the non-overflowing case.
//
// Only checked MUL on i128 stays fail-closed (still needs the 256-bit product).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    Block as TrustIrBlock, Constant, FuncTy, Function as TrustIrFunction, ICmpOp, Inst, InstrNode,
    Module as TrustIrModule, OverflowOp, Ty, UnOp,
};
use trust_ir::{BlockId, FuncId, ValueId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

/// `fn name(a, b) -> i32 { if op(a, b) overflows { 1 } else { 0 } }`
/// where the operands/result are the given 128-bit `ty` (I128 or U128).
fn build_overflow_flag_func(
    func_id: u32,
    name: &str,
    module: &mut TrustIrModule,
    ty: Ty,
    op: OverflowOp,
) {
    let ft_id = module.add_func_type(FuncTy {
        params: vec![ty.clone(), ty.clone()],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(func_id), name, ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), ty.clone()), (ValueId::new(1), ty.clone())],
        body: vec![
            // (sum, did_overflow) = op(a, b)
            InstrNode::new(Inst::Overflow {
                op,
                ty,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_results([ValueId::new(2), ValueId::new(3)]),
            // one = 1i32, zero = 0i32
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(5)),
            // flag_i32 = did_overflow ? 1 : 0  (clean 0/1 in w0)
            InstrNode::new(Inst::Select {
                ty: Ty::I32,
                cond: ValueId::new(3),
                then_val: ValueId::new(4),
                else_val: ValueId::new(5),
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(6)],
            }),
        ],
    }];
    module.add_function(func);
}

/// `fn name(a, b) -> i128 { a (op) b   // the WRAPPED value (result[0]) }`
fn build_overflow_value_func(
    func_id: u32,
    name: &str,
    module: &mut TrustIrModule,
    ty: Ty,
    op: OverflowOp,
) {
    let ft_id = module.add_func_type(FuncTy {
        params: vec![ty.clone(), ty.clone()],
        returns: vec![ty.clone()],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(func_id), name, ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), ty.clone()), (ValueId::new(1), ty.clone())],
        body: vec![
            InstrNode::new(Inst::Overflow {
                op,
                ty,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_results([ValueId::new(2), ValueId::new(3)]),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(func);
}

fn build_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("i128_overflow");
    build_overflow_flag_func(
        0,
        "_i128_sadd_ovf",
        &mut module,
        Ty::I128,
        OverflowOp::AddOverflow,
    );
    build_overflow_flag_func(
        1,
        "_i128_ssub_ovf",
        &mut module,
        Ty::I128,
        OverflowOp::SubOverflow,
    );
    build_overflow_flag_func(
        2,
        "_u128_uadd_ovf",
        &mut module,
        Ty::U128,
        OverflowOp::AddOverflow,
    );
    build_overflow_flag_func(
        3,
        "_u128_usub_ovf",
        &mut module,
        Ty::U128,
        OverflowOp::SubOverflow,
    );
    build_overflow_value_func(
        4,
        "_i128_sadd_val",
        &mut module,
        Ty::I128,
        OverflowOp::AddOverflow,
    );
    module
}

/// `fn name(a) -> i128 { (op) a }` — single i128 unary op (Neg or Not).
fn build_unop_func(func_id: u32, name: &str, module: &mut TrustIrModule, op: UnOp) {
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I128],
        returns: vec![Ty::I128],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(func_id), name, ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I128)],
        body: vec![
            InstrNode::new(Inst::UnOp {
                op,
                ty: Ty::I128,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module.add_function(func);
}

fn build_unop_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("i128_unop");
    build_unop_func(0, "_i128_neg", &mut module, UnOp::Neg);
    build_unop_func(1, "_i128_not", &mut module, UnOp::Not);
    build_unop_func(2, "_i128_popcount", &mut module, UnOp::CtPop);
    module
}

/// `fn name(a, b) -> i128 { if cmp(a, b) { a } else { b } }` — i128 compare
/// feeding an i128 register-pair Select (a branchless min).
fn build_i128_cmp_select(func_id: u32, name: &str, module: &mut TrustIrModule, cmp: ICmpOp) {
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I128, Ty::I128],
        returns: vec![Ty::I128],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(func_id), name, ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I128), (ValueId::new(1), Ty::I128)],
        body: vec![
            InstrNode::new(Inst::ICmp {
                op: cmp,
                ty: Ty::I128,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Select {
                ty: Ty::I128,
                cond: ValueId::new(2),
                then_val: ValueId::new(0),
                else_val: ValueId::new(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    module.add_function(func);
}

fn build_select_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("i128_select");
    build_i128_cmp_select(0, "_i128_min", &mut module, ICmpOp::Slt);
    build_i128_cmp_select(1, "_i128_umin", &mut module, ICmpOp::Ult);
    module
}

fn build_loadstore_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("i128_loadstore");

    // _i128_load(p: *const i128) -> i128 { *p }
    let load_ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::I128],
        is_vararg: false,
    });
    let mut load_fn = TrustIrFunction::new(FuncId::new(0), "_i128_load", load_ft, BlockId::new(0));
    load_fn.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body: vec![
            InstrNode::new(Inst::Load {
                ty: Ty::I128,
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module.add_function(load_fn);

    // _i128_store(p: *mut i128, v: i128) { *p = v }
    let store_ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::I128],
        returns: vec![],
        is_vararg: false,
    });
    let mut store_fn =
        TrustIrFunction::new(FuncId::new(1), "_i128_store", store_ft, BlockId::new(0));
    store_fn.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr), (ValueId::new(1), Ty::I128)],
        body: vec![
            InstrNode::new(Inst::Store {
                ty: Ty::I128,
                ptr: ValueId::new(0),
                value: ValueId::new(1),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module.add_function(store_fn);

    module
}

/// `fn _i128_loopsum(n: i128) -> i128 { let mut s = 1<<100; let mut i = 1;
///  while i <= n { s += i; i += 1; } s }`
///
/// The loop-carried i128 accumulator `s` is threaded across the back-edge as an
/// i128 block parameter (an i128 Copy on every CFG edge). It is seeded with a
/// NONZERO high half (1<<100), so the result is wrong iff the register-pair Copy
/// drops the high half on the back-edge.
fn build_i128_loop_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("i128_loop");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I128],
        returns: vec![Ty::I128],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(0), "_i128_loopsum", ft, BlockId::new(0));
    f.blocks = vec![
        // bb0(n): s0 = 1<<100; i0 = 1; -> bb1(s0, i0)
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I128)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I128,
                    value: Constant::Int(1_i128 << 100),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I128,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(1), ValueId::new(2)],
                }),
            ],
        },
        // bb1(s, i): if i <= n -> bb2 else bb3
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![(ValueId::new(10), Ty::I128), (ValueId::new(11), Ty::I128)],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sle,
                    ty: Ty::I128,
                    lhs: ValueId::new(11),
                    rhs: ValueId::new(0),
                })
                .with_result(ValueId::new(12)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(12),
                    then_target: BlockId::new(2),
                    then_args: vec![],
                    else_target: BlockId::new(3),
                    else_args: vec![],
                }),
            ],
        },
        // bb2: s' = s + i; i' = i + 1; -> bb1(s', i')
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: trust_ir::BinOp::Add,
                    ty: Ty::I128,
                    lhs: ValueId::new(10),
                    rhs: ValueId::new(11),
                })
                .with_result(ValueId::new(20)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I128,
                    value: Constant::Int(1),
                })
                .with_result(ValueId::new(21)),
                InstrNode::new(Inst::BinOp {
                    op: trust_ir::BinOp::Add,
                    ty: Ty::I128,
                    lhs: ValueId::new(11),
                    rhs: ValueId::new(21),
                })
                .with_result(ValueId::new(22)),
                InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![ValueId::new(20), ValueId::new(22)],
                }),
            ],
        },
        // bb3: return s
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(10)],
            })],
        },
    ];
    module.add_function(f);
    module
}

fn compile_to_obj_at(module: &TrustIrModule, opt_level: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("i128/u128 lowering must compile (proof/coverage gate included)");
    assert!(!result.object_code.is_empty());
    result.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>

extern int       _i128_sadd_ovf(__int128 a, __int128 b);
extern int       _i128_ssub_ovf(__int128 a, __int128 b);
extern int       _u128_uadd_ovf(unsigned __int128 a, unsigned __int128 b);
extern int       _u128_usub_ovf(unsigned __int128 a, unsigned __int128 b);
extern __int128  _i128_sadd_val(__int128 a, __int128 b);

int main(void) {
    __int128 IMAX = (((__int128)0x7fffffffffffffffLL) << 64) | (__int128)0xffffffffffffffffULL;
    __int128 IMIN = ((__int128)1) << 127;            /* i128::MIN */
    unsigned __int128 UMAX = ~(unsigned __int128)0;  /* u128::MAX */

    /* signed add */
    if (_i128_sadd_ovf(IMAX, 1) != 1) return 1;      /* MAX + 1 overflows */
    if (_i128_sadd_ovf(5, 7)    != 0) return 2;      /* no overflow */
    if (_i128_sadd_ovf(IMIN, -1) != 1) return 3;     /* MIN + (-1) overflows */
    if (_i128_sadd_ovf(IMAX, IMIN) != 0) return 4;   /* MAX + MIN = -1, no overflow */

    /* signed sub */
    if (_i128_ssub_ovf(IMIN, 1) != 1) return 5;      /* MIN - 1 overflows */
    if (_i128_ssub_ovf(5, 7)    != 0) return 6;      /* no overflow */
    if (_i128_ssub_ovf(IMAX, -1) != 1) return 7;     /* MAX - (-1) overflows */

    /* unsigned add */
    if (_u128_uadd_ovf(UMAX, 1) != 1) return 8;      /* UMAX + 1 wraps */
    if (_u128_uadd_ovf(5, 7)    != 0) return 9;      /* no overflow */

    /* unsigned sub */
    if (_u128_usub_ovf(0, 1) != 1) return 10;        /* 0 - 1 borrows */
    if (_u128_usub_ovf(7, 5) != 0) return 11;        /* no overflow */

    /* wrapped value: MAX + 1 == MIN (mod 2^128) */
    if (_i128_sadd_val(IMAX, 1) != IMIN) return 12;
    if (_i128_sadd_val(100, 23) != 123) return 13;

    printf("i128/u128 checked add/sub overflow: all boundary cases correct\n");
    return 0;
}
"#;

/// Compile `obj`, link against `driver`, run, and return the process exit code
/// (or `None` when this host can't link+run aarch64 Mach-O).
fn link_run_exit_code(tag: &str, obj: &[u8], driver: &str) -> Option<i32> {
    if !can_link_and_run_aarch64_macho() {
        eprintln!("SKIP: link-and-run requires an aarch64-apple-darwin host");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("trust_cg_{tag}_e2e"));
    let _ = fs::create_dir_all(&dir);
    let obj_path = dir.join(format!("{tag}.o"));
    let drv_path = dir.join("driver.c");
    let bin_path = dir.join(format!("{tag}_bin"));
    fs::write(&obj_path, obj).expect("write .o");
    fs::write(&drv_path, driver).expect("write driver");

    let link = Command::new("cc")
        .args([
            drv_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            bin_path.to_str().unwrap(),
        ])
        .output()
        .expect("cc available");
    assert!(
        link.status.success(),
        "link failed:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );

    let run = Command::new(bin_path.to_str().unwrap())
        .output()
        .expect("run binary");
    let code = run.status.code().unwrap_or(-1);
    let _ = fs::remove_dir_all(&dir);
    Some(code)
}

#[test]
fn e2e_aarch64_i128_u128_checked_overflow_add_sub() {
    let module = build_module();
    // Exercise both -O0 (straight bit-pattern decomposition) and -O2 (the same
    // decomposition after the optimizer has run over the i128 ops).
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_to_obj_at(&module, opt);
        let Some(code) = link_run_exit_code("i128_overflow", &obj, DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "i128/u128 checked overflow runtime mismatch at {opt:?} (failing-case code {code})",
        );
    }
}

const UNOP_DRIVER: &str = r#"
#include <stdio.h>

extern __int128 _i128_neg(__int128 a);
extern __int128 _i128_not(__int128 a);
extern __int128 _i128_popcount(__int128 a);

static int popcount_i128(unsigned __int128 a) {
    return __builtin_popcountll((unsigned long long)a)
         + __builtin_popcountll((unsigned long long)(a >> 64));
}

int main(void) {
    __int128 IMIN = ((__int128)1) << 127;            /* i128::MIN */
    unsigned __int128 UMAX = ~(unsigned __int128)0;

    /* negation crosses the 64-bit boundary (borrow propagation) */
    if (_i128_neg(1)  != -1) return 1;
    if (_i128_neg(-1) !=  1) return 2;
    if (_i128_neg(0)  !=  0) return 3;
    if (_i128_neg(((__int128)1) << 64) != -(((__int128)1) << 64)) return 4;
    if (_i128_neg(IMIN) != IMIN) return 5;           /* -MIN wraps to MIN */

    /* bitwise NOT of each half */
    if (_i128_not(0)  != (__int128)UMAX) return 6;   /* ~0 == all ones */
    if (_i128_not(5)  != -6)             return 7;   /* ~x == -x-1 */
    if (_i128_not((__int128)UMAX) != 0)  return 8;

    /* popcount over both 64-bit halves */
    if ((long long)_i128_popcount(0)             != 0)   return 9;
    if ((long long)_i128_popcount((__int128)UMAX) != 128) return 10;
    if ((long long)_i128_popcount(((__int128)1) << 64) != 1) return 11;  /* a bit only in the high half */
    if ((long long)_i128_popcount((__int128)0xF0F0F0F0F0F0F0F0ULL) != 32) return 12;
    {
        unsigned __int128 v = (((unsigned __int128)0x0123456789abcdefULL) << 64)
                            | (unsigned __int128)0xfedcba9876543210ULL;
        if ((long long)_i128_popcount((__int128)v) != popcount_i128(v)) return 13;
    }

    printf("i128 neg/not/popcount: register-pair unary ops correct\n");
    return 0;
}
"#;

const SELECT_DRIVER: &str = r#"
#include <stdio.h>

extern __int128 _i128_min(__int128 a, __int128 b);
extern unsigned __int128 _i128_umin(unsigned __int128 a, unsigned __int128 b);

int main(void) {
    __int128 IMAX = (((__int128)0x7fffffffffffffffLL) << 64) | (__int128)0xffffffffffffffffULL;
    __int128 IMIN = ((__int128)1) << 127;
    unsigned __int128 UMAX = ~(unsigned __int128)0;
    __int128 HI = ((__int128)1) << 64;   /* hi=1, lo=0 — exercises high-half select */

    /* signed min */
    if (_i128_min(5, 7)  != 5)  return 1;
    if (_i128_min(7, 5)  != 5)  return 2;
    if (_i128_min(-3, 2) != -3) return 3;
    if (_i128_min(IMIN, IMAX) != IMIN) return 4;
    if (_i128_min(HI, 1) != 1)  return 5;   /* min must pick lo=1,hi=0, not the larger HI */
    if (_i128_min(1, HI) != 1)  return 6;

    /* unsigned min */
    if (_i128_umin(5, 7)    != 5) return 7;
    if (_i128_umin(UMAX, 1) != 1) return 8;        /* UMAX is huge unsigned */
    if (_i128_umin((unsigned __int128)HI, 1) != 1) return 9;

    printf("i128 register-pair select (min/umin) correct\n");
    return 0;
}
"#;

const LOADSTORE_DRIVER: &str = r#"
#include <stdio.h>

extern __int128 _i128_load(const __int128 *p);
extern void     _i128_store(__int128 *p, __int128 v);

int main(void) {
    __int128 IMIN = ((__int128)1) << 127;
    /* distinct high and low halves — fails if either half is dropped */
    __int128 v = (((__int128)0x0123456789abcdefLL) << 64) | (__int128)0xfedcba9876543210LL;
    __int128 storage = 0;

    _i128_store(&storage, v);
    if (storage != v) return 1;              /* store must write BOTH halves */
    if (_i128_load(&storage) != v) return 2; /* load must read BOTH halves (separate call) */

    _i128_store(&storage, IMIN);
    if (_i128_load(&storage) != IMIN) return 3;
    _i128_store(&storage, -1);
    if (_i128_load(&storage) != -1) return 4;
    _i128_store(&storage, 0);
    if (_i128_load(&storage) != 0) return 5;

    printf("i128 load/store (register-pair memory access) correct\n");
    return 0;
}
"#;

const LOOP_DRIVER: &str = r#"
#include <stdio.h>

extern __int128 _i128_loopsum(__int128 n);

int main(void) {
    __int128 BASE = ((__int128)1) << 100;   /* nonzero high half */
    if (_i128_loopsum(0)  != BASE)        return 1;  /* loop body never runs */
    if (_i128_loopsum(1)  != BASE + 1)    return 2;
    if (_i128_loopsum(10) != BASE + 55)   return 3;  /* 1+..+10 */
    if (_i128_loopsum(100) != BASE + 5050) return 4;
    printf("i128 loop-carried block-arg (register-pair Copy across back-edge) correct\n");
    return 0;
}
"#;

#[test]
fn e2e_aarch64_i128_loop_carried_copy() {
    let module = build_i128_loop_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_to_obj_at(&module, opt);
        let Some(code) = link_run_exit_code("i128_loop", &obj, LOOP_DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "i128 loop-carried copy runtime mismatch at {opt:?} (failing-case code {code})",
        );
    }
}

#[test]
fn e2e_aarch64_i128_load_store_register_pair() {
    let module = build_loadstore_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_to_obj_at(&module, opt);
        let Some(code) = link_run_exit_code("i128_loadstore", &obj, LOADSTORE_DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "i128 load/store runtime mismatch at {opt:?} (failing-case code {code})",
        );
    }
}

#[test]
fn e2e_aarch64_i128_select_register_pair() {
    let module = build_select_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_to_obj_at(&module, opt);
        let Some(code) = link_run_exit_code("i128_select", &obj, SELECT_DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "i128 register-pair select runtime mismatch at {opt:?} (failing-case code {code})",
        );
    }
}

#[test]
fn e2e_aarch64_i128_neg_not() {
    let module = build_unop_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_to_obj_at(&module, opt);
        let Some(code) = link_run_exit_code("i128_unop", &obj, UNOP_DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "i128 neg/not/popcount runtime mismatch at {opt:?} (failing-case code {code})",
        );
    }
}
