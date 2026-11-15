// trust-cg-codegen/tests/e2e_aarch64_indirect_call.rs
//
// Completeness: indirect calls (function pointers) via `Inst::CallIndirect`.
// This is a distinct code path from direct calls -- the callee is a runtime
// value (a `ptr`) rather than a symbol, so the backend must materialize the
// target address into a register and emit `BLR` instead of a `BL` to a fixup.
// It is also the path exercised by the non-C conventions enabled earlier, so
// pinning it guards both.
//
// The test is a native differential check on AArch64 macOS or Linux GNU: the
// host C compiler (clang on macOS, GCC on the Linux floor host), the oracle,
// compiles a driver that passes real C function pointers (`dbl`, `neg`,
// `fma3`) into trust-cg-compiled trampolines `apply1`/`apply3`, which invoke
// them through `call_indirect`. If the address materialization, the BLR, or
// the argument marshalling were wrong, the result would diverge from the
// direct C call the host compiler would have made.
//
// A second module (L04-P11) runs at O0-O3 against direct C computation:
//   * a trust-cg global table of function pointers (four trust-cg functions
//     and one C function, relocated data words) indexed and called in
//     trust-cg, and C-built tables passed in and called by index or folded
//     over in a loop (mixed trust-cg and C callees);
//   * a call whose result feeds a dense switch (a jump table), and a switch
//     whose arms choose the table slot a following indirect call goes through
//     (a function-pointer block parameter);
//   * mixed GPR/FPR arguments and an FP result, nine integer arguments (the
//     ninth on the stack), two dependent calls through the same pointer (the
//     pointer and the input live across the first BLR) and an FP value live
//     across a call; the C callees `c_sub5`/`c_xor` overwrite X1-X17,
//     V0-V7 and V16-V31 (not X18 or the caller-saved upper halves of
//     V8-V15), so a value kept in those registers across a BLR is caught;
//   * a narrow i8 result widened after the call. On AArch64 Linux GNU the C
//     callee also returns garbage above bit 7 (AAPCS64 leaves those bits
//     unspecified; Apple's arm64 ABI makes the callee extend, so that leg is
//     Linux-only).
// Each caller is compiled alone and its decoded code words must contain an
// indirect BLR or BR (never a BL to a named callee), and on Linux GNU
// binutils `objdump` reads the same instructions back from the object.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, CallingConv, CastOp, Constant, FuncTy,
    Function as TrustIrFunction, Global, ICmpOp, Inst, InstrNode, Linkage, Module as TrustIrModule,
    SwitchCase, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

#[path = "common/native_host.rs"]
mod native_host;

const ALL_OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// A qualifying run sets `L04P11_RETAIN_DIR` to keep the compiled objects and
/// C drivers (under `<dir>/<relative>`) for disassembly and hashing.
fn retain(relative: &str, bytes: &[u8]) {
    if let Some(dir) = std::env::var_os("L04P11_RETAIN_DIR") {
        let path = std::path::Path::new(&dir).join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, bytes).unwrap();
    }
}

/// AArch64 Linux GNU (ELF) or macOS (Mach-O): `Compiler::new` derives the
/// host's object format and ABI, and the host `cc` links it.
fn can_link_and_run_aarch64_native() -> bool {
    native_host::NATIVE
}

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("indirect_call");

    // Signature of the *target* being called through the pointer: (i64)->(i64).
    let callee1_sig = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    // apply1(fp: ptr, x: i64) -> i64 { return (*fp)(x) }
    let apply1_sig = m
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut apply1 = TrustIrFunction::new(FuncId::new(0), "apply1", apply1_sig, BlockId::new(0));
    apply1.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(0),
                sig: callee1_sig,
                args: vec![ValueId::new(1)],
                calling_conv: CallingConv::C,
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    m.try_add_function(apply1)
        .expect("Module::try_add_function: test fixture");

    // Signature of the 3-arg target: (i64,i64,i64)->(i64).
    let callee3_sig = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    // apply3(fp: ptr, a,b,c: i64) -> i64 { return (*fp)(a,b,c) }
    let apply3_sig = m
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I64, Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut apply3 = TrustIrFunction::new(FuncId::new(1), "apply3", apply3_sig, BlockId::new(0));
    apply3.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::Ptr),
            (ValueId::new(1), Ty::I64),
            (ValueId::new(2), Ty::I64),
            (ValueId::new(3), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(0),
                sig: callee3_sig,
                args: vec![ValueId::new(1), ValueId::new(2), ValueId::new(3)],
                calling_conv: CallingConv::C,
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(4)],
            }),
        ],
    }];
    m.try_add_function(apply3)
        .expect("Module::try_add_function: test fixture");

    m
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Result<Vec<u8>, String> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed());
    compiler
        .compile(module)
        .map(|r| r.object_code)
        .map_err(|e| format!("{e:?}"))
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
extern int64_t apply1(int64_t (*)(int64_t), int64_t);
extern int64_t apply3(int64_t (*)(int64_t,int64_t,int64_t), int64_t,int64_t,int64_t);
static int64_t dbl(int64_t x){ return 2*x; }
static int64_t neg(int64_t x){ return -x; }
static int64_t fma3(int64_t a,int64_t b,int64_t c){ return a*b+c; }
int main(void){
    if(apply1(dbl,21)!=42){printf("apply1 dbl\n");return 1;}
    if(apply1(neg,7)!=-7){printf("apply1 neg\n");return 2;}
    if(apply1(dbl,-100)!=-200){printf("apply1 dbl neg\n");return 3;}
    if(apply3(fma3,3,5,7)!=22){printf("apply3\n");return 4;}
    if(apply3(fma3,-2,10,4)!=-16){printf("apply3 b\n");return 5;}
    if(apply3(fma3,0,999,42)!=42){printf("apply3 c\n");return 6;}
    printf("indirect calls (function pointers via call_indirect) bit-exact vs clang\n");
    return 0;
}
"#;

fn link_run(tag: &str, obj: &[u8]) -> Option<i32> {
    if !can_link_and_run_aarch64_native() {
        eprintln!("SKIP: needs an AArch64 Linux GNU or macOS host");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("trust_cg_{tag}_e2e"));
    let _ = fs::create_dir_all(&dir);
    let obj_path = dir.join(format!("{tag}.o"));
    let drv_path = dir.join("driver.c");
    let bin_path = dir.join(format!("{tag}_bin"));
    fs::write(&obj_path, obj).unwrap();
    fs::write(&drv_path, DRIVER).unwrap();
    let link = Command::new("cc")
        .args([
            drv_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            bin_path.to_str().unwrap(),
        ])
        .args(native_host::c_math_library_args())
        .output()
        .expect("cc");
    assert!(
        link.status.success(),
        "link:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let code = Command::new(bin_path.to_str().unwrap())
        .output()
        .unwrap()
        .status
        .code()
        .unwrap_or(-1);
    let _ = fs::remove_dir_all(&dir);
    Some(code)
}

#[test]
fn e2e_aarch64_indirect_call_matches_clang() {
    let module = build_module();
    for opt in ALL_OPT_LEVELS {
        let obj = compile_at(&module, opt).expect("indirect-call module must compile");
        let Some(code) = link_run("indirect_call", &obj) else {
            return;
        };
        assert_eq!(code, 0, "indirect-call result mismatch at {opt:?}");
    }
}

// ===========================================================================
// Function-pointer tables, switch/call interplay and call ABI shapes (L04-P11)
// ===========================================================================

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}

fn def(inst: Inst, id: u32) -> InstrNode {
    InstrNode::new(inst).with_result(v(id))
}

fn int(ty: Ty, value: i128, id: u32) -> InstrNode {
    def(
        Inst::Const {
            ty,
            value: Constant::Int(value),
        },
        id,
    )
}

fn ret(id: u32) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: vec![v(id)],
    })
}

fn br(target: u32, args: &[u32]) -> InstrNode {
    InstrNode::new(Inst::Br {
        target: BlockId::new(target),
        args: args.iter().map(|&a| v(a)).collect(),
    })
}

fn block(id: u32, params: &[(u32, Ty)], body: Vec<InstrNode>) -> TrustIrBlock {
    TrustIrBlock {
        id: BlockId::new(id),
        params: params.iter().map(|(p, ty)| (v(*p), ty.clone())).collect(),
        body,
    }
}

fn binop(op: BinOp, lhs: u32, rhs: u32, id: u32) -> InstrNode {
    def(
        Inst::BinOp {
            op,
            ty: Ty::I64,
            lhs: v(lhs),
            rhs: v(rhs),
        },
        id,
    )
}

fn call_indirect(callee: u32, sig: trust_ir::FuncTyId, args: &[u32], id: u32) -> InstrNode {
    def(
        Inst::CallIndirect {
            callee: v(callee),
            sig,
            args: args.iter().map(|&a| v(a)).collect(),
            calling_conv: CallingConv::C,
        },
        id,
    )
}

/// `slot = &tc_ops[index]; *slot` as a function pointer.
fn load_table_slot(table: u32, index: u32, slot: u32, pointer: u32) -> [InstrNode; 2] {
    [
        def(
            Inst::GEP {
                pointee_ty: Ty::Ptr,
                base: v(table),
                indices: vec![v(index)],
                inbounds: true,
            },
            slot,
        ),
        def(
            Inst::Load {
                ty: Ty::Ptr,
                ptr: v(slot),
                volatile: false,
                align: None,
            },
            pointer,
        ),
    ]
}

/// The trust-cg callers of this module and the number of indirect call sites
/// each contains.
const FNPTR_CALLERS: &[(&str, usize)] = &[
    ("dispatch_global", 1),
    ("dispatch_table", 1),
    ("fold_table", 1),
    ("classify_call", 1),
    ("switch_then_call", 1),
    ("apply_mixed", 1),
    ("apply9", 1),
    ("twice", 2),
    ("scale_call", 1),
    ("widen_i8", 1),
];

/// The function-pointer module, restricted to the functions `keep` names
/// (every function when `keep` accepts all). The `tc_ops` table is always
/// present: its slots relocate against `tc_double`, `tc_negate`, `tc_square`,
/// `tc_add7` and the C driver's `c_triple`.
fn build_fnptr_module(keep: &dyn Fn(&str) -> bool) -> TrustIrModule {
    let mut m = TrustIrModule::new("fnptr");
    let ptr_ty = m.add_type(Ty::Ptr).expect("Module::add_type: test fixture");
    m.globals.push(Global {
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        name: "tc_ops".into(),
        ty: Ty::Array(ptr_ty, 5),
        mutable: false,
        initializer: Some(Constant::Aggregate(
            ["tc_double", "tc_negate", "tc_square", "tc_add7", "c_triple"]
                .iter()
                .map(|symbol| Constant::SymbolAddr {
                    symbol: (*symbol).into(),
                    addend: 0,
                })
                .collect(),
        )),
        linkage: Linkage::External,
        tls: None,
        align: Some(8),
    });
    let table = trust_ir::value::GlobalId::new(0);
    let mut sig = |params: Vec<Ty>, returns: Vec<Ty>| {
        m.add_func_type(FuncTy {
            params,
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture")
    };
    let unary = sig(vec![Ty::I64], vec![Ty::I64]);
    let index_x = sig(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
    let table_index_x = sig(vec![Ty::Ptr, Ty::I64, Ty::I64], vec![Ty::I64]);
    let fp_x = sig(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
    let mixed = sig(vec![Ty::F64, Ty::I32, Ty::I64, Ty::F32], vec![Ty::F64]);
    let apply_mixed_sig = sig(
        vec![Ty::Ptr, Ty::F64, Ty::I32, Ty::I64, Ty::F32],
        vec![Ty::F64],
    );
    let nine = sig(vec![Ty::I64; 9], vec![Ty::I64]);
    let apply9_sig = sig(
        std::iter::once(Ty::Ptr).chain(vec![Ty::I64; 9]).collect(),
        vec![Ty::I64],
    );
    let narrow = sig(vec![Ty::I8], vec![Ty::I8]);
    let widen_sig = sig(vec![Ty::Ptr, Ty::I8], vec![Ty::I64]);
    let scale_sig = sig(vec![Ty::Ptr, Ty::I64, Ty::F64], vec![Ty::F64]);

    let mut functions: Vec<(&str, trust_ir::FuncTyId, Vec<TrustIrBlock>)> = vec![
        // tc_double(x) = x + x; tc_negate(x) = 0 - x; tc_square(x) = x * x;
        // tc_add7(x) = x + 7 (all wrapping).
        (
            "tc_double",
            unary,
            vec![block(
                0,
                &[(0, Ty::I64)],
                vec![binop(BinOp::Add, 0, 0, 1), ret(1)],
            )],
        ),
        (
            "tc_negate",
            unary,
            vec![block(
                0,
                &[(0, Ty::I64)],
                vec![int(Ty::I64, 0, 1), binop(BinOp::Sub, 1, 0, 2), ret(2)],
            )],
        ),
        (
            "tc_square",
            unary,
            vec![block(
                0,
                &[(0, Ty::I64)],
                vec![binop(BinOp::Mul, 0, 0, 1), ret(1)],
            )],
        ),
        (
            "tc_add7",
            unary,
            vec![block(
                0,
                &[(0, Ty::I64)],
                vec![int(Ty::I64, 7, 1), binop(BinOp::Add, 0, 1, 2), ret(2)],
            )],
        ),
        // dispatch_global(idx, x) = tc_ops[idx](x)
    ];
    let [slot, pointer] = load_table_slot(2, 0, 3, 4);
    functions.push((
        "dispatch_global",
        index_x,
        vec![block(
            0,
            &[(0, Ty::I64), (1, Ty::I64)],
            vec![
                def(Inst::GlobalAddr { global: table }, 2),
                slot,
                pointer,
                call_indirect(4, unary, &[1], 5),
                ret(5),
            ],
        )],
    ));
    // dispatch_table(table, idx, x) = table[idx](x)
    let [slot, pointer] = load_table_slot(0, 1, 3, 4);
    functions.push((
        "dispatch_table",
        table_index_x,
        vec![block(
            0,
            &[(0, Ty::Ptr), (1, Ty::I64), (2, Ty::I64)],
            vec![slot, pointer, call_indirect(4, unary, &[2], 5), ret(5)],
        )],
    ));
    // fold_table(table, n, x): acc = x; for i in 0..n { acc = table[i](acc) }
    let [slot, pointer] = load_table_slot(0, 4, 7, 8);
    functions.push((
        "fold_table",
        table_index_x,
        vec![
            block(
                0,
                &[(0, Ty::Ptr), (1, Ty::I64), (2, Ty::I64)],
                vec![int(Ty::I64, 0, 3), br(1, &[3, 2])],
            ),
            block(
                1,
                &[(4, Ty::I64), (5, Ty::I64)],
                vec![
                    def(
                        Inst::ICmp {
                            op: ICmpOp::Slt,
                            ty: Ty::I64,
                            lhs: v(4),
                            rhs: v(1),
                        },
                        6,
                    ),
                    InstrNode::new(Inst::CondBr {
                        cond: v(6),
                        then_target: BlockId::new(2),
                        then_args: vec![],
                        else_target: BlockId::new(3),
                        else_args: vec![v(5)],
                    }),
                ],
            ),
            block(
                2,
                &[],
                vec![
                    slot,
                    pointer,
                    call_indirect(8, unary, &[5], 9),
                    int(Ty::I64, 1, 10),
                    binop(BinOp::Add, 4, 10, 11),
                    br(1, &[11, 9]),
                ],
            ),
            block(3, &[(12, Ty::I64)], vec![ret(12)]),
        ],
    ));
    // classify_call(fp, x): switch fp(x) { -2..=5 => 1..=8, default => -1 }
    let mut blocks = vec![block(
        0,
        &[(0, Ty::Ptr), (1, Ty::I64)],
        vec![
            call_indirect(0, unary, &[1], 2),
            InstrNode::new(Inst::Switch {
                value: v(2),
                default: BlockId::new(9),
                default_args: vec![],
                cases: (-2..=5)
                    .enumerate()
                    .map(|(i, key)| SwitchCase {
                        value: Constant::Int(key),
                        target: BlockId::new(i as u32 + 1),
                        args: vec![],
                    })
                    .collect(),
                exhaustive_enum_unreachable: false,
            }),
        ],
    )];
    for i in 0..8u32 {
        blocks.push(block(
            i + 1,
            &[],
            vec![int(Ty::I64, i128::from(i) + 1, 10 + i), ret(10 + i)],
        ));
    }
    blocks.push(block(9, &[], vec![int(Ty::I64, -1, 20), ret(20)]));
    functions.push(("classify_call", fp_x, blocks));
    // switch_then_call(k, x): k in 0..=3 picks tc_ops slot [2, 0, 4, 1] (the
    // pointer reaches the call as a block argument); otherwise -1.
    let mut blocks = vec![block(
        0,
        &[(0, Ty::I64), (1, Ty::I64)],
        vec![InstrNode::new(Inst::Switch {
            value: v(0),
            default: BlockId::new(5),
            default_args: vec![],
            cases: (0..4)
                .map(|k| SwitchCase {
                    value: Constant::Int(k),
                    target: BlockId::new(k as u32 + 1),
                    args: vec![],
                })
                .collect(),
            exhaustive_enum_unreachable: false,
        })],
    )];
    for (k, slot_index) in [2i128, 0, 4, 1].into_iter().enumerate() {
        let base = 10 + 4 * k as u32;
        let [slot, pointer] = load_table_slot(base, base + 1, base + 2, base + 3);
        blocks.push(block(
            k as u32 + 1,
            &[],
            vec![
                def(Inst::GlobalAddr { global: table }, base),
                int(Ty::I64, slot_index, base + 1),
                slot,
                pointer,
                br(6, &[base + 3]),
            ],
        ));
    }
    blocks.push(block(5, &[], vec![int(Ty::I64, -1, 30), ret(30)]));
    blocks.push(block(
        6,
        &[(31, Ty::Ptr)],
        vec![call_indirect(31, unary, &[1], 32), ret(32)],
    ));
    functions.push(("switch_then_call", index_x, blocks));
    // apply_mixed(fp, a, b, c, d) = fp(a, b, c, d)
    functions.push((
        "apply_mixed",
        apply_mixed_sig,
        vec![block(
            0,
            &[
                (0, Ty::Ptr),
                (1, Ty::F64),
                (2, Ty::I32),
                (3, Ty::I64),
                (4, Ty::F32),
            ],
            vec![call_indirect(0, mixed, &[1, 2, 3, 4], 5), ret(5)],
        )],
    ));
    // apply9(fp, a1..a9) = fp(a1..a9): a9 is a stack argument both ways.
    let mut params = vec![(0, Ty::Ptr)];
    params.extend((1..=9).map(|p| (p, Ty::I64)));
    functions.push((
        "apply9",
        apply9_sig,
        vec![block(
            0,
            &params,
            vec![
                call_indirect(0, nine, &[1, 2, 3, 4, 5, 6, 7, 8, 9], 10),
                ret(10),
            ],
        )],
    ));
    // twice(fp, x) = fp(fp(x)) + x: fp and x stay live across the first call.
    functions.push((
        "twice",
        fp_x,
        vec![block(
            0,
            &[(0, Ty::Ptr), (1, Ty::I64)],
            vec![
                call_indirect(0, unary, &[1], 2),
                call_indirect(0, unary, &[2], 3),
                binop(BinOp::Add, 3, 1, 4),
                ret(4),
            ],
        )],
    ));
    // scale_call(fp, x, s) = (f64)fp(x) * s: s stays live across the call.
    functions.push((
        "scale_call",
        scale_sig,
        vec![block(
            0,
            &[(0, Ty::Ptr), (1, Ty::I64), (2, Ty::F64)],
            vec![
                call_indirect(0, unary, &[1], 3),
                def(
                    Inst::Cast {
                        op: CastOp::SIToFP,
                        src_ty: Ty::I64,
                        dst_ty: Ty::F64,
                        operand: v(3),
                    },
                    4,
                ),
                def(
                    Inst::BinOp {
                        op: BinOp::FMul,
                        ty: Ty::F64,
                        lhs: v(4),
                        rhs: v(2),
                    },
                    5,
                ),
                ret(5),
            ],
        )],
    ));
    // widen_i8(fp, x) = sext64(fp(x)) with an i8 result.
    functions.push((
        "widen_i8",
        widen_sig,
        vec![block(
            0,
            &[(0, Ty::Ptr), (1, Ty::I8)],
            vec![
                call_indirect(0, narrow, &[1], 2),
                def(
                    Inst::Cast {
                        op: CastOp::SExt,
                        src_ty: Ty::I8,
                        dst_ty: Ty::I64,
                        operand: v(2),
                    },
                    3,
                ),
                ret(3),
            ],
        )],
    ));

    let mut next_id = 0;
    for (name, ft, blocks) in functions {
        if !keep(name) {
            continue;
        }
        let mut f = TrustIrFunction::new(FuncId::new(next_id), name, ft, BlockId::new(0));
        f.blocks = blocks;
        m.try_add_function(f)
            .expect("Module::try_add_function: test fixture");
        next_id += 1;
    }
    m
}

/// The C driver for the function-pointer module. `dirty_narrow_return` adds
/// the AAPCS64 leg whose i8 callee returns garbage above bit 7.
fn fnptr_driver(dirty_narrow_return: bool) -> String {
    let mut c = String::from(
        r#"#include <stdio.h>
#include <stdint.h>
typedef int64_t (*unary_fn)(int64_t);
typedef double (*mixed_fn)(double, int32_t, int64_t, float);
typedef int64_t (*nine_fn)(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t,
                           int64_t, int64_t);
typedef int8_t (*i8_fn)(int8_t);
extern int64_t tc_double(int64_t);
extern int64_t tc_negate(int64_t);
extern int64_t tc_square(int64_t);
extern int64_t tc_add7(int64_t);
extern int64_t dispatch_global(int64_t, int64_t);
extern int64_t dispatch_table(const unary_fn *, int64_t, int64_t);
extern int64_t fold_table(const unary_fn *, int64_t, int64_t);
extern int64_t classify_call(unary_fn, int64_t);
extern int64_t switch_then_call(int64_t, int64_t);
extern double apply_mixed(mixed_fn, double, int32_t, int64_t, float);
extern int64_t apply9(nine_fn, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t,
                      int64_t, int64_t);
extern int64_t twice(unary_fn, int64_t);
extern double scale_call(unary_fn, int64_t, double);
extern int64_t widen_i8(i8_fn, int8_t);

/* Overwrite the AAPCS64 caller-saved X1-X17, V0-V7 and V16-V31, and NZCV
   (not X18 or the caller-saved upper halves of V8-V15): a caller that keeps
   a live value there across the call reads garbage afterwards. */
#define CLOBBER_CALLER_SAVED() __asm__ volatile(                                  \
    "mov x1, #0x5a5a\n\tmov x2, #0x5a5a\n\tmov x3, #0x5a5a\n\tmov x4, #0x5a5a\n\t" \
    "mov x5, #0x5a5a\n\tmov x6, #0x5a5a\n\tmov x7, #0x5a5a\n\tmov x8, #0x5a5a\n\t" \
    "mov x9, #0x5a5a\n\tmov x10, #0x5a5a\n\tmov x11, #0x5a5a\n\tmov x12, #0x5a5a\n\t" \
    "mov x13, #0x5a5a\n\tmov x14, #0x5a5a\n\tmov x15, #0x5a5a\n\tmov x16, #0x5a5a\n\t" \
    "mov x17, #0x5a5a\n\tcmp x1, #0\n\t"                                           \
    "movi v0.16b, #0xa5\n\tmovi v1.16b, #0xa5\n\tmovi v2.16b, #0xa5\n\t"          \
    "movi v3.16b, #0xa5\n\tmovi v4.16b, #0xa5\n\tmovi v5.16b, #0xa5\n\t"          \
    "movi v6.16b, #0xa5\n\tmovi v7.16b, #0xa5\n\tmovi v16.16b, #0xa5\n\t"         \
    "movi v17.16b, #0xa5\n\tmovi v18.16b, #0xa5\n\tmovi v19.16b, #0xa5\n\t"       \
    "movi v20.16b, #0xa5\n\tmovi v21.16b, #0xa5\n\tmovi v22.16b, #0xa5\n\t"       \
    "movi v23.16b, #0xa5\n\tmovi v24.16b, #0xa5\n\tmovi v25.16b, #0xa5\n\t"       \
    "movi v26.16b, #0xa5\n\tmovi v27.16b, #0xa5\n\tmovi v28.16b, #0xa5\n\t"       \
    "movi v29.16b, #0xa5\n\tmovi v30.16b, #0xa5\n\tmovi v31.16b, #0xa5\n\t"       \
    ::: "x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", \
        "x13", "x14", "x15", "x16", "x17", "v0", "v1", "v2", "v3", "v4", "v5",     \
        "v6", "v7", "v16", "v17", "v18", "v19", "v20", "v21", "v22", "v23", "v24", \
        "v25", "v26", "v27", "v28", "v29", "v30", "v31", "cc", "memory")

/* tc_ops[4] relocates against this definition. */
int64_t c_triple(int64_t x) { return (int64_t)((uint64_t)x * 3u); }
static int64_t c_sub5(int64_t x) {
    CLOBBER_CALLER_SAVED();
    return (int64_t)((uint64_t)x - 5u);
}
static int64_t c_xor(int64_t x) {
    CLOBBER_CALLER_SAVED();
    return x ^ 0x5a5a;
}
static int64_t r_double(int64_t x) { return (int64_t)((uint64_t)x * 2u); }
static int64_t r_negate(int64_t x) { return (int64_t)(0u - (uint64_t)x); }
static int64_t r_square(int64_t x) { return (int64_t)((uint64_t)x * (uint64_t)x); }
static int64_t r_add7(int64_t x) { return (int64_t)((uint64_t)x + 7u); }
static const unary_fn global_ref[5] = {r_double, r_negate, r_square, r_add7, c_triple};
static const int slot_of_k[4] = {2, 0, 4, 1};
/* One out-of-line oracle, built without FP contraction, serves both sides. */
__attribute__((noinline)) static double mix(double a, int32_t b, int64_t c, float d) {
    return a * b + (double)c - d;
}
static int64_t sum9(int64_t a1, int64_t a2, int64_t a3, int64_t a4, int64_t a5, int64_t a6,
                    int64_t a7, int64_t a8, int64_t a9) {
    return (int64_t)((uint64_t)a1 + 2u * (uint64_t)a2 + 3u * (uint64_t)a3 + 4u * (uint64_t)a4
                     + 5u * (uint64_t)a5 + 6u * (uint64_t)a6 + 7u * (uint64_t)a7
                     + 8u * (uint64_t)a8 + 9u * (uint64_t)a9);
}
static int8_t clean_i8(int8_t x) { return (int8_t)(uint8_t)((uint8_t)x * 3u); }
static uint64_t dirty_i8(uint64_t x) {
    return UINT64_C(0xDEADBEEF12345600) ^ ((x << 8) & UINT64_C(0xFF00))
        | (uint8_t)((uint8_t)x * 3u);
}
static int64_t r_classify(int64_t r) { return (r >= -2 && r <= 5) ? r + 3 : -1; }

static long checks = 0, bad = 0;
static void check(const char *label, long long x, long long got, long long want) {
    checks++;
    if (got != want) {
        if (bad < 24) printf("%s x=%lld got=%lld want=%lld\n", label, x, got, want);
        bad++;
    }
}

int main(void) {
    static const int64_t xs[] = {0, 1, -1, 2, 5, 7, -7, 100, -100, 12345, -54321,
                                 0x7fffffff, -0x80000000LL, INT64_MAX, INT64_MIN,
                                 0x123456789LL};
    const unary_fn mixed_table[6] = {tc_square, c_sub5, tc_negate, c_xor, tc_add7, tc_double};
    const unary_fn mixed_ref[6] = {r_square, c_sub5, r_negate, c_xor, r_add7, r_double};
    for (unsigned i = 0; i < sizeof xs / sizeof xs[0]; i++) {
        int64_t x = xs[i];
        for (int idx = 0; idx < 5; idx++)
            check("dispatch_global", x, dispatch_global(idx, x), global_ref[idx](x));
        for (int idx = 0; idx < 6; idx++)
            check("dispatch_table", x, dispatch_table(mixed_table, idx, x), mixed_ref[idx](x));
        for (int n = 0; n <= 6; n++) {
            int64_t acc = x;
            for (int j = 0; j < n; j++) acc = mixed_ref[j](acc);
            check("fold_table", x, fold_table(mixed_table, n, x), acc);
        }
        check("twice tc_square", x, twice(tc_square, x),
              (int64_t)((uint64_t)r_square(r_square(x)) + (uint64_t)x));
        check("twice c_sub5", x, twice(c_sub5, x),
              (int64_t)((uint64_t)c_sub5(c_sub5(x)) + (uint64_t)x));
        static const double scales[2] = {1.5, -0.25};
        for (int s = 0; s < 2; s++) {
            double got = scale_call(c_xor, x, scales[s]);
            double want = (double)c_xor(x) * scales[s];
            check("scale_call c_xor", x, got != want, 0);
            got = scale_call(tc_add7, x, scales[s]);
            want = (double)r_add7(x) * scales[s];
            check("scale_call tc_add7", x, got != want, 0);
        }
        for (int k = -3; k <= 6; k++)
            check("switch_then_call", x, switch_then_call(k, x),
                  (k >= 0 && k < 4) ? global_ref[slot_of_k[k]](x) : -1);
    }
    const unary_fn classifiers[4] = {c_sub5, tc_add7, tc_negate, tc_double};
    const unary_fn classifier_ref[4] = {c_sub5, r_add7, r_negate, r_double};
    for (int64_t x = -20; x <= 20; x++)
        for (int f = 0; f < 4; f++)
            check("classify_call", x, classify_call(classifiers[f], x),
                  r_classify(classifier_ref[f](x)));
    static const double as[] = {0.0, 1.5, -2.25, 1e300, -3.0e-300};
    static const int32_t bs[] = {0, 1, -7, 2147483647, INT32_MIN};
    static const int64_t cs[] = {0, 3, -1, INT64_MAX, -1234567890123LL};
    static const float ds[] = {0.0f, 0.5f, -8.0f, 3.4e38f};
    for (unsigned a = 0; a < 5; a++)
        for (unsigned b = 0; b < 5; b++)
            for (unsigned c = 0; c < 5; c++)
                for (unsigned d = 0; d < 4; d++) {
                    double got = apply_mixed(mix, as[a], bs[b], cs[c], ds[d]);
                    double want = mix(as[a], bs[b], cs[c], ds[d]);
                    checks++;
                    if (got != want && !(got != got && want != want)) {
                        if (bad < 24) printf("apply_mixed %u %u %u %u: %a vs %a\n", a, b, c, d,
                                             got, want);
                        bad++;
                    }
                }
    for (unsigned i = 0; i < sizeof xs / sizeof xs[0]; i++) {
        int64_t x = xs[i];
        check("apply9", x, apply9(sum9, x, 1, -2, 3, -4, 5, -6, 7, x ^ 0x55),
              sum9(x, 1, -2, 3, -4, 5, -6, 7, x ^ 0x55));
        check("apply9 ninth", x, apply9(sum9, 0, 0, 0, 0, 0, 0, 0, 0, x), sum9(0, 0, 0, 0, 0, 0,
                                                                              0, 0, x));
    }
    for (int x = -128; x <= 127; x++) {
        check("widen_i8", x, widen_i8(clean_i8, (int8_t)x), (int64_t)clean_i8((int8_t)x));
"#,
    );
    if dirty_narrow_return {
        c.push_str(
            "        check(\"widen_i8 dirty return\", x, widen_i8((i8_fn)dirty_i8, (int8_t)x),\n\
             \x20             (int64_t)clean_i8((int8_t)x));\n",
        );
    }
    c.push_str(
        r#"    }
    printf("indirect calls: %ld checks, %ld mismatches\n", checks, bad);
    return bad != 0;
}
"#,
    );
    c
}

/// Instruction-word counts of one compiled function: `BLR Xn`, `BR Xn` and
/// `BL label`, decoded here from the Arm ARM encodings.
fn call_word_counts(words: &[u32]) -> (usize, usize, usize) {
    let blr = words
        .iter()
        .filter(|&&w| w & 0xFFFF_FC1F == 0xD63F_0000)
        .count();
    let br = words
        .iter()
        .filter(|&&w| w & 0xFFFF_FC1F == 0xD61F_0000)
        .count();
    let bl = words
        .iter()
        .filter(|&&w| w & 0xFC00_0000 == 0x9400_0000)
        .count();
    (blr, br, bl)
}

/// Every caller of the function-pointer module agrees with direct C
/// computation at O0-O3; every indirect call site stays an indirect branch.
#[test]
fn e2e_aarch64_indirect_call_tables_and_switch_interplay_match_c_at_every_opt_level() {
    if !can_link_and_run_aarch64_native() {
        eprintln!("SKIP: needs an AArch64 Linux GNU or macOS host");
        return;
    }
    let module = build_fnptr_module(&|_| true);
    let driver = fnptr_driver(native_host::LINUX_GNU);
    let dir = std::env::temp_dir().join(format!("trust_cg_fnptr_{}_e2e", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let drv_path = dir.join("driver.c");
    fs::write(&drv_path, &driver).unwrap();
    retain("indirect_call/driver.c", driver.as_bytes());
    let mut total_checks = 0u64;
    for opt in ALL_OPT_LEVELS {
        let obj = compile_at(&module, opt)
            .unwrap_or_else(|error| panic!("fnptr module must compile at {opt:?}: {error}"));
        native_host::assert_native_object(&obj);
        retain(&format!("indirect_call/fnptr_{opt:?}.o"), &obj);
        let obj_path = dir.join(format!("fnptr_{opt:?}.o"));
        let bin_path = dir.join(format!("fnptr_{opt:?}"));
        fs::write(&obj_path, &obj).unwrap();
        let link = Command::new("cc")
            .args(["-O1", "-w", "-ffp-contract=off"])
            .arg(&drv_path)
            .arg(&obj_path)
            .arg("-o")
            .arg(&bin_path)
            .args(native_host::c_math_library_args())
            .output()
            .expect("cc");
        assert!(
            link.status.success(),
            "link at {opt:?}:\n{}",
            String::from_utf8_lossy(&link.stderr)
        );
        let run = Command::new(&bin_path).output().unwrap();
        let stdout = String::from_utf8_lossy(&run.stdout).into_owned();
        assert_eq!(
            run.status.code(),
            Some(0),
            "indirect-call mismatch at {opt:?}:\n{stdout}"
        );
        let checks: u64 = stdout
            .split("indirect calls: ")
            .nth(1)
            .and_then(|rest| rest.split_whitespace().next())
            .and_then(|n| n.parse().ok())
            .unwrap_or_else(|| panic!("no check count at {opt:?}:\n{stdout}"));
        // 16 inputs x 34 table/fold/twice/scale/switch checks, 41 x 4
        // classify, 500 mixed, 32 nine-argument and 256 (Linux: 512) narrow.
        let expected = if native_host::LINUX_GNU { 1752 } else { 1496 };
        assert_eq!(
            checks, expected,
            "unexpected check count at {opt:?}: {stdout}"
        );
        total_checks += checks;

        if native_host::LINUX_GNU {
            let out = Command::new("objdump")
                .args(["-d", "--no-show-raw-insn"])
                .arg(&obj_path)
                .output()
                .expect("binutils objdump is required on the Linux floor host");
            assert!(out.status.success());
            let text = String::from_utf8(out.stdout).unwrap();
            for &(caller, sites) in FNPTR_CALLERS {
                let header = format!("<{caller}>:");
                let body: Vec<&str> = text
                    .split_once(&header)
                    .unwrap_or_else(|| panic!("objdump has no {header} at {opt:?}"))
                    .1
                    .split("\n\n")
                    .next()
                    .unwrap()
                    .lines()
                    .filter_map(|line| line.split_once(":\t"))
                    .map(|(_, insn)| insn.split_whitespace().next().unwrap_or(""))
                    .collect();
                let indirect = body.iter().filter(|m| **m == "blr" || **m == "br").count();
                assert!(
                    indirect >= sites && !body.contains(&"bl"),
                    "objdump: {caller} at {opt:?} has {indirect} indirect branches for \
                     {sites} call sites: {body:?}"
                );
            }
        }
        for &(caller, sites) in FNPTR_CALLERS {
            let single = build_fnptr_module(&|name| name == caller);
            let obj = compile_at(&single, opt)
                .unwrap_or_else(|error| panic!("{caller} must compile at {opt:?}: {error}"));
            let (blr, br, bl) = call_word_counts(&native_host::text_words(&obj));
            assert!(
                blr + br >= sites && bl == 0,
                "{caller} at {opt:?}: BLR {blr}, BR {br}, BL {bl} for {sites} indirect sites"
            );
        }
    }
    let _ = fs::remove_dir_all(&dir);
    println!(
        "indirect calls on {}: {} callers x O0-O3, {total_checks} checks",
        native_host::HOST,
        FNPTR_CALLERS.len()
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
