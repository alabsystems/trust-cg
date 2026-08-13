// trust-cg-codegen/tests/e2e_aarch64_swift_scalar.rs
//
// Completeness: the SCALAR subset of the `Swift` calling convention. trust-cg
// used to fail-close on every swiftcc function. But on aarch64, Swift's
// convention is byte-for-byte identical to the C register ABI (AAPCS64) for a
// signature whose parameters and (single/absent) return are all non-aggregate,
// single-register scalars -- the Swift-specific registers (self x20, error x21,
// async x22) are engaged ONLY by swiftself/swifterror/swiftasync parameter
// attributes, which trust-ir's ParamAttrs cannot express. This was verified by
// disassembling clang's `__attribute__((swiftcall))` vs `ccc`: identical arg
// registers, identical stack spill past x7/v7, identical scalar returns.
//
// So that subset now lowers via the C ABI. This test proves it end-to-end: a
// clang `ccc` driver calls the trust-cg-compiled swiftcc functions and, because
// the two ABIs coincide for scalars, gets the right answers. Aggregate/i128
// swiftcc signatures (where Swift genuinely diverges -- struct return in x0-x3
// vs sret) stay fail-closed; that is pinned in e2e_aarch64_calling_conv.rs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, CallingConv, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Module as TrustIrModule, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

// swiftcc `fn name(a,b,c,d: i64) -> i64 { a + b*2 + c*3 + d*4 }` -- four integer
// scalars, all in registers.
fn build_swift_add4(m: &mut TrustIrModule) {
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I64; 4],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(0), "sw_add4", ft, BlockId::new(0));
    f.calling_conv = CallingConv::Swift;
    // b*2, c*3, d*4, then sum with a.
    let mul = |lhs: u32, k: u32, out: u32, kval: u32| -> Vec<InstrNode> {
        vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: trust_ir::Constant::Int(kval as i128),
            })
            .with_result(ValueId::new(k)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: ValueId::new(lhs),
                rhs: ValueId::new(k),
            })
            .with_result(ValueId::new(out)),
        ]
    };
    let mut body = Vec::new();
    body.extend(mul(1, 20, 30, 2)); // b*2 -> %30
    body.extend(mul(2, 21, 31, 3)); // c*3 -> %31
    body.extend(mul(3, 22, 32, 4)); // d*4 -> %32
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(0),
            rhs: ValueId::new(30),
        })
        .with_result(ValueId::new(40)),
    );
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(40),
            rhs: ValueId::new(31),
        })
        .with_result(ValueId::new(41)),
    );
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(41),
            rhs: ValueId::new(32),
        })
        .with_result(ValueId::new(42)),
    );
    body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(42)],
    }));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: (0..4).map(|i| (ValueId::new(i), Ty::I64)).collect(),
        body,
    }];
    m.add_function(f);
}

// swiftcc `fn name(a,b,c,d,e,f,g,h,i,j: i64) -> i64 { a + h*8 + i*9 + j*10 }`
// -- ten integer scalars: eight in x0..x7, two spilled to the stack. Verifies
// the register-exhaustion spill matches C.
fn build_swift_add10(m: &mut TrustIrModule) {
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I64; 10],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(1), "sw_add10", ft, BlockId::new(0));
    f.calling_conv = CallingConv::Swift;
    let mut body = Vec::new();
    // h*8 (%7), i*9 (%8), j*10 (%9)
    let terms = [
        (7u32, 8u32, 100u32, 110u32),
        (8, 9, 101, 111),
        (9, 10, 102, 112),
    ];
    for (arg, kval, kid, out) in terms {
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: trust_ir::Constant::Int(kval as i128),
            })
            .with_result(ValueId::new(kid)),
        );
        body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: ValueId::new(arg),
                rhs: ValueId::new(kid),
            })
            .with_result(ValueId::new(out)),
        );
    }
    // a + %110 + %111 + %112
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(0),
            rhs: ValueId::new(110),
        })
        .with_result(ValueId::new(120)),
    );
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(120),
            rhs: ValueId::new(111),
        })
        .with_result(ValueId::new(121)),
    );
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(121),
            rhs: ValueId::new(112),
        })
        .with_result(ValueId::new(122)),
    );
    body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(122)],
    }));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: (0..10).map(|i| (ValueId::new(i), Ty::I64)).collect(),
        body,
    }];
    m.add_function(f);
}

// swiftcc `fn name(a: i128, b: i128) -> i128 { a*b + a }` -- i128 uses aligned
// GPR pairs (x0:x1, x2:x3) and returns in x0:x1, identically under Swift and C
// (verified in-register / spilled / mixed by disassembly).
fn build_swift_i128(m: &mut TrustIrModule) {
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I128, Ty::I128],
        returns: vec![Ty::I128],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(2), "sw_i128", ft, BlockId::new(0));
    f.calling_conv = CallingConv::Swift;
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I128), (ValueId::new(1), Ty::I128)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I128,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I128,
                lhs: ValueId::new(2),
                rhs: ValueId::new(0),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    m.add_function(f);
}

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("swift_scalar");
    build_swift_add4(&mut m);
    build_swift_add10(&mut m);
    build_swift_i128(&mut m);
    m
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Result<Vec<u8>, String> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    compiler
        .compile(module)
        .map(|r| r.object_code)
        .map_err(|e| format!("{e:?}"))
}

// The driver declares the trust-cg functions with the ORDINARY C prototype (no
// swiftcall attribute). Because scalar swiftcc coincides with the C ABI, a plain
// C call must reach them correctly -- that is exactly what proves the coincidence.
const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
extern int64_t sw_add4(int64_t,int64_t,int64_t,int64_t);
extern int64_t sw_add10(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t);
extern __int128 sw_i128(__int128, __int128);
int main(void){
    if (sw_add4(1,2,3,4) != 1 + 2*2 + 3*3 + 4*4) { printf("add4 a\n"); return 1; }
    if (sw_add4(-5,10,-2,7) != -5 + 10*2 + (-2)*3 + 7*4) { printf("add4 b\n"); return 2; }
    if (sw_add10(1,2,3,4,5,6,7,8,9,10) != 1 + 8*8 + 9*9 + 10*10) { printf("add10 a\n"); return 3; }
    if (sw_add10(100,0,0,0,0,0,0,-3,-4,-5) != 100 + (-3)*8 + (-4)*9 + (-5)*10) { printf("add10 b\n"); return 4; }
    // i128 register-pair args (x0:x1, x2:x3) + i128 return (x0:x1).
    {
        __int128 a = ((__int128)0x0123456789ABCDEFll << 64) | 0xFEDCBA9876543210ull;
        __int128 b = 3;
        if (sw_i128(a,b) != a*b + a) { printf("i128 a\n"); return 5; }
        if (sw_i128(-7, 1000000) != (__int128)-7 * 1000000 + -7) { printf("i128 b\n"); return 6; }
    }
    printf("scalar+i128 swiftcc lowers identically to the C register ABI (bit-exact vs clang)\n");
    return 0;
}
"#;

fn link_run(tag: &str, obj: &[u8]) -> Option<i32> {
    if !can_link_and_run_aarch64_macho() {
        eprintln!("SKIP: needs aarch64-apple-darwin");
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
fn e2e_aarch64_swift_scalar_matches_c_abi() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt).expect("scalar swiftcc module must compile");
        let Some(code) = link_run("swift_scalar", &obj) else {
            return;
        };
        assert_eq!(code, 0, "scalar swiftcc / C-ABI mismatch at {opt:?}");
    }
}
