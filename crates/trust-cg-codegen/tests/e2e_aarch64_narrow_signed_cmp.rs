// trust-cg-codegen/tests/e2e_aarch64_narrow_signed_cmp.rs
//
// Regression test for the narrow (i8/i16) signed-comparison silent-miscompile
// class (audit finding U1): `select_cmp` emitted CmpRR directly on operands that
// are NOT canonically sign-extended, so a SIGNED compare of a truncated/loaded
// i16(-1) = 0x0000FFFF was performed as the unsigned value +65535.
//
// The function truncates an i32 arg to i16 (Trunc -> low 16 bits, non-canonical
// upper bits) and signed-compares — this is the exact shape that exposes the bug.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    Block as TrustIrBlock, CastOp, Constant, FuncTy, Function as TrustIrFunction, ICmpOp, Inst,
    InstrNode, InterpretValue, Interpreter, Module as TrustIrModule, OverflowOp, Ty,
};
use trust_ir::{BlockId, FuncId, ValueId};

mod common;
use common::a64_interp::{A64Interp, extract_text, symbol_addrs};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

/// `fn name(a: i32, b: i32) -> i32 { let x = a as NARROW; let y = b as NARROW;
///  (x cmp y) as i32 }` — truncates to the narrow type, then compares.
fn build_trunc_cmp(func_id: u32, name: &str, module: &mut TrustIrModule, narrow: Ty, cmp: ICmpOp) {
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I32), (ValueId::new(1), Ty::I32)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I32,
                dst_ty: narrow.clone(),
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I32,
                dst_ty: narrow.clone(),
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::ICmp {
                op: cmp,
                ty: narrow,
                lhs: ValueId::new(2),
                rhs: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::Select {
                ty: Ty::I32,
                cond: ValueId::new(4),
                then_val: ValueId::new(5),
                else_val: ValueId::new(6),
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(7)],
            }),
        ],
    }];
    module.add_function(f);
}

/// `fn name(a: i32, b: i32) -> i32 { let x = a as NARROW; let y = b as NARROW;
///  x.overflowing_add(y).1 as i32 }` — exposes the narrow checked-overflow class
/// (audit U2/U3): the final overflow Icmp is on narrow operands.
fn build_narrow_add_ovf(func_id: u32, name: &str, module: &mut TrustIrModule, narrow: Ty) {
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I32), (ValueId::new(1), Ty::I32)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I32,
                dst_ty: narrow.clone(),
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I32,
                dst_ty: narrow.clone(),
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Overflow {
                op: OverflowOp::AddOverflow,
                ty: narrow,
                lhs: ValueId::new(2),
                rhs: ValueId::new(3),
            })
            .with_results([ValueId::new(4), ValueId::new(5)]),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::Select {
                ty: Ty::I32,
                cond: ValueId::new(5),
                then_val: ValueId::new(6),
                else_val: ValueId::new(7),
            })
            .with_result(ValueId::new(8)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(8)],
            }),
        ],
    }];
    module.add_function(f);
}

fn build_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("narrow_cmp");
    build_trunc_cmp(0, "_i16_slt", &mut module, Ty::I16, ICmpOp::Slt);
    build_trunc_cmp(1, "_i16_sgt", &mut module, Ty::I16, ICmpOp::Sgt);
    build_trunc_cmp(2, "_i8_slt", &mut module, Ty::I8, ICmpOp::Slt);
    build_trunc_cmp(3, "_i16_ult", &mut module, Ty::U16, ICmpOp::Ult);
    build_trunc_cmp(4, "_i8_ult", &mut module, Ty::U8, ICmpOp::Ult);
    build_narrow_add_ovf(5, "_i8_add_ovf", &mut module, Ty::I8);
    build_narrow_add_ovf(6, "_u8_add_ovf", &mut module, Ty::U8);
    build_narrow_add_ovf(7, "_i16_add_ovf", &mut module, Ty::I16);
    module
}

fn compile_to_obj_at(module: &TrustIrModule, opt_level: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("narrow compare must compile");
    assert!(!result.object_code.is_empty());
    result.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>

extern int _i16_slt(int a, int b);
extern int _i16_sgt(int a, int b);
extern int _i8_slt(int a, int b);
extern int _i16_ult(int a, int b);
extern int _i8_ult(int a, int b);
extern int _i8_add_ovf(int a, int b);
extern int _u8_add_ovf(int a, int b);
extern int _i16_add_ovf(int a, int b);

int main(void) {
    /* low 16 bits = 0xFFFF = i16 -1; low 16 = 0 = i16 0 */
    if (_i16_slt(0xFFFF, 0x0000) != 1) return 1;   /* -1 <s 0  -> true */
    if (_i16_slt(0x0000, 0xFFFF) != 0) return 2;   /*  0 <s -1 -> false */
    if (_i16_sgt(0x0000, 0xFFFF) != 1) return 3;   /*  0 >s -1 -> true */
    /* low 8 bits = 0xFF = i8 -1 */
    if (_i8_slt(0x12FF, 0x3400) != 1) return 4;    /* -1 <s 0 (upper junk ignored) */
    /* unsigned must still be correct */
    if (_i16_ult(0xFFFF, 0x0000) != 0) return 5;   /* 65535 <u 0 -> false */
    if (_i8_ult(0x00FF, 0x0000) != 0) return 6;    /* 255 <u 0 -> false */
    if (_i16_ult(0x0000, 0xFFFF) != 1) return 7;   /* 0 <u 65535 -> true */

    /* narrow checked-overflow (U2/U3): the final overflow Icmp is narrow */
    if (_i8_add_ovf(127, 1)   != 1) return 8;   /* i8  127+1 overflows */
    if (_i8_add_ovf(10, 20)   != 0) return 9;   /* no overflow */
    if (_i8_add_ovf(-128, -1) != 1) return 10;  /* i8  MIN + -1 overflows */
    if (_u8_add_ovf(200, 100) != 1) return 11;  /* u8  200+100=300 wraps */
    if (_u8_add_ovf(100, 50)  != 0) return 12;  /* no overflow */
    if (_i16_add_ovf(32767, 1) != 1) return 13; /* i16 MAX + 1 overflows */
    if (_i16_add_ovf(100, 200) != 0) return 14; /* no overflow */

    printf("narrow i8/i16 compares + checked overflow correct\n");
    return 0;
}
"#;

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

/// Decode + interpret one emitted AArch64 function (`fn(i32,i32)->i32`) on THIS
/// host and return the i32 result. Mach-O prepends a leading underscore to the
/// symbol, so `_i16_slt` is looked up as `__i16_slt`.
fn interp_narrow(obj: &[u8], name: &str, a: i32, b: i32) -> i32 {
    let sym = format!("_{name}");
    let text = extract_text(obj);
    let addrs = symbol_addrs(obj);
    let n_value = *addrs
        .get(&sym)
        .unwrap_or_else(|| panic!("symbol {sym} present in object"));
    let entry = (n_value - text.addr) as usize;
    let mut interp = A64Interp::new(text.bytes);
    interp.set_x(0, a as u32 as u64);
    interp.set_x(1, b as u32 as u64);
    interp
        .run(entry)
        .unwrap_or_else(|e| panic!("interpret {name}: {e:?}")) as u32 as i32
}

/// The faithful `trust_ir::Interpreter` oracle for `name(a, b)` on the module.
fn oracle_narrow(module: &TrustIrModule, name: &str, a: i32, b: i32) -> i32 {
    let func = module
        .function_by_name(name)
        .unwrap_or_else(|| panic!("function {name} in module"));
    let args = [
        InterpretValue::int(Ty::I32, a as i128).unwrap(),
        InterpretValue::int(Ty::I32, b as i128).unwrap(),
    ];
    Interpreter::with_module(module)
        .execute_func(func.id, args)
        .expect("oracle executes")
        .returns[0]
        .as_int()
        .expect("int result")
        .as_signed() as i32
}

/// Fail-CLOSED on-host assertion: interpret every driver case from the emitted
/// AArch64 bytes and require it to match BOTH the faithful trust_ir oracle AND
/// the hand-computed key. This runs on ANY host (including this x86 box), so an
/// AArch64 narrow-compare miscompile can no longer pass green by being skipped.
fn assert_narrow_on_host(module: &TrustIrModule, obj: &[u8], opt: OptLevel) {
    // (name, a, b, key) — the same input/output pairs the C DRIVER checks.
    let cases: &[(&str, i32, i32, i32)] = &[
        ("_i16_slt", 0xFFFF, 0x0000, 1), // -1 <s 0  -> true   (i16(-1)<0 key)
        ("_i16_slt", 0x0000, 0xFFFF, 0), //  0 <s -1 -> false
        ("_i16_sgt", 0x0000, 0xFFFF, 1), //  0 >s -1 -> true
        ("_i8_slt", 0x12FF, 0x3400, 1),  // -1 <s 0 (upper junk ignored)
        ("_i16_ult", 0xFFFF, 0x0000, 0), // 65535 <u 0 -> false
        ("_i8_ult", 0x00FF, 0x0000, 0),  // 255 <u 0 -> false
        ("_i16_ult", 0x0000, 0xFFFF, 1), // 0 <u 65535 -> true
        ("_i8_add_ovf", 127, 1, 1),      // i8 127+1 overflows
        ("_i8_add_ovf", 10, 20, 0),      // no overflow
        ("_i8_add_ovf", -128, -1, 1),    // i8 MIN + -1 overflows
        ("_u8_add_ovf", 200, 100, 1),    // u8 200+100=300 wraps
        ("_u8_add_ovf", 100, 50, 0),     // no overflow
        ("_i16_add_ovf", 32767, 1, 1),   // i16 MAX + 1 overflows
        ("_i16_add_ovf", 100, 200, 0),   // no overflow
    ];
    for &(name, a, b, key) in cases {
        let want = oracle_narrow(module, name, a, b);
        assert_eq!(
            want, key,
            "trust_ir oracle disagrees with key for {name}({a:#x},{b:#x})"
        );
        let got = interp_narrow(obj, name, a, b);
        assert_eq!(
            got, key,
            "AArch64 codegen MISCOMPILE at {opt:?}: {name}({a:#x},{b:#x}) = {got}, want {key}",
        );
    }
}

#[test]
fn e2e_aarch64_narrow_signed_compare() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_to_obj_at(&module, opt);

        // FAIL-CLOSED on-host correctness: decode + interpret the emitted AArch64
        // bytes on THIS host and assert against the faithful oracle + key. This
        // is what converts the previous fail-OPEN cfg!(aarch64) skip into a
        // genuine assertion that runs on x86.
        assert_narrow_on_host(&module, &obj, opt);

        // Additionally link-and-run on a real aarch64 host when available.
        let Some(code) = link_run_exit_code("narrow_cmp", &obj, DRIVER) else {
            continue;
        };
        assert_eq!(
            code, 0,
            "narrow i8/i16 compare miscompiled at {opt:?} (failing-case code {code})",
        );
    }
}
