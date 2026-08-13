// trust-cg-codegen/tests/e2e_aarch64_u128_checked_mul.rs
//
// End-to-end coverage for UNSIGNED u128 checked multiply (`u128::checked_mul` /
// `Inst::Overflow { MulOverflow, U128 }`), previously fail-closed ("need 256-bit
// multiply"). AArch64 FCVTZ... err — the product's high 128 bits aren't needed:
// overflow is detected from the LOW product via a division check,
//   result = a * b (low 128 bits);  flag = (a != 0) && (result / max(a,1) != b)
// which is exact for u128 (floor-division recovers `b` iff no overflow) and
// avoids the __udivti3 divide-by-zero UB. SIGNED i128 checked mul remains
// fail-closed (still needs the SMULH-based 256-bit product).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, OverflowOp, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

// `fn(a: ty, b: ty) -> ret` doing a checked mul over `ty` and returning result[idx].
fn build_checked_mul(
    id: u32,
    name: &str,
    m: &mut TrustIrModule,
    ty: Ty,
    ret: Ty,
    result_idx: usize,
) {
    let ft = m.add_func_type(FuncTy {
        params: vec![ty.clone(), ty.clone()],
        returns: vec![ret.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), ty.clone()), (ValueId::new(1), ty.clone())],
        body: vec![
            InstrNode::new(Inst::Overflow {
                op: OverflowOp::MulOverflow,
                ty,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_results(vec![ValueId::new(2), ValueId::new(3)]),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2 + result_idx as u32)],
            }),
        ],
    }];
    m.add_function(f);
}

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("u128_checked_mul");
    build_checked_mul(0, "umul_lo", &mut m, Ty::U128, Ty::U128, 0); // product
    build_checked_mul(1, "umul_ovf", &mut m, Ty::U128, Ty::Bool, 1); // overflow flag
    m
}

fn build_signed_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("i128_checked_mul");
    build_checked_mul(0, "smul_lo", &mut m, Ty::I128, Ty::I128, 0);
    build_checked_mul(1, "smul_ovf", &mut m, Ty::I128, Ty::Bool, 1);
    m
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    let r = compiler
        .compile(module)
        .expect("u128 checked mul must compile");
    assert!(!r.object_code.is_empty());
    r.object_code
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
typedef unsigned __int128 u128;
extern u128   umul_lo(u128, u128);
extern _Bool  umul_ovf(u128, u128);
int main(void) {
    u128 M = ~(u128)0, B64 = (u128)1 << 64, B127 = (u128)1 << 127;
    struct { u128 a, b; } C[] = {
        {0, M}, {5, 3}, {B64, B64}, {B127, 2}, {B127, 1}, {M, 2}, {M, 1},
        {B64 - 1, B64 - 1}, {B64, B64 - 1}, {(u128)1 << 65, B64}, {7, 0}, {M, M},
        {B64 + 1, B64 + 1},
    };
    for (unsigned i = 0; i < sizeof(C)/sizeof(C[0]); i++) {
        u128 a = C[i].a, b = C[i].b;
        _Bool ref_ovf = (a != 0 && b > M / a);
        u128 ref_lo = a * b; /* __int128 multiply wraps -> low 128 bits */
        if (umul_ovf(a, b) != ref_ovf) return 1;
        if (umul_lo(a, b) != ref_lo)   return 2;
    }
    printf("u128 checked-mul (product + overflow) bit-exact vs __int128 reference\n");
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
            "-O2",
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

const SIGNED_DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
typedef __int128 i128;
extern i128   smul_lo(i128, i128);
extern _Bool  smul_ovf(i128, i128);
int main(void) {
    i128 MIN = (i128)1 << 127, MAX = ~MIN;
    i128 V[] = {
        0, 1, -1, 2, -2, MIN, MAX, MIN + 1, MAX - 1, (i128)1 << 63, -((i128)1 << 63),
        (i128)1 << 100, -((i128)1 << 100), 3, -3, (i128)1 << 126, -((i128)1 << 126),
        5, -5, 1000000, -1000000,
    };
    unsigned n = sizeof(V)/sizeof(V[0]);
    for (unsigned i = 0; i < n; i++) for (unsigned j = 0; j < n; j++) {
        i128 a = V[i], b = V[j], prod;
        _Bool ref_ovf = __builtin_mul_overflow(a, b, &prod); /* ground truth */
        if (smul_ovf(a, b) != ref_ovf) return 1;
        if (smul_lo(a, b)  != prod)    return 2;
    }
    printf("signed i128 checked-mul (product + overflow) matches __builtin_mul_overflow (441 cases)\n");
    return 0;
}
"#;

fn link_run_driver(tag: &str, obj: &[u8], driver: &str) -> Option<i32> {
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
    fs::write(&drv_path, driver).unwrap();
    let link = Command::new("cc")
        .args([
            "-O2",
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
fn e2e_aarch64_u128_checked_multiply() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt);
        let Some(code) = link_run("u128_checked_mul", &obj) else {
            return;
        };
        assert_eq!(
            code, 0,
            "u128 checked-mul mismatch at {opt:?} (case code {code})"
        );
    }
}

#[test]
fn e2e_aarch64_i128_signed_checked_multiply() {
    let module = build_signed_module();
    for opt in [OptLevel::O0, OptLevel::O2] {
        let obj = compile_at(&module, opt);
        let Some(code) = link_run_driver("i128_checked_mul", &obj, SIGNED_DRIVER) else {
            return;
        };
        assert_eq!(
            code, 0,
            "signed i128 checked-mul mismatch at {opt:?} (case code {code})"
        );
    }
}
