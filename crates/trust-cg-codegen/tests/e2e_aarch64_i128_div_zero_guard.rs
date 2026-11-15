// trust-cg-codegen/tests/e2e_aarch64_i128_div_zero_guard.rs
//
// End-to-end coverage for the division-by-zero guard of a 128-bit divisor.
//
// A div/rem node carrying `DivNonZero` lowers to `GuardDivZero [divisor]`
// ahead of the division. An i128 divisor is a `(lo, hi)` register pair, so
// the guard's runtime zero test must read both halves: a divisor whose low
// word is zero (`1 << 64`, `3 << 64`, `-(1 << 64)`, `i128::MIN`) is nonzero.
// A carrier that tested the low half alone trapped (BRK #1, SIGTRAP) on those
// well-defined divisions. Here every function carries `DivNonZero` explicitly,
// so each one emits the guard, and the C driver checks every result against
// the `__int128` reference. Constant divisors elide the guard in ISel; runtime
// divisors keep a carrier that tests `lo | hi`, and a runtime divisor that IS
// zero must still trap in that carrier (SIGTRAP) before the libcall runs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::inst::BinOp;
use trust_ir::{
    Block as TrustIrBlock, Constant, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, ProofAnnotation, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

#[path = "common/native_host.rs"]
mod native_host;

/// The trust-ir spelling of a 128-bit constant of `ty`.
fn constant(ty: &Ty, pattern: u128) -> Constant {
    match ty {
        Ty::U128 if pattern > i128::MAX as u128 => Constant::U128(pattern),
        _ => Constant::Int(pattern as i128),
    }
}

/// `fn name(a: ty) -> ty { a <op> K }` with the division annotated `DivNonZero`.
fn build_const_divisor(m: &mut TrustIrModule, id: u32, name: &str, op: BinOp, ty: Ty, k: u128) {
    let ft = m
        .add_func_type(FuncTy {
            params: vec![ty.clone()],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), ty.clone())],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: constant(&ty, k),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::BinOp {
                op,
                ty,
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
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
}

/// `fn name(a: ty, b: ty) -> ty { a <op> b }` with the division annotated `DivNonZero`.
fn build_runtime_divisor(m: &mut TrustIrModule, id: u32, name: &str, op: BinOp, ty: Ty) {
    let ft = m
        .add_func_type(FuncTy {
            params: vec![ty.clone(), ty.clone()],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), ty.clone()), (ValueId::new(1), ty.clone())],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op,
                ty,
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
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
}

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("i128_div_zero_guard");
    let neg_2p64 = (-(1i128 << 64)) as u128;
    let min = i128::MIN as u128;
    let consts: [(&str, BinOp, Ty, u128); 9] = [
        ("udiv_3x2p64", BinOp::UDiv, Ty::U128, 3u128 << 64),
        ("urem_3x2p64", BinOp::URem, Ty::U128, 3u128 << 64),
        (
            "udiv_top_bit",
            BinOp::UDiv,
            Ty::U128,
            (1u128 << 127) | (1u128 << 64),
        ),
        ("sdiv_2p64", BinOp::SDiv, Ty::I128, 1u128 << 64),
        ("srem_2p64", BinOp::SRem, Ty::I128, 1u128 << 64),
        ("sdiv_neg_2p64", BinOp::SDiv, Ty::I128, neg_2p64),
        ("srem_neg_2p64", BinOp::SRem, Ty::I128, neg_2p64),
        ("sdiv_min", BinOp::SDiv, Ty::I128, min),
        ("srem_min", BinOp::SRem, Ty::I128, min),
    ];
    let mut id = 0;
    for (name, op, ty, k) in consts {
        build_const_divisor(&mut m, id, name, op, ty, k);
        id += 1;
    }
    for (name, op, ty) in [
        ("udiv_rt", BinOp::UDiv, Ty::U128),
        ("urem_rt", BinOp::URem, Ty::U128),
        ("sdiv_rt", BinOp::SDiv, Ty::I128),
        ("srem_rt", BinOp::SRem, Ty::I128),
    ] {
        build_runtime_divisor(&mut m, id, name, op, ty);
        id += 1;
    }
    m
}

/// Each failing check returns its own exit code; a guard that traps on a
/// nonzero divisor ends the process on SIGTRAP instead. With an argument, the
/// driver divides by a runtime ZERO through the named function instead: the
/// guard must end the process on SIGTRAP, and exit code 99 means it did not.
const DRIVER: &str = r#"
#include <stdio.h>
typedef unsigned __int128 u128;
typedef __int128 i128;
extern u128 udiv_3x2p64(u128);
extern u128 urem_3x2p64(u128);
extern u128 udiv_top_bit(u128);
extern i128 sdiv_2p64(i128);
extern i128 srem_2p64(i128);
extern i128 sdiv_neg_2p64(i128);
extern i128 srem_neg_2p64(i128);
extern i128 sdiv_min(i128);
extern i128 srem_min(i128);
extern u128 udiv_rt(u128, u128);
extern u128 urem_rt(u128, u128);
extern i128 sdiv_rt(i128, i128);
extern i128 srem_rt(i128, i128);
int main(int argc, char **argv) {
    if (argc > 1) {
        u128 uq = 0;
        i128 iq = 0;
        switch (argv[1][0]) {
        case 'u': uq = udiv_rt(1, 0); break;
        case 'r': uq = urem_rt(1, 0); break;
        case 's': iq = sdiv_rt(1, 0); break;
        case 'm': iq = srem_rt(1, 0); break;
        default: return 98;
        }
        printf("zero divisor did not trap: %llu %lld\n", (unsigned long long)uq, (long long)iq);
        return 99;
    }
    const u128 B64 = (u128)1 << 64, UMAX = ~(u128)0;
    const i128 MIN = (i128)((u128)1 << 127), MAX = ~MIN;
    const u128 UA[] = {0, 1, 7 * B64, 7 * B64 + 9, 3 * B64 - 1, UMAX, (u128)1 << 127};
    const i128 IA[] = {0, 1, -1, (i128)5 << 64, -(((i128)5 << 64) + 9), MAX, MIN + 1, MIN};
    const u128 UD[] = {B64, 3 * B64, B64 + 1, 7, UMAX, (u128)1 << 127};
    const i128 ID[] = {(i128)1 << 64, -((i128)1 << 64), MIN, -7, MAX, (i128)3 << 64};
    const u128 K3 = 3 * B64, KTOP = ((u128)1 << 127) | B64;
    const i128 K1 = (i128)1 << 64, KN = -((i128)1 << 64);
    unsigned n = 0;
    for (unsigned i = 0; i < sizeof(UA) / sizeof(UA[0]); i++) {
        u128 a = UA[i];
        if (udiv_3x2p64(a) != a / K3) return 10;
        if (urem_3x2p64(a) != a % K3) return 11;
        if (udiv_top_bit(a) != a / KTOP) return 12;
        for (unsigned j = 0; j < sizeof(UD) / sizeof(UD[0]); j++) {
            if (udiv_rt(a, UD[j]) != a / UD[j]) return 20;
            if (urem_rt(a, UD[j]) != a % UD[j]) return 21;
            n += 2;
        }
        n += 3;
    }
    for (unsigned i = 0; i < sizeof(IA) / sizeof(IA[0]); i++) {
        i128 a = IA[i];
        if (sdiv_2p64(a) != a / K1) return 30;
        if (srem_2p64(a) != a % K1) return 31;
        if (sdiv_neg_2p64(a) != a / KN) return 32;
        if (srem_neg_2p64(a) != a % KN) return 33;
        if (sdiv_min(a) != a / MIN) return 34;
        if (srem_min(a) != a % MIN) return 35;
        for (unsigned j = 0; j < sizeof(ID) / sizeof(ID[0]); j++) {
            if (sdiv_rt(a, ID[j]) != a / ID[j]) return 40;
            if (srem_rt(a, ID[j]) != a % ID[j]) return 41;
            n += 2;
        }
        n += 6;
    }
    printf("i128 div-zero guard: %u results match the __int128 reference\n", n);
    return 0;
}
"#;

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed());
    let result = compiler.compile(module).unwrap_or_else(|error| {
        panic!("the i128 division module must compile at {opt:?}: {error:?}")
    });
    assert!(!result.object_code.is_empty());
    result.object_code
}

/// The driver argument for each zero-divisor run, and the function it divides
/// through.
const ZERO_DIVISOR_RUNS: [(&str, &str); 4] = [
    ("u", "udiv_rt"),
    ("r", "urem_rt"),
    ("s", "sdiv_rt"),
    ("m", "srem_rt"),
];

/// The signal `BRK #1` raises on AArch64 Linux and macOS.
const SIGTRAP: i32 = 5;

#[cfg(unix)]
fn signal_of(status: &std::process::ExitStatus) -> Option<i32> {
    use std::os::unix::process::ExitStatusExt;
    status.signal()
}

#[cfg(not(unix))]
fn signal_of(_: &std::process::ExitStatus) -> Option<i32> {
    None
}

/// Link `obj` with the driver and run it once per argument list; `None` on a
/// host that cannot run it.
fn link_run(tag: &str, obj: &[u8], runs: &[Vec<&str>]) -> Option<Vec<std::process::Output>> {
    if !native_host::NATIVE {
        eprintln!("SKIP: needs an AArch64 Linux GNU or macOS host");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("trust_cg_{tag}_{}_e2e", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create workdir");
    let obj_path = dir.join(format!("{tag}.o"));
    let drv_path = dir.join("driver.c");
    let bin_path = dir.join(format!("{tag}_bin"));
    fs::write(&obj_path, obj).expect("write object");
    fs::write(&drv_path, DRIVER).expect("write driver");
    let link = Command::new("cc")
        .args(["-O2"])
        .arg(&drv_path)
        .arg(&obj_path)
        .arg("-o")
        .arg(&bin_path)
        .args(native_host::c_math_library_args())
        .output()
        .expect("spawn cc");
    assert!(
        link.status.success(),
        "link:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let outputs = runs
        .iter()
        .map(|args| {
            Command::new(&bin_path)
                .args(args)
                .output()
                .expect("run the driver")
        })
        .collect();
    let _ = fs::remove_dir_all(&dir);
    Some(outputs)
}

#[test]
fn e2e_aarch64_i128_div_zero_guard_tests_the_full_divisor() {
    let module = build_module();
    let runs: Vec<Vec<&str>> = std::iter::once(Vec::new())
        .chain(ZERO_DIVISOR_RUNS.iter().map(|(arg, _)| vec![*arg]))
        .collect();
    for opt in [OptLevel::O0, OptLevel::O2, OptLevel::O3] {
        let obj = compile_at(&module, opt);
        let Some(outputs) = link_run(&format!("i128_div_zero_guard_{opt:?}"), &obj, &runs) else {
            return;
        };
        let (output, zero_runs) = outputs.split_first().expect("one output per run");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(
            output.status.code(),
            Some(0),
            "{opt:?}: a nonzero 128-bit divisor must divide, not trap (exit code None is a \
             signal; SIGTRAP is the div-zero guard testing one half); stdout <<<{stdout}>>>"
        );
        assert_eq!(
            stdout, "i128 div-zero guard: 249 results match the __int128 reference\n",
            "{opt:?}"
        );
        // The full-width carrier is still a guard: a runtime zero divisor traps.
        for ((_, function), zero) in ZERO_DIVISOR_RUNS.iter().zip(zero_runs) {
            assert_eq!(
                signal_of(&zero.status),
                Some(SIGTRAP),
                "{opt:?}: {function}(1, 0) must trap in the div-zero guard before the libcall; \
                 status {:?}, stdout <<<{}>>>",
                zero.status,
                String::from_utf8_lossy(&zero.stdout)
            );
            assert!(zero.stdout.is_empty(), "{opt:?}: {function}(1, 0)");
        }
    }
}
