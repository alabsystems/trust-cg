// trust-cg-codegen/tests/e2e_x86_64_scale_emergent.rs
//
// Faithful x86_64 check of historical aarch64-JIT scale-emergent backend
// miscompiles: the exact pinned trust-ir that triggered the aarch64 JIT issue is
// compiled through the SEPARATE x86_64 path (x86_64_isel.rs + Greedy regalloc) and
// executed under Rosetta 2. Answers definitively: are these a LIVE x86 miscompile?
//
// Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0.

#![allow(clippy::all)]

mod common;

use std::path::Path;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;

fn compile_x86_64_at(module: &trust_ir::Module, opt: OptLevel) -> Result<Vec<u8>, String> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        target: Target::X86_64,
        ..CompilerConfig::default()
    });
    match compiler.compile(module) {
        Ok(r) if !r.object_code.is_empty() => Ok(r.object_code),
        Ok(_) => Err("compiled but empty object".to_string()),
        Err(e) => Err(format!("{e:?}")),
    }
}

fn nm_dump(obj_path: &Path) -> String {
    Command::new("nm")
        .arg(obj_path.to_str().unwrap())
        .output()
        .ok()
        .map(|o| String::from_utf8_lossy(&o.stdout).to_string())
        .unwrap_or_default()
}

/// The exact pinned trust-ir that the aarch64 JIT miscompiles COMPILES cleanly on
/// the x86_64 backend at every opt level (it does NOT fail-closed). Contrast with a
/// Rust-source version, which the trusted MIR->trust-ir frontend fails-closed on
/// (`Ref(Tuple)` not scalarizable) — a FRONTEND gap, separate from this BACKEND
/// question. Compiling the pre-emitted IR isolates the backend.
#[test]
fn x86_64_scale_emergent_irs_compile() {
    // edge_bounds is notable: the aarch64 ISel CANNOT lower its 4xi128 sret
    // ("value not defined before use"), pinned by trust_cg_cannot_lower_edge_bounds_
    // pinned_isel_limit; the x86_64 backend lowers it fine (and correctly, see
    // x86_64_edge_bounds_faithful) — x86 is MORE complete here.
    for (name, ir) in [
        ("fold_binop", MIR_FOLD_BINOP_TRUST_IR),
        ("value_matches", MIR_VALUE_MATCHES_TRUST_IR),
        ("edge_bounds", MIR_EDGE_BOUNDS_TRUST_IR),
    ] {
        let module = trust_ir::parser::parse_module(ir)
            .unwrap_or_else(|e| panic!("{name} must parse: {e:?}"));
        for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let bytes = compile_x86_64_at(&module, opt).unwrap_or_else(|e| {
                panic!("x86_64 must compile {name} at {opt:?} (not fail-closed): {e}")
            });
            eprintln!("[compile] {name} {opt:?}: {} bytes", bytes.len());
        }
    }
}

const MIR_FOLD_BINOP_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::fold_binop"

functy.0 = (ptr, ptr) -> ()

functy.1 = (ptr) -> ()

functy.2 = (ptr, i128, i128) -> ()

functy.3 = (ptr, i128, i128) -> ()

functy.4 = (ptr, i128, i128) -> ()

functy.5 = (ptr, i128, u32) -> ()

functy.6 = (ptr, u8, ptr, ptr) -> ()

functy.7 = (ptr, ptr, ptr) -> ()

functy.8 = (ptr, i128, i128) -> ()

functy.9 = (ptr, ptr, i128) -> ()

fn @_RNvXsJ_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionnENtNtNtB7_3ops9try_trait3Try6branchCs99MkpMfQ48c_23trust_fold_binop2_slice(functy.0) {
}

fn @_RNvXsK_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionnEINtNtNtB7_3ops9try_trait12FromResidualIBy_NtNtB7_7convert10InfallibleEE13from_residualCs99MkpMfQ48c_23trust_fold_binop2_slice(functy.1) {
}

fn @_RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_mulCs99MkpMfQ48c_23trust_fold_binop2_slice(functy.2) {
}

fn @_RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_subCs99MkpMfQ48c_23trust_fold_binop2_slice(functy.3) {
}

fn @_RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_addCs99MkpMfQ48c_23trust_fold_binop2_slice(functy.4) {
}

fn @_RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_shlCs99MkpMfQ48c_23trust_fold_binop2_slice(functy.5) {
}

fn @fold_binop(functy.6) {
bb0(%0: ptr, %1: u8, %2: ptr, %3: ptr):
    %15 = alloca i8, align 1
    %16 = alloca i128, align 16
    %17 = alloca (i128, i128), align 16
    %18 = alloca (i128, i128), align 16
    %19 = alloca (i128, i128), align 16
    %20 = alloca (i128, i128), align 16
    %21 = alloca i64, align 8
    store u8 %1, ptr %15
    call @func.0(%18, %2)
    br bb1
bb1:
    %22 = load i128, ptr %18
    %23 = trunc i128 %22 to i64
    switch %23 [ 0: bb3 1: bb4 default: bb2 ]
bb2:
    unreachable
bb3:
    %24 = const i64 16
    %25 = gep i8, ptr %18, %24
    %26 = load i128, ptr %25
    call @func.0(%19, %3)
    br bb5(%26)
bb4:
    call @func.1(%0)
    br bb20
bb5(%4: i128):
    %27 = load i128, ptr %19
    %28 = trunc i128 %27 to i64
    switch %28 [ 0: bb6(%4) 1: bb7 default: bb2 ]
bb6(%5: i128):
    %29 = const i64 16
    %30 = gep i8, ptr %19, %29
    %31 = load i128, ptr %30
    store i128 %5, ptr %17
    %32 = const i64 16
    %33 = gep i8, ptr %17, %32
    store i128 %31, ptr %33
    %34 = load i128, ptr %17
    store i128 %34, ptr %16
    %35 = const i64 16
    %36 = gep i8, ptr %17, %35
    %37 = load i128, ptr %36
    %38 = load i8, ptr %15
    %39 = sext i8 %38 to i64
    switch %39 [ 0: bb15(%37) 1: bb14(%37) 2: bb13(%37) 14: bb12(%37) 15: bb11(%37) 16: bb10(%37) 17: bb9(%37) default: bb8 ]
bb7:
    call @func.1(%0)
    br bb20
bb8:
    %40 = const i128 0
    store i128 %40, ptr %0
    br bb20
bb9(%6: i128):
    %41 = const i128 0
    %42 = icmp slt i128 %6, %41
    condbr %42, bb17, bb16(%6)
bb10(%7: i128):
    %43 = load i128, ptr %16
    %44 = xor i128 %43, %7
    %45 = const i64 16
    %46 = gep i8, ptr %0, %45
    store i128 %44, ptr %46
    %47 = const i128 1
    store i128 %47, ptr %0
    br bb20
bb11(%8: i128):
    %48 = load i128, ptr %16
    %49 = or i128 %48, %8
    %50 = const i64 16
    %51 = gep i8, ptr %0, %50
    store i128 %49, ptr %51
    %52 = const i128 1
    store i128 %52, ptr %0
    br bb20
bb12(%9: i128):
    %53 = load i128, ptr %16
    %54 = and i128 %53, %9
    %55 = const i64 16
    %56 = gep i8, ptr %0, %55
    store i128 %54, ptr %56
    %57 = const i128 1
    store i128 %57, ptr %0
    br bb20
bb13(%10: i128):
    %58 = load i128, ptr %16
    call @func.2(%0, %58, %10)
    br bb20
bb14(%11: i128):
    %59 = load i128, ptr %16
    call @func.3(%0, %59, %11)
    br bb20
bb15(%12: i128):
    %60 = load i128, ptr %16
    call @func.4(%0, %60, %12)
    br bb20
bb16(%13: i128):
    %61 = const i128 128
    %62 = icmp sge i128 %13, %61
    condbr %62, bb17, bb18(%13)
bb17:
    %63 = const i128 0
    store i128 %63, ptr %0
    br bb20
bb18(%14: i128):
    %64 = trunc i128 %14 to u32
    %65 = const i128 1
    call @func.5(%20, %65, %64)
    br bb19
bb19:
    store ptr %16, ptr %21
    call @func.7(%0, %20, %21)
    br bb20
bb20:
    ret
}

fn @std__option__Option___T___and_then__mono94d7478bc0df42bb(functy.7) {
bb0(%0: ptr, %1: ptr, %2: ptr):
    %3 = alloca i64, align 8
    %4 = alloca i128, align 16
    %5 = load i128, ptr %1
    %6 = trunc i128 %5 to i64
    switch %6 [ 0: bb2 1: bb3 default: bb1 ]
bb1:
    unreachable
bb2:
    %7 = const i128 0
    store i128 %7, ptr %0
    br bb5
bb3:
    %8 = const i64 16
    %9 = gep i8, ptr %1, %8
    %10 = load i128, ptr %9
    %11 = load i64, ptr %2
    store i64 %11, ptr %3
    store i128 %10, ptr %4
    %12 = load i128, ptr %4
    call @func.9(%0, %3, %12)
    br bb4
bb4:
    br bb5
bb5:
    ret
}

fn @_RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_mulCs99MkpMfQ48c_23trust_fold_binop2_slice(functy.8) {
}

fn @fold_binop___closure_0_(functy.9) {
bb0(%0: ptr, %1: ptr, %2: i128):
    %3 = load ptr, ptr %1
    %4 = load i128, ptr %3
    call @func.8(%0, %4, %2)
    br bb1
bb1:
    ret
}
"#;
// ---- FAITHFUL fold_binop x86_64 differential (Rosetta) ----

// Symbol names of the externs the trust-cg object calls + the entry, read off the
// emitted object (nm). Mach-O leading-underscore convention applies.
const SYM_FOLD: &str = "_fold_binop";
const SYM_TRY_BRANCH: &str = "__RNvXsJ_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionnENtNtNtB7_3ops9try_trait3Try6branchCs99MkpMfQ48c_23trust_fold_binop2_slice";
const SYM_FROM_RESIDUAL: &str = "__RNvXsK_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionnEINtNtNtB7_3ops9try_trait12FromResidualIBy_NtNtB7_7convert10InfallibleEE13from_residualCs99MkpMfQ48c_23trust_fold_binop2_slice";
const SYM_CHECKED_ADD: &str =
    "__RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_addCs99MkpMfQ48c_23trust_fold_binop2_slice";
const SYM_CHECKED_SUB: &str =
    "__RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_subCs99MkpMfQ48c_23trust_fold_binop2_slice";
const SYM_CHECKED_MUL: &str =
    "__RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_mulCs99MkpMfQ48c_23trust_fold_binop2_slice";
const SYM_CHECKED_SHL: &str =
    "__RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_shlCs99MkpMfQ48c_23trust_fold_binop2_slice";

fn driver_c() -> String {
    format!(
        r####"
#include <stdio.h>
typedef struct __attribute__((aligned(16))) {{ __int128 disc; __int128 val; }} OptI128;
typedef struct __attribute__((aligned(16))) {{ __int128 disc; __int128 val; }} CtrlFlowI128;

void shim_try_branch(CtrlFlowI128* out, const OptI128* opt) __asm__("{try}");
void shim_try_branch(CtrlFlowI128* out, const OptI128* opt) {{
    if (opt->disc == 1) {{ out->disc = 0; out->val = opt->val; }}
    else {{ out->disc = 1; out->val = 0; }}
}}
void shim_from_residual(OptI128* out) __asm__("{fromres}");
void shim_from_residual(OptI128* out) {{ out->disc = 0; out->val = 0; }}

static void put(OptI128* out, int ok, __int128 v) {{ if (ok) {{ out->disc = 1; out->val = v; }} else {{ out->disc = 0; out->val = 0; }} }}

void shim_checked_add(OptI128* out, __int128 a, __int128 b) __asm__("{add}");
void shim_checked_add(OptI128* out, __int128 a, __int128 b) {{ __int128 r; int o = __builtin_add_overflow(a,b,&r); put(out,!o,r); }}
void shim_checked_sub(OptI128* out, __int128 a, __int128 b) __asm__("{sub}");
void shim_checked_sub(OptI128* out, __int128 a, __int128 b) {{ __int128 r; int o = __builtin_sub_overflow(a,b,&r); put(out,!o,r); }}
void shim_checked_mul(OptI128* out, __int128 a, __int128 b) __asm__("{mul}");
void shim_checked_mul(OptI128* out, __int128 a, __int128 b) {{ __int128 r; int o = __builtin_mul_overflow(a,b,&r); put(out,!o,r); }}
void shim_checked_shl(OptI128* out, __int128 val, unsigned int shift) __asm__("{shl}");
void shim_checked_shl(OptI128* out, __int128 val, unsigned int shift) {{
    if (shift >= 128) {{ out->disc = 0; out->val = 0; }}
    else {{ out->disc = 1; out->val = (__int128)((unsigned __int128)val << shift); }}
}}

extern void fold_binop(OptI128* out, unsigned char op, const OptI128* lhs, const OptI128* rhs) __asm__("{fold}");

int main(void) {{
    struct {{ unsigned char op; OptI128 l; OptI128 r; }} cases[] = {{
        {{0,  {{1,2}},{{1,3}}}},
        {{2,  {{1,6}},{{1,7}}}},
        {{14, {{1,12}},{{1,10}}}},
        {{0,  {{0,0}},{{1,3}}}},
        {{17, {{1,3}},{{1,4}}}},
        {{17, {{1,1}},{{1,0}}}},
        {{17, {{1,3}},{{1,63}}}},
        {{17, {{1,1}},{{1,127}}}},
        {{17, {{1,3}},{{1,126}}}},
        {{17, {{1,5}},{{1,128}}}},
    }};
    int n = (int)(sizeof(cases)/sizeof(cases[0]));
    for (int i=0;i<n;i++) {{
        OptI128 out; out.disc = 99; out.val = 0;
        fold_binop(&out, cases[i].op, &cases[i].l, &cases[i].r);
        unsigned long long dlo=(unsigned long long)out.disc, dhi=(unsigned long long)((unsigned __int128)out.disc>>64);
        unsigned long long vlo=(unsigned long long)out.val, vhi=(unsigned long long)((unsigned __int128)out.val>>64);
        printf("%d %016llx%016llx %016llx%016llx\n", i, dhi,dlo, vhi,vlo);
    }}
    return 0;
}}
"####,
        try = SYM_TRY_BRANCH, fromres = SYM_FROM_RESIDUAL, add = SYM_CHECKED_ADD,
        sub = SYM_CHECKED_SUB, mul = SYM_CHECKED_MUL, shl = SYM_CHECKED_SHL, fold = SYM_FOLD,
    )
}

/// (disc, val_u128) expected per case. val ignored when disc==0 (None).
fn expected() -> Vec<(u128, u128)> {
    vec![
        (1, 5),            // Add 2,3
        (1, 42),           // Mul 6,7
        (1, 8),            // And 12,10
        (0, 0),            // Add None,3 -> None (?)
        (1, 48),           // Shl 3<<4   [aarch64 JIT MISCOMPILE -> None]
        (1, 1),            // Shl 1<<0   [aarch64 JIT MISCOMPILE -> None]
        (1, 3u128 << 63),  // Shl 3<<63  [aarch64 JIT MISCOMPILE -> None]
        (1, 1u128 << 127), // Shl 1<<127 [aarch64 JIT MISCOMPILE -> None]
        (0, 0),            // Shl 3<<126 -> None (overflow)
        (0, 0),            // Shl b>=128 -> None (guard)
    ]
}

fn run_fold_binop_at(opt: OptLevel) -> Result<Vec<(u128, u128)>, String> {
    let module = trust_ir::parser::parse_module(MIR_FOLD_BINOP_TRUST_IR)
        .map_err(|e| format!("parse: {e:?}"))?;
    let obj = compile_x86_64_at(&module, opt)?;
    let dir = std::env::temp_dir().join(format!("trust_cg_scale_fold_{opt:?}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let obj_path = dir.join("fold.o");
    std::fs::write(&obj_path, &obj).unwrap();
    let drv_path = dir.join("driver.c");
    std::fs::write(&drv_path, driver_c()).unwrap();
    let bin = dir.join("test_fold");
    let out = Command::new("cc")
        .args(if cfg!(target_os = "macos") {
            &["-arch", "x86_64"][..]
        } else {
            &[][..]
        })
        .args([
            "-O0",
            "-o",
            bin.to_str().unwrap(),
            drv_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
        ])
        .output()
        .map_err(|e| format!("cc spawn: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "LINK FAIL ({opt:?}):\nstderr={}\n--- nm ---\n{}",
            String::from_utf8_lossy(&out.stderr),
            nm_dump(&obj_path)
        ));
    }
    let run = Command::new(&bin)
        .output()
        .map_err(|e| format!("run spawn (Rosetta?): {e}"))?;
    if !run.status.success() {
        return Err(format!(
            "RUN FAIL ({opt:?}): code={:?} stderr={}",
            run.status.code(),
            String::from_utf8_lossy(&run.stderr)
        ));
    }
    let stdout = String::from_utf8_lossy(&run.stdout).to_string();
    let mut results = Vec::new();
    for line in stdout.lines() {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() != 3 {
            continue;
        }
        let disc = u128::from_str_radix(parts[1], 16).map_err(|e| format!("parse disc: {e}"))?;
        let val = u128::from_str_radix(parts[2], 16).map_err(|e| format!("parse val: {e}"))?;
        results.push((disc, val));
    }
    Ok(results)
}

#[test]
fn x86_64_fold_binop_shl_faithful() {
    if !common::rosetta::has_cc_x86_64_link_run() {
        eprintln!("skip: cc -arch x86_64 link/run unavailable");
        return;
    }
    let exp = expected();
    let mut any_miscompile = false;
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        match run_fold_binop_at(opt) {
            Ok(results) => {
                assert_eq!(results.len(), exp.len(), "case count mismatch at {opt:?}");
                for (i, (got, want)) in results.iter().zip(exp.iter()).enumerate() {
                    let ok = if want.0 == 0 { got.0 == 0 } else { got == want };
                    if !ok {
                        any_miscompile = true;
                        eprintln!(
                            "*** x86_64 MISCOMPILE fold_binop case {i} at {opt:?}: got (disc={:#x}, val={:#x}) want (disc={:#x}, val={:#x})",
                            got.0, got.1, want.0, want.1
                        );
                    }
                }
                eprintln!("[fold_binop {opt:?}] {} cases checked", results.len());
            }
            Err(e) => {
                // Fail-closed at compile/link is SOUND (not a miscompile); record it.
                eprintln!("[fold_binop {opt:?}] not executed: {e}");
            }
        }
    }
    assert!(
        !any_miscompile,
        "x86_64 fold_binop Shl miscompile detected (see stderr) — LIVE x86 BUG"
    );
}

const MIR_VALUE_MATCHES_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::Constant::value_matches_ty"

functy.0 = (ptr) -> (u64)

functy.1 = (ptr, ptr) -> ()

functy.2 = (ptr, ptr) -> ()

functy.3 = (ptr, ptr) -> (bool)

functy.4 = (ptr, ptr) -> (bool)

functy.5 = (ptr) -> (bool)

functy.6 = (i128, ptr) -> (bool)

functy.7 = (u64, u64) -> ()

functy.8 = (ptr, ptr) -> (bool)

functy.9 = (ptr) -> (bool)

functy.10 = (ptr) -> (bool)

functy.11 = (ptr) -> (bool)

functy.12 = (ptr, ptr) -> (bool)

fn @_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCs8vhpJKEIjU0_25trust_value_matches_slice8ConstantE3lenBG_(functy.0) {
}

fn @_RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs8vhpJKEIjU0_25trust_value_matches_slice8ConstantENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefBH_(functy.1) {
}

fn @_RNvMNtCs2EYQwhfuABO_4core5sliceSNtCs8vhpJKEIjU0_25trust_value_matches_slice8Constant4iterBw_(functy.2) {
}

fn @Constant__value_matches_ty(functy.3) {
bb0(%0: ptr, %1: ptr):
    %16 = alloca (i64, i64), align 8
    %17 = alloca i64, align 8
    %18 = alloca i64, align 8
    %19 = alloca (i64, i64), align 8
    %20 = alloca (i64, i64), align 8
    %21 = alloca i64, align 8
    %22 = alloca i64, align 8
    %23 = alloca i64, align 8
    %24 = alloca i64, align 8
    %25 = alloca i64, align 8
    store ptr %0, ptr %16
    %26 = const i64 8
    %27 = gep i8, ptr %16, %26
    store ptr %1, ptr %27
    %28 = load ptr, ptr %16
    %29 = load i8, ptr %28
    %30 = sext i8 %29 to i64
    switch %30 [ 0: bb4(%0, %1) 5: bb2(%0, %1) default: bb1(%0, %1) ]
bb1(%2: ptr, %3: ptr):
    %31 = call @func.4(%2, %3)
    br bb12(%31)
bb2(%4: ptr, %5: ptr):
    %32 = const i64 8
    %33 = gep i8, ptr %16, %32
    %34 = load ptr, ptr %33
    %35 = load i64, ptr %34
    %36 = const i64 21
    %37 = const i64 -9223372036854775808
    %38 = icmp eq i64 %35, %37
    %39 = const i64 0
    %40 = select i64 %38, %39, %36
    %41 = const i64 -9223372036854775807
    %42 = icmp eq i64 %35, %41
    %43 = const i64 1
    %44 = select i64 %42, %43, %40
    %45 = const i64 -9223372036854775806
    %46 = icmp eq i64 %35, %45
    %47 = const i64 2
    %48 = select i64 %46, %47, %44
    %49 = const i64 -9223372036854775805
    %50 = icmp eq i64 %35, %49
    %51 = const i64 3
    %52 = select i64 %50, %51, %48
    %53 = const i64 -9223372036854775804
    %54 = icmp eq i64 %35, %53
    %55 = const i64 4
    %56 = select i64 %54, %55, %52
    %57 = const i64 -9223372036854775803
    %58 = icmp eq i64 %35, %57
    %59 = const i64 5
    %60 = select i64 %58, %59, %56
    %61 = const i64 -9223372036854775802
    %62 = icmp eq i64 %35, %61
    %63 = const i64 6
    %64 = select i64 %62, %63, %60
    %65 = const i64 -9223372036854775801
    %66 = icmp eq i64 %35, %65
    %67 = const i64 7
    %68 = select i64 %66, %67, %64
    %69 = const i64 -9223372036854775800
    %70 = icmp eq i64 %35, %69
    %71 = const i64 8
    %72 = select i64 %70, %71, %68
    %73 = const i64 -9223372036854775799
    %74 = icmp eq i64 %35, %73
    %75 = const i64 9
    %76 = select i64 %74, %75, %72
    %77 = const i64 -9223372036854775798
    %78 = icmp eq i64 %35, %77
    %79 = const i64 10
    %80 = select i64 %78, %79, %76
    %81 = const i64 -9223372036854775797
    %82 = icmp eq i64 %35, %81
    %83 = const i64 11
    %84 = select i64 %82, %83, %80
    %85 = const i64 -9223372036854775796
    %86 = icmp eq i64 %35, %85
    %87 = const i64 12
    %88 = select i64 %86, %87, %84
    %89 = const i64 -9223372036854775795
    %90 = icmp eq i64 %35, %89
    %91 = const i64 13
    %92 = select i64 %90, %91, %88
    %93 = const i64 -9223372036854775794
    %94 = icmp eq i64 %35, %93
    %95 = const i64 14
    %96 = select i64 %94, %95, %92
    %97 = const i64 -9223372036854775793
    %98 = icmp eq i64 %35, %97
    %99 = const i64 15
    %100 = select i64 %98, %99, %96
    %101 = const i64 -9223372036854775792
    %102 = icmp eq i64 %35, %101
    %103 = const i64 16
    %104 = select i64 %102, %103, %100
    %105 = const i64 -9223372036854775791
    %106 = icmp eq i64 %35, %105
    %107 = const i64 17
    %108 = select i64 %106, %107, %104
    %109 = const i64 -9223372036854775790
    %110 = icmp eq i64 %35, %109
    %111 = const i64 18
    %112 = select i64 %110, %111, %108
    %113 = const i64 -9223372036854775789
    %114 = icmp eq i64 %35, %113
    %115 = const i64 19
    %116 = select i64 %114, %115, %112
    %117 = const i64 -9223372036854775788
    %118 = icmp eq i64 %35, %117
    %119 = const i64 20
    %120 = select i64 %118, %119, %116
    %121 = const i64 -9223372036854775786
    %122 = icmp eq i64 %35, %121
    %123 = const i64 22
    %124 = select i64 %122, %123, %120
    %125 = const i64 -9223372036854775785
    %126 = icmp eq i64 %35, %125
    %127 = const i64 23
    %128 = select i64 %126, %127, %124
    %129 = const i64 -9223372036854775784
    %130 = icmp eq i64 %35, %129
    %131 = const i64 24
    %132 = select i64 %130, %131, %128
    %133 = const i64 -9223372036854775783
    %134 = icmp eq i64 %35, %133
    %135 = const i64 25
    %136 = select i64 %134, %135, %132
    %137 = const i64 -9223372036854775782
    %138 = icmp eq i64 %35, %137
    %139 = const i64 26
    %140 = select i64 %138, %139, %136
    %141 = const i64 -9223372036854775781
    %142 = icmp eq i64 %35, %141
    %143 = const i64 27
    %144 = select i64 %142, %143, %140
    %145 = const i64 -9223372036854775780
    %146 = icmp eq i64 %35, %145
    %147 = const i64 28
    %148 = select i64 %146, %147, %144
    %149 = const i64 -9223372036854775779
    %150 = icmp eq i64 %35, %149
    %151 = const i64 29
    %152 = select i64 %150, %151, %148
    %153 = const i64 -9223372036854775778
    %154 = icmp eq i64 %35, %153
    %155 = const i64 30
    %156 = select i64 %154, %155, %152
    %157 = const i64 -9223372036854775777
    %158 = icmp eq i64 %35, %157
    %159 = const i64 31
    %160 = select i64 %158, %159, %156
    %161 = const i64 -9223372036854775776
    %162 = icmp eq i64 %35, %161
    %163 = const i64 32
    %164 = select i64 %162, %163, %160
    switch %164 [ 14: bb3 default: bb1(%4, %5) ]
bb3:
    %165 = load ptr, ptr %16
    store ptr %165, ptr %22
    %166 = load ptr, ptr %22
    %167 = const i64 8
    %168 = gep i8, ptr %166, %167
    %169 = const i64 8
    %170 = gep i8, ptr %16, %169
    %171 = load ptr, ptr %170
    store ptr %171, ptr %23
    %172 = load ptr, ptr %23
    %173 = const i64 8
    %174 = gep i8, ptr %172, %173
    store ptr %174, ptr %18
    %175 = const i64 8
    %176 = gep i8, ptr %16, %175
    %177 = load ptr, ptr %176
    store ptr %177, ptr %24
    %178 = load ptr, ptr %24
    %179 = const i64 16
    %180 = gep i8, ptr %178, %179
    %181 = call @func.0(%168)
    br bb7(%168, %180, %181)
bb4(%6: ptr, %7: ptr):
    %182 = load ptr, ptr %16
    store ptr %182, ptr %25
    %183 = load ptr, ptr %25
    %184 = const i64 16
    %185 = gep i8, ptr %183, %184
    store ptr %185, ptr %17
    %186 = const i64 8
    %187 = gep i8, ptr %16, %186
    %188 = load ptr, ptr %187
    %189 = call @func.5(%188)
    br bb5(%6, %7, %189)
bb5(%8: ptr, %9: ptr, %10: bool):
    condbr %10, bb6, bb1(%8, %9)
bb6:
    %190 = const i64 8
    %191 = gep i8, ptr %16, %190
    %192 = load ptr, ptr %191
    %193 = load ptr, ptr %17
    %194 = load i128, ptr %193
    %195 = call @func.6(%194, %192)
    br bb12(%195)
bb7(%11: ptr, %12: ptr, %13: u64):
    %196 = load u32, ptr %12
    %197 = zext u32 %196 to u64
    %198 = icmp eq u64 %13, %197
    condbr %198, bb8(%11), bb9
bb8(%14: ptr):
    call @func.1(%20, %14)
    br bb10
bb9:
    %199 = const bool false
    br bb12(%199)
bb10:
    call @func.2(%19, %20)
    br bb11
bb11:
    store ptr %18, ptr %21
    %200 = call @func.8(%19, %21)
    br bb12(%200)
bb12(%15: bool):
    ret %15
}

fn @Constant__shape_matches_ty(functy.4) {
bb0(%0: ptr, %1: ptr):
    %5 = alloca (i64, i64), align 8
    store ptr %0, ptr %5
    %6 = const i64 8
    %7 = gep i8, ptr %5, %6
    store ptr %1, ptr %7
    %8 = load ptr, ptr %5
    %9 = load i8, ptr %8
    %10 = sext i8 %9 to i64
    switch %10 [ 0: bb27 1: bb25 2: bb2 3: bb3 4: bb4 5: bb5 6: bb6 7: bb7 8: bb8 9: bb9 10: bb10 11: bb11 12: bb12 default: bb34 ]
bb1:
    %11 = const bool false
    br bb33(%11)
bb2:
    %12 = const i64 8
    %13 = gep i8, ptr %5, %12
    %14 = load ptr, ptr %13
    %15 = load i64, ptr %14
    %16 = const i64 21
    %17 = const i64 -9223372036854775808
    %18 = icmp eq i64 %15, %17
    %19 = const i64 0
    %20 = select i64 %18, %19, %16
    %21 = const i64 -9223372036854775807
    %22 = icmp eq i64 %15, %21
    %23 = const i64 1
    %24 = select i64 %22, %23, %20
    %25 = const i64 -9223372036854775806
    %26 = icmp eq i64 %15, %25
    %27 = const i64 2
    %28 = select i64 %26, %27, %24
    %29 = const i64 -9223372036854775805
    %30 = icmp eq i64 %15, %29
    %31 = const i64 3
    %32 = select i64 %30, %31, %28
    %33 = const i64 -9223372036854775804
    %34 = icmp eq i64 %15, %33
    %35 = const i64 4
    %36 = select i64 %34, %35, %32
    %37 = const i64 -9223372036854775803
    %38 = icmp eq i64 %15, %37
    %39 = const i64 5
    %40 = select i64 %38, %39, %36
    %41 = const i64 -9223372036854775802
    %42 = icmp eq i64 %15, %41
    %43 = const i64 6
    %44 = select i64 %42, %43, %40
    %45 = const i64 -9223372036854775801
    %46 = icmp eq i64 %15, %45
    %47 = const i64 7
    %48 = select i64 %46, %47, %44
    %49 = const i64 -9223372036854775800
    %50 = icmp eq i64 %15, %49
    %51 = const i64 8
    %52 = select i64 %50, %51, %48
    %53 = const i64 -9223372036854775799
    %54 = icmp eq i64 %15, %53
    %55 = const i64 9
    %56 = select i64 %54, %55, %52
    %57 = const i64 -9223372036854775798
    %58 = icmp eq i64 %15, %57
    %59 = const i64 10
    %60 = select i64 %58, %59, %56
    %61 = const i64 -9223372036854775797
    %62 = icmp eq i64 %15, %61
    %63 = const i64 11
    %64 = select i64 %62, %63, %60
    %65 = const i64 -9223372036854775796
    %66 = icmp eq i64 %15, %65
    %67 = const i64 12
    %68 = select i64 %66, %67, %64
    %69 = const i64 -9223372036854775795
    %70 = icmp eq i64 %15, %69
    %71 = const i64 13
    %72 = select i64 %70, %71, %68
    %73 = const i64 -9223372036854775794
    %74 = icmp eq i64 %15, %73
    %75 = const i64 14
    %76 = select i64 %74, %75, %72
    %77 = const i64 -9223372036854775793
    %78 = icmp eq i64 %15, %77
    %79 = const i64 15
    %80 = select i64 %78, %79, %76
    %81 = const i64 -9223372036854775792
    %82 = icmp eq i64 %15, %81
    %83 = const i64 16
    %84 = select i64 %82, %83, %80
    %85 = const i64 -9223372036854775791
    %86 = icmp eq i64 %15, %85
    %87 = const i64 17
    %88 = select i64 %86, %87, %84
    %89 = const i64 -9223372036854775790
    %90 = icmp eq i64 %15, %89
    %91 = const i64 18
    %92 = select i64 %90, %91, %88
    %93 = const i64 -9223372036854775789
    %94 = icmp eq i64 %15, %93
    %95 = const i64 19
    %96 = select i64 %94, %95, %92
    %97 = const i64 -9223372036854775788
    %98 = icmp eq i64 %15, %97
    %99 = const i64 20
    %100 = select i64 %98, %99, %96
    %101 = const i64 -9223372036854775786
    %102 = icmp eq i64 %15, %101
    %103 = const i64 22
    %104 = select i64 %102, %103, %100
    %105 = const i64 -9223372036854775785
    %106 = icmp eq i64 %15, %105
    %107 = const i64 23
    %108 = select i64 %106, %107, %104
    %109 = const i64 -9223372036854775784
    %110 = icmp eq i64 %15, %109
    %111 = const i64 24
    %112 = select i64 %110, %111, %108
    %113 = const i64 -9223372036854775783
    %114 = icmp eq i64 %15, %113
    %115 = const i64 25
    %116 = select i64 %114, %115, %112
    %117 = const i64 -9223372036854775782
    %118 = icmp eq i64 %15, %117
    %119 = const i64 26
    %120 = select i64 %118, %119, %116
    %121 = const i64 -9223372036854775781
    %122 = icmp eq i64 %15, %121
    %123 = const i64 27
    %124 = select i64 %122, %123, %120
    %125 = const i64 -9223372036854775780
    %126 = icmp eq i64 %15, %125
    %127 = const i64 28
    %128 = select i64 %126, %127, %124
    %129 = const i64 -9223372036854775779
    %130 = icmp eq i64 %15, %129
    %131 = const i64 29
    %132 = select i64 %130, %131, %128
    %133 = const i64 -9223372036854775778
    %134 = icmp eq i64 %15, %133
    %135 = const i64 30
    %136 = select i64 %134, %135, %132
    %137 = const i64 -9223372036854775777
    %138 = icmp eq i64 %15, %137
    %139 = const i64 31
    %140 = select i64 %138, %139, %136
    %141 = const i64 -9223372036854775776
    %142 = icmp eq i64 %15, %141
    %143 = const i64 32
    %144 = select i64 %142, %143, %140
    switch %144 [ 13: bb24 default: bb1 ]
bb3:
    %145 = const i64 8
    %146 = gep i8, ptr %5, %145
    %147 = load ptr, ptr %146
    %148 = load i64, ptr %147
    %149 = const i64 21
    %150 = const i64 -9223372036854775808
    %151 = icmp eq i64 %148, %150
    %152 = const i64 0
    %153 = select i64 %151, %152, %149
    %154 = const i64 -9223372036854775807
    %155 = icmp eq i64 %148, %154
    %156 = const i64 1
    %157 = select i64 %155, %156, %153
    %158 = const i64 -9223372036854775806
    %159 = icmp eq i64 %148, %158
    %160 = const i64 2
    %161 = select i64 %159, %160, %157
    %162 = const i64 -9223372036854775805
    %163 = icmp eq i64 %148, %162
    %164 = const i64 3
    %165 = select i64 %163, %164, %161
    %166 = const i64 -9223372036854775804
    %167 = icmp eq i64 %148, %166
    %168 = const i64 4
    %169 = select i64 %167, %168, %165
    %170 = const i64 -9223372036854775803
    %171 = icmp eq i64 %148, %170
    %172 = const i64 5
    %173 = select i64 %171, %172, %169
    %174 = const i64 -9223372036854775802
    %175 = icmp eq i64 %148, %174
    %176 = const i64 6
    %177 = select i64 %175, %176, %173
    %178 = const i64 -9223372036854775801
    %179 = icmp eq i64 %148, %178
    %180 = const i64 7
    %181 = select i64 %179, %180, %177
    %182 = const i64 -9223372036854775800
    %183 = icmp eq i64 %148, %182
    %184 = const i64 8
    %185 = select i64 %183, %184, %181
    %186 = const i64 -9223372036854775799
    %187 = icmp eq i64 %148, %186
    %188 = const i64 9
    %189 = select i64 %187, %188, %185
    %190 = const i64 -9223372036854775798
    %191 = icmp eq i64 %148, %190
    %192 = const i64 10
    %193 = select i64 %191, %192, %189
    %194 = const i64 -9223372036854775797
    %195 = icmp eq i64 %148, %194
    %196 = const i64 11
    %197 = select i64 %195, %196, %193
    %198 = const i64 -9223372036854775796
    %199 = icmp eq i64 %148, %198
    %200 = const i64 12
    %201 = select i64 %199, %200, %197
    %202 = const i64 -9223372036854775795
    %203 = icmp eq i64 %148, %202
    %204 = const i64 13
    %205 = select i64 %203, %204, %201
    %206 = const i64 -9223372036854775794
    %207 = icmp eq i64 %148, %206
    %208 = const i64 14
    %209 = select i64 %207, %208, %205
    %210 = const i64 -9223372036854775793
    %211 = icmp eq i64 %148, %210
    %212 = const i64 15
    %213 = select i64 %211, %212, %209
    %214 = const i64 -9223372036854775792
    %215 = icmp eq i64 %148, %214
    %216 = const i64 16
    %217 = select i64 %215, %216, %213
    %218 = const i64 -9223372036854775791
    %219 = icmp eq i64 %148, %218
    %220 = const i64 17
    %221 = select i64 %219, %220, %217
    %222 = const i64 -9223372036854775790
    %223 = icmp eq i64 %148, %222
    %224 = const i64 18
    %225 = select i64 %223, %224, %221
    %226 = const i64 -9223372036854775789
    %227 = icmp eq i64 %148, %226
    %228 = const i64 19
    %229 = select i64 %227, %228, %225
    %230 = const i64 -9223372036854775788
    %231 = icmp eq i64 %148, %230
    %232 = const i64 20
    %233 = select i64 %231, %232, %229
    %234 = const i64 -9223372036854775786
    %235 = icmp eq i64 %148, %234
    %236 = const i64 22
    %237 = select i64 %235, %236, %233
    %238 = const i64 -9223372036854775785
    %239 = icmp eq i64 %148, %238
    %240 = const i64 23
    %241 = select i64 %239, %240, %237
    %242 = const i64 -9223372036854775784
    %243 = icmp eq i64 %148, %242
    %244 = const i64 24
    %245 = select i64 %243, %244, %241
    %246 = const i64 -9223372036854775783
    %247 = icmp eq i64 %148, %246
    %248 = const i64 25
    %249 = select i64 %247, %248, %245
    %250 = const i64 -9223372036854775782
    %251 = icmp eq i64 %148, %250
    %252 = const i64 26
    %253 = select i64 %251, %252, %249
    %254 = const i64 -9223372036854775781
    %255 = icmp eq i64 %148, %254
    %256 = const i64 27
    %257 = select i64 %255, %256, %253
    %258 = const i64 -9223372036854775780
    %259 = icmp eq i64 %148, %258
    %260 = const i64 28
    %261 = select i64 %259, %260, %257
    %262 = const i64 -9223372036854775779
    %263 = icmp eq i64 %148, %262
    %264 = const i64 29
    %265 = select i64 %263, %264, %261
    %266 = const i64 -9223372036854775778
    %267 = icmp eq i64 %148, %266
    %268 = const i64 30
    %269 = select i64 %267, %268, %265
    %270 = const i64 -9223372036854775777
    %271 = icmp eq i64 %148, %270
    %272 = const i64 31
    %273 = select i64 %271, %272, %269
    %274 = const i64 -9223372036854775776
    %275 = icmp eq i64 %148, %274
    %276 = const i64 32
    %277 = select i64 %275, %276, %273
    switch %277 [ 19: bb23 20: bb23 21: bb23 31: bb23 default: bb1 ]
bb4:
    %278 = const i64 8
    %279 = gep i8, ptr %5, %278
    %280 = load ptr, ptr %279
    %281 = load i64, ptr %280
    %282 = const i64 21
    %283 = const i64 -9223372036854775808
    %284 = icmp eq i64 %281, %283
    %285 = const i64 0
    %286 = select i64 %284, %285, %282
    %287 = const i64 -9223372036854775807
    %288 = icmp eq i64 %281, %287
    %289 = const i64 1
    %290 = select i64 %288, %289, %286
    %291 = const i64 -9223372036854775806
    %292 = icmp eq i64 %281, %291
    %293 = const i64 2
    %294 = select i64 %292, %293, %290
    %295 = const i64 -9223372036854775805
    %296 = icmp eq i64 %281, %295
    %297 = const i64 3
    %298 = select i64 %296, %297, %294
    %299 = const i64 -9223372036854775804
    %300 = icmp eq i64 %281, %299
    %301 = const i64 4
    %302 = select i64 %300, %301, %298
    %303 = const i64 -9223372036854775803
    %304 = icmp eq i64 %281, %303
    %305 = const i64 5
    %306 = select i64 %304, %305, %302
    %307 = const i64 -9223372036854775802
    %308 = icmp eq i64 %281, %307
    %309 = const i64 6
    %310 = select i64 %308, %309, %306
    %311 = const i64 -9223372036854775801
    %312 = icmp eq i64 %281, %311
    %313 = const i64 7
    %314 = select i64 %312, %313, %310
    %315 = const i64 -9223372036854775800
    %316 = icmp eq i64 %281, %315
    %317 = const i64 8
    %318 = select i64 %316, %317, %314
    %319 = const i64 -9223372036854775799
    %320 = icmp eq i64 %281, %319
    %321 = const i64 9
    %322 = select i64 %320, %321, %318
    %323 = const i64 -9223372036854775798
    %324 = icmp eq i64 %281, %323
    %325 = const i64 10
    %326 = select i64 %324, %325, %322
    %327 = const i64 -9223372036854775797
    %328 = icmp eq i64 %281, %327
    %329 = const i64 11
    %330 = select i64 %328, %329, %326
    %331 = const i64 -9223372036854775796
    %332 = icmp eq i64 %281, %331
    %333 = const i64 12
    %334 = select i64 %332, %333, %330
    %335 = const i64 -9223372036854775795
    %336 = icmp eq i64 %281, %335
    %337 = const i64 13
    %338 = select i64 %336, %337, %334
    %339 = const i64 -9223372036854775794
    %340 = icmp eq i64 %281, %339
    %341 = const i64 14
    %342 = select i64 %340, %341, %338
    %343 = const i64 -9223372036854775793
    %344 = icmp eq i64 %281, %343
    %345 = const i64 15
    %346 = select i64 %344, %345, %342
    %347 = const i64 -9223372036854775792
    %348 = icmp eq i64 %281, %347
    %349 = const i64 16
    %350 = select i64 %348, %349, %346
    %351 = const i64 -9223372036854775791
    %352 = icmp eq i64 %281, %351
    %353 = const i64 17
    %354 = select i64 %352, %353, %350
    %355 = const i64 -9223372036854775790
    %356 = icmp eq i64 %281, %355
    %357 = const i64 18
    %358 = select i64 %356, %357, %354
    %359 = const i64 -9223372036854775789
    %360 = icmp eq i64 %281, %359
    %361 = const i64 19
    %362 = select i64 %360, %361, %358
    %363 = const i64 -9223372036854775788
    %364 = icmp eq i64 %281, %363
    %365 = const i64 20
    %366 = select i64 %364, %365, %362
    %367 = const i64 -9223372036854775786
    %368 = icmp eq i64 %281, %367
    %369 = const i64 22
    %370 = select i64 %368, %369, %366
    %371 = const i64 -9223372036854775785
    %372 = icmp eq i64 %281, %371
    %373 = const i64 23
    %374 = select i64 %372, %373, %370
    %375 = const i64 -9223372036854775784
    %376 = icmp eq i64 %281, %375
    %377 = const i64 24
    %378 = select i64 %376, %377, %374
    %379 = const i64 -9223372036854775783
    %380 = icmp eq i64 %281, %379
    %381 = const i64 25
    %382 = select i64 %380, %381, %378
    %383 = const i64 -9223372036854775782
    %384 = icmp eq i64 %281, %383
    %385 = const i64 26
    %386 = select i64 %384, %385, %382
    %387 = const i64 -9223372036854775781
    %388 = icmp eq i64 %281, %387
    %389 = const i64 27
    %390 = select i64 %388, %389, %386
    %391 = const i64 -9223372036854775780
    %392 = icmp eq i64 %281, %391
    %393 = const i64 28
    %394 = select i64 %392, %393, %390
    %395 = const i64 -9223372036854775779
    %396 = icmp eq i64 %281, %395
    %397 = const i64 29
    %398 = select i64 %396, %397, %394
    %399 = const i64 -9223372036854775778
    %400 = icmp eq i64 %281, %399
    %401 = const i64 30
    %402 = select i64 %400, %401, %398
    %403 = const i64 -9223372036854775777
    %404 = icmp eq i64 %281, %403
    %405 = const i64 31
    %406 = select i64 %404, %405, %402
    %407 = const i64 -9223372036854775776
    %408 = icmp eq i64 %281, %407
    %409 = const i64 32
    %410 = select i64 %408, %409, %406
    switch %410 [ 20: bb22 default: bb1 ]
bb5:
    %411 = const i64 8
    %412 = gep i8, ptr %5, %411
    %413 = load ptr, ptr %412
    %414 = load i64, ptr %413
    %415 = const i64 21
    %416 = const i64 -9223372036854775808
    %417 = icmp eq i64 %414, %416
    %418 = const i64 0
    %419 = select i64 %417, %418, %415
    %420 = const i64 -9223372036854775807
    %421 = icmp eq i64 %414, %420
    %422 = const i64 1
    %423 = select i64 %421, %422, %419
    %424 = const i64 -9223372036854775806
    %425 = icmp eq i64 %414, %424
    %426 = const i64 2
    %427 = select i64 %425, %426, %423
    %428 = const i64 -9223372036854775805
    %429 = icmp eq i64 %414, %428
    %430 = const i64 3
    %431 = select i64 %429, %430, %427
    %432 = const i64 -9223372036854775804
    %433 = icmp eq i64 %414, %432
    %434 = const i64 4
    %435 = select i64 %433, %434, %431
    %436 = const i64 -9223372036854775803
    %437 = icmp eq i64 %414, %436
    %438 = const i64 5
    %439 = select i64 %437, %438, %435
    %440 = const i64 -9223372036854775802
    %441 = icmp eq i64 %414, %440
    %442 = const i64 6
    %443 = select i64 %441, %442, %439
    %444 = const i64 -9223372036854775801
    %445 = icmp eq i64 %414, %444
    %446 = const i64 7
    %447 = select i64 %445, %446, %443
    %448 = const i64 -9223372036854775800
    %449 = icmp eq i64 %414, %448
    %450 = const i64 8
    %451 = select i64 %449, %450, %447
    %452 = const i64 -9223372036854775799
    %453 = icmp eq i64 %414, %452
    %454 = const i64 9
    %455 = select i64 %453, %454, %451
    %456 = const i64 -9223372036854775798
    %457 = icmp eq i64 %414, %456
    %458 = const i64 10
    %459 = select i64 %457, %458, %455
    %460 = const i64 -9223372036854775797
    %461 = icmp eq i64 %414, %460
    %462 = const i64 11
    %463 = select i64 %461, %462, %459
    %464 = const i64 -9223372036854775796
    %465 = icmp eq i64 %414, %464
    %466 = const i64 12
    %467 = select i64 %465, %466, %463
    %468 = const i64 -9223372036854775795
    %469 = icmp eq i64 %414, %468
    %470 = const i64 13
    %471 = select i64 %469, %470, %467
    %472 = const i64 -9223372036854775794
    %473 = icmp eq i64 %414, %472
    %474 = const i64 14
    %475 = select i64 %473, %474, %471
    %476 = const i64 -9223372036854775793
    %477 = icmp eq i64 %414, %476
    %478 = const i64 15
    %479 = select i64 %477, %478, %475
    %480 = const i64 -9223372036854775792
    %481 = icmp eq i64 %414, %480
    %482 = const i64 16
    %483 = select i64 %481, %482, %479
    %484 = const i64 -9223372036854775791
    %485 = icmp eq i64 %414, %484
    %486 = const i64 17
    %487 = select i64 %485, %486, %483
    %488 = const i64 -9223372036854775790
    %489 = icmp eq i64 %414, %488
    %490 = const i64 18
    %491 = select i64 %489, %490, %487
    %492 = const i64 -9223372036854775789
    %493 = icmp eq i64 %414, %492
    %494 = const i64 19
    %495 = select i64 %493, %494, %491
    %496 = const i64 -9223372036854775788
    %497 = icmp eq i64 %414, %496
    %498 = const i64 20
    %499 = select i64 %497, %498, %495
    %500 = const i64 -9223372036854775786
    %501 = icmp eq i64 %414, %500
    %502 = const i64 22
    %503 = select i64 %501, %502, %499
    %504 = const i64 -9223372036854775785
    %505 = icmp eq i64 %414, %504
    %506 = const i64 23
    %507 = select i64 %505, %506, %503
    %508 = const i64 -9223372036854775784
    %509 = icmp eq i64 %414, %508
    %510 = const i64 24
    %511 = select i64 %509, %510, %507
    %512 = const i64 -9223372036854775783
    %513 = icmp eq i64 %414, %512
    %514 = const i64 25
    %515 = select i64 %513, %514, %511
    %516 = const i64 -9223372036854775782
    %517 = icmp eq i64 %414, %516
    %518 = const i64 26
    %519 = select i64 %517, %518, %515
    %520 = const i64 -9223372036854775781
    %521 = icmp eq i64 %414, %520
    %522 = const i64 27
    %523 = select i64 %521, %522, %519
    %524 = const i64 -9223372036854775780
    %525 = icmp eq i64 %414, %524
    %526 = const i64 28
    %527 = select i64 %525, %526, %523
    %528 = const i64 -9223372036854775779
    %529 = icmp eq i64 %414, %528
    %530 = const i64 29
    %531 = select i64 %529, %530, %527
    %532 = const i64 -9223372036854775778
    %533 = icmp eq i64 %414, %532
    %534 = const i64 30
    %535 = select i64 %533, %534, %531
    %536 = const i64 -9223372036854775777
    %537 = icmp eq i64 %414, %536
    %538 = const i64 31
    %539 = select i64 %537, %538, %535
    %540 = const i64 -9223372036854775776
    %541 = icmp eq i64 %414, %540
    %542 = const i64 32
    %543 = select i64 %541, %542, %539
    switch %543 [ 14: bb21 default: bb1 ]
bb6:
    %544 = const i64 8
    %545 = gep i8, ptr %5, %544
    %546 = load ptr, ptr %545
    %547 = load i64, ptr %546
    %548 = const i64 21
    %549 = const i64 -9223372036854775808
    %550 = icmp eq i64 %547, %549
    %551 = const i64 0
    %552 = select i64 %550, %551, %548
    %553 = const i64 -9223372036854775807
    %554 = icmp eq i64 %547, %553
    %555 = const i64 1
    %556 = select i64 %554, %555, %552
    %557 = const i64 -9223372036854775806
    %558 = icmp eq i64 %547, %557
    %559 = const i64 2
    %560 = select i64 %558, %559, %556
    %561 = const i64 -9223372036854775805
    %562 = icmp eq i64 %547, %561
    %563 = const i64 3
    %564 = select i64 %562, %563, %560
    %565 = const i64 -9223372036854775804
    %566 = icmp eq i64 %547, %565
    %567 = const i64 4
    %568 = select i64 %566, %567, %564
    %569 = const i64 -9223372036854775803
    %570 = icmp eq i64 %547, %569
    %571 = const i64 5
    %572 = select i64 %570, %571, %568
    %573 = const i64 -9223372036854775802
    %574 = icmp eq i64 %547, %573
    %575 = const i64 6
    %576 = select i64 %574, %575, %572
    %577 = const i64 -9223372036854775801
    %578 = icmp eq i64 %547, %577
    %579 = const i64 7
    %580 = select i64 %578, %579, %576
    %581 = const i64 -9223372036854775800
    %582 = icmp eq i64 %547, %581
    %583 = const i64 8
    %584 = select i64 %582, %583, %580
    %585 = const i64 -9223372036854775799
    %586 = icmp eq i64 %547, %585
    %587 = const i64 9
    %588 = select i64 %586, %587, %584
    %589 = const i64 -9223372036854775798
    %590 = icmp eq i64 %547, %589
    %591 = const i64 10
    %592 = select i64 %590, %591, %588
    %593 = const i64 -9223372036854775797
    %594 = icmp eq i64 %547, %593
    %595 = const i64 11
    %596 = select i64 %594, %595, %592
    %597 = const i64 -9223372036854775796
    %598 = icmp eq i64 %547, %597
    %599 = const i64 12
    %600 = select i64 %598, %599, %596
    %601 = const i64 -9223372036854775795
    %602 = icmp eq i64 %547, %601
    %603 = const i64 13
    %604 = select i64 %602, %603, %600
    %605 = const i64 -9223372036854775794
    %606 = icmp eq i64 %547, %605
    %607 = const i64 14
    %608 = select i64 %606, %607, %604
    %609 = const i64 -9223372036854775793
    %610 = icmp eq i64 %547, %609
    %611 = const i64 15
    %612 = select i64 %610, %611, %608
    %613 = const i64 -9223372036854775792
    %614 = icmp eq i64 %547, %613
    %615 = const i64 16
    %616 = select i64 %614, %615, %612
    %617 = const i64 -9223372036854775791
    %618 = icmp eq i64 %547, %617
    %619 = const i64 17
    %620 = select i64 %618, %619, %616
    %621 = const i64 -9223372036854775790
    %622 = icmp eq i64 %547, %621
    %623 = const i64 18
    %624 = select i64 %622, %623, %620
    %625 = const i64 -9223372036854775789
    %626 = icmp eq i64 %547, %625
    %627 = const i64 19
    %628 = select i64 %626, %627, %624
    %629 = const i64 -9223372036854775788
    %630 = icmp eq i64 %547, %629
    %631 = const i64 20
    %632 = select i64 %630, %631, %628
    %633 = const i64 -9223372036854775786
    %634 = icmp eq i64 %547, %633
    %635 = const i64 22
    %636 = select i64 %634, %635, %632
    %637 = const i64 -9223372036854775785
    %638 = icmp eq i64 %547, %637
    %639 = const i64 23
    %640 = select i64 %638, %639, %636
    %641 = const i64 -9223372036854775784
    %642 = icmp eq i64 %547, %641
    %643 = const i64 24
    %644 = select i64 %642, %643, %640
    %645 = const i64 -9223372036854775783
    %646 = icmp eq i64 %547, %645
    %647 = const i64 25
    %648 = select i64 %646, %647, %644
    %649 = const i64 -9223372036854775782
    %650 = icmp eq i64 %547, %649
    %651 = const i64 26
    %652 = select i64 %650, %651, %648
    %653 = const i64 -9223372036854775781
    %654 = icmp eq i64 %547, %653
    %655 = const i64 27
    %656 = select i64 %654, %655, %652
    %657 = const i64 -9223372036854775780
    %658 = icmp eq i64 %547, %657
    %659 = const i64 28
    %660 = select i64 %658, %659, %656
    %661 = const i64 -9223372036854775779
    %662 = icmp eq i64 %547, %661
    %663 = const i64 29
    %664 = select i64 %662, %663, %660
    %665 = const i64 -9223372036854775778
    %666 = icmp eq i64 %547, %665
    %667 = const i64 30
    %668 = select i64 %666, %667, %664
    %669 = const i64 -9223372036854775777
    %670 = icmp eq i64 %547, %669
    %671 = const i64 31
    %672 = select i64 %670, %671, %668
    %673 = const i64 -9223372036854775776
    %674 = icmp eq i64 %547, %673
    %675 = const i64 32
    %676 = select i64 %674, %675, %672
    switch %676 [ 30: bb20 default: bb1 ]
bb7:
    %677 = const i64 8
    %678 = gep i8, ptr %5, %677
    %679 = load ptr, ptr %678
    %680 = load i64, ptr %679
    %681 = const i64 21
    %682 = const i64 -9223372036854775808
    %683 = icmp eq i64 %680, %682
    %684 = const i64 0
    %685 = select i64 %683, %684, %681
    %686 = const i64 -9223372036854775807
    %687 = icmp eq i64 %680, %686
    %688 = const i64 1
    %689 = select i64 %687, %688, %685
    %690 = const i64 -9223372036854775806
    %691 = icmp eq i64 %680, %690
    %692 = const i64 2
    %693 = select i64 %691, %692, %689
    %694 = const i64 -9223372036854775805
    %695 = icmp eq i64 %680, %694
    %696 = const i64 3
    %697 = select i64 %695, %696, %693
    %698 = const i64 -9223372036854775804
    %699 = icmp eq i64 %680, %698
    %700 = const i64 4
    %701 = select i64 %699, %700, %697
    %702 = const i64 -9223372036854775803
    %703 = icmp eq i64 %680, %702
    %704 = const i64 5
    %705 = select i64 %703, %704, %701
    %706 = const i64 -9223372036854775802
    %707 = icmp eq i64 %680, %706
    %708 = const i64 6
    %709 = select i64 %707, %708, %705
    %710 = const i64 -9223372036854775801
    %711 = icmp eq i64 %680, %710
    %712 = const i64 7
    %713 = select i64 %711, %712, %709
    %714 = const i64 -9223372036854775800
    %715 = icmp eq i64 %680, %714
    %716 = const i64 8
    %717 = select i64 %715, %716, %713
    %718 = const i64 -9223372036854775799
    %719 = icmp eq i64 %680, %718
    %720 = const i64 9
    %721 = select i64 %719, %720, %717
    %722 = const i64 -9223372036854775798
    %723 = icmp eq i64 %680, %722
    %724 = const i64 10
    %725 = select i64 %723, %724, %721
    %726 = const i64 -9223372036854775797
    %727 = icmp eq i64 %680, %726
    %728 = const i64 11
    %729 = select i64 %727, %728, %725
    %730 = const i64 -9223372036854775796
    %731 = icmp eq i64 %680, %730
    %732 = const i64 12
    %733 = select i64 %731, %732, %729
    %734 = const i64 -9223372036854775795
    %735 = icmp eq i64 %680, %734
    %736 = const i64 13
    %737 = select i64 %735, %736, %733
    %738 = const i64 -9223372036854775794
    %739 = icmp eq i64 %680, %738
    %740 = const i64 14
    %741 = select i64 %739, %740, %737
    %742 = const i64 -9223372036854775793
    %743 = icmp eq i64 %680, %742
    %744 = const i64 15
    %745 = select i64 %743, %744, %741
    %746 = const i64 -9223372036854775792
    %747 = icmp eq i64 %680, %746
    %748 = const i64 16
    %749 = select i64 %747, %748, %745
    %750 = const i64 -9223372036854775791
    %751 = icmp eq i64 %680, %750
    %752 = const i64 17
    %753 = select i64 %751, %752, %749
    %754 = const i64 -9223372036854775790
    %755 = icmp eq i64 %680, %754
    %756 = const i64 18
    %757 = select i64 %755, %756, %753
    %758 = const i64 -9223372036854775789
    %759 = icmp eq i64 %680, %758
    %760 = const i64 19
    %761 = select i64 %759, %760, %757
    %762 = const i64 -9223372036854775788
    %763 = icmp eq i64 %680, %762
    %764 = const i64 20
    %765 = select i64 %763, %764, %761
    %766 = const i64 -9223372036854775786
    %767 = icmp eq i64 %680, %766
    %768 = const i64 22
    %769 = select i64 %767, %768, %765
    %770 = const i64 -9223372036854775785
    %771 = icmp eq i64 %680, %770
    %772 = const i64 23
    %773 = select i64 %771, %772, %769
    %774 = const i64 -9223372036854775784
    %775 = icmp eq i64 %680, %774
    %776 = const i64 24
    %777 = select i64 %775, %776, %773
    %778 = const i64 -9223372036854775783
    %779 = icmp eq i64 %680, %778
    %780 = const i64 25
    %781 = select i64 %779, %780, %777
    %782 = const i64 -9223372036854775782
    %783 = icmp eq i64 %680, %782
    %784 = const i64 26
    %785 = select i64 %783, %784, %781
    %786 = const i64 -9223372036854775781
    %787 = icmp eq i64 %680, %786
    %788 = const i64 27
    %789 = select i64 %787, %788, %785
    %790 = const i64 -9223372036854775780
    %791 = icmp eq i64 %680, %790
    %792 = const i64 28
    %793 = select i64 %791, %792, %789
    %794 = const i64 -9223372036854775779
    %795 = icmp eq i64 %680, %794
    %796 = const i64 29
    %797 = select i64 %795, %796, %793
    %798 = const i64 -9223372036854775778
    %799 = icmp eq i64 %680, %798
    %800 = const i64 30
    %801 = select i64 %799, %800, %797
    %802 = const i64 -9223372036854775777
    %803 = icmp eq i64 %680, %802
    %804 = const i64 31
    %805 = select i64 %803, %804, %801
    %806 = const i64 -9223372036854775776
    %807 = icmp eq i64 %680, %806
    %808 = const i64 32
    %809 = select i64 %807, %808, %805
    switch %809 [ 29: bb19 default: bb1 ]
bb8:
    %810 = const i64 8
    %811 = gep i8, ptr %5, %810
    %812 = load ptr, ptr %811
    %813 = load i64, ptr %812
    %814 = const i64 21
    %815 = const i64 -9223372036854775808
    %816 = icmp eq i64 %813, %815
    %817 = const i64 0
    %818 = select i64 %816, %817, %814
    %819 = const i64 -9223372036854775807
    %820 = icmp eq i64 %813, %819
    %821 = const i64 1
    %822 = select i64 %820, %821, %818
    %823 = const i64 -9223372036854775806
    %824 = icmp eq i64 %813, %823
    %825 = const i64 2
    %826 = select i64 %824, %825, %822
    %827 = const i64 -9223372036854775805
    %828 = icmp eq i64 %813, %827
    %829 = const i64 3
    %830 = select i64 %828, %829, %826
    %831 = const i64 -9223372036854775804
    %832 = icmp eq i64 %813, %831
    %833 = const i64 4
    %834 = select i64 %832, %833, %830
    %835 = const i64 -9223372036854775803
    %836 = icmp eq i64 %813, %835
    %837 = const i64 5
    %838 = select i64 %836, %837, %834
    %839 = const i64 -9223372036854775802
    %840 = icmp eq i64 %813, %839
    %841 = const i64 6
    %842 = select i64 %840, %841, %838
    %843 = const i64 -9223372036854775801
    %844 = icmp eq i64 %813, %843
    %845 = const i64 7
    %846 = select i64 %844, %845, %842
    %847 = const i64 -9223372036854775800
    %848 = icmp eq i64 %813, %847
    %849 = const i64 8
    %850 = select i64 %848, %849, %846
    %851 = const i64 -9223372036854775799
    %852 = icmp eq i64 %813, %851
    %853 = const i64 9
    %854 = select i64 %852, %853, %850
    %855 = const i64 -9223372036854775798
    %856 = icmp eq i64 %813, %855
    %857 = const i64 10
    %858 = select i64 %856, %857, %854
    %859 = const i64 -9223372036854775797
    %860 = icmp eq i64 %813, %859
    %861 = const i64 11
    %862 = select i64 %860, %861, %858
    %863 = const i64 -9223372036854775796
    %864 = icmp eq i64 %813, %863
    %865 = const i64 12
    %866 = select i64 %864, %865, %862
    %867 = const i64 -9223372036854775795
    %868 = icmp eq i64 %813, %867
    %869 = const i64 13
    %870 = select i64 %868, %869, %866
    %871 = const i64 -9223372036854775794
    %872 = icmp eq i64 %813, %871
    %873 = const i64 14
    %874 = select i64 %872, %873, %870
    %875 = const i64 -9223372036854775793
    %876 = icmp eq i64 %813, %875
    %877 = const i64 15
    %878 = select i64 %876, %877, %874
    %879 = const i64 -9223372036854775792
    %880 = icmp eq i64 %813, %879
    %881 = const i64 16
    %882 = select i64 %880, %881, %878
    %883 = const i64 -9223372036854775791
    %884 = icmp eq i64 %813, %883
    %885 = const i64 17
    %886 = select i64 %884, %885, %882
    %887 = const i64 -9223372036854775790
    %888 = icmp eq i64 %813, %887
    %889 = const i64 18
    %890 = select i64 %888, %889, %886
    %891 = const i64 -9223372036854775789
    %892 = icmp eq i64 %813, %891
    %893 = const i64 19
    %894 = select i64 %892, %893, %890
    %895 = const i64 -9223372036854775788
    %896 = icmp eq i64 %813, %895
    %897 = const i64 20
    %898 = select i64 %896, %897, %894
    %899 = const i64 -9223372036854775786
    %900 = icmp eq i64 %813, %899
    %901 = const i64 22
    %902 = select i64 %900, %901, %898
    %903 = const i64 -9223372036854775785
    %904 = icmp eq i64 %813, %903
    %905 = const i64 23
    %906 = select i64 %904, %905, %902
    %907 = const i64 -9223372036854775784
    %908 = icmp eq i64 %813, %907
    %909 = const i64 24
    %910 = select i64 %908, %909, %906
    %911 = const i64 -9223372036854775783
    %912 = icmp eq i64 %813, %911
    %913 = const i64 25
    %914 = select i64 %912, %913, %910
    %915 = const i64 -9223372036854775782
    %916 = icmp eq i64 %813, %915
    %917 = const i64 26
    %918 = select i64 %916, %917, %914
    %919 = const i64 -9223372036854775781
    %920 = icmp eq i64 %813, %919
    %921 = const i64 27
    %922 = select i64 %920, %921, %918
    %923 = const i64 -9223372036854775780
    %924 = icmp eq i64 %813, %923
    %925 = const i64 28
    %926 = select i64 %924, %925, %922
    %927 = const i64 -9223372036854775779
    %928 = icmp eq i64 %813, %927
    %929 = const i64 29
    %930 = select i64 %928, %929, %926
    %931 = const i64 -9223372036854775778
    %932 = icmp eq i64 %813, %931
    %933 = const i64 30
    %934 = select i64 %932, %933, %930
    %935 = const i64 -9223372036854775777
    %936 = icmp eq i64 %813, %935
    %937 = const i64 31
    %938 = select i64 %936, %937, %934
    %939 = const i64 -9223372036854775776
    %940 = icmp eq i64 %813, %939
    %941 = const i64 32
    %942 = select i64 %940, %941, %938
    switch %942 [ 31: bb18 default: bb1 ]
bb9:
    %943 = const i64 8
    %944 = gep i8, ptr %5, %943
    %945 = load ptr, ptr %944
    %946 = load i64, ptr %945
    %947 = const i64 21
    %948 = const i64 -9223372036854775808
    %949 = icmp eq i64 %946, %948
    %950 = const i64 0
    %951 = select i64 %949, %950, %947
    %952 = const i64 -9223372036854775807
    %953 = icmp eq i64 %946, %952
    %954 = const i64 1
    %955 = select i64 %953, %954, %951
    %956 = const i64 -9223372036854775806
    %957 = icmp eq i64 %946, %956
    %958 = const i64 2
    %959 = select i64 %957, %958, %955
    %960 = const i64 -9223372036854775805
    %961 = icmp eq i64 %946, %960
    %962 = const i64 3
    %963 = select i64 %961, %962, %959
    %964 = const i64 -9223372036854775804
    %965 = icmp eq i64 %946, %964
    %966 = const i64 4
    %967 = select i64 %965, %966, %963
    %968 = const i64 -9223372036854775803
    %969 = icmp eq i64 %946, %968
    %970 = const i64 5
    %971 = select i64 %969, %970, %967
    %972 = const i64 -9223372036854775802
    %973 = icmp eq i64 %946, %972
    %974 = const i64 6
    %975 = select i64 %973, %974, %971
    %976 = const i64 -9223372036854775801
    %977 = icmp eq i64 %946, %976
    %978 = const i64 7
    %979 = select i64 %977, %978, %975
    %980 = const i64 -9223372036854775800
    %981 = icmp eq i64 %946, %980
    %982 = const i64 8
    %983 = select i64 %981, %982, %979
    %984 = const i64 -9223372036854775799
    %985 = icmp eq i64 %946, %984
    %986 = const i64 9
    %987 = select i64 %985, %986, %983
    %988 = const i64 -9223372036854775798
    %989 = icmp eq i64 %946, %988
    %990 = const i64 10
    %991 = select i64 %989, %990, %987
    %992 = const i64 -9223372036854775797
    %993 = icmp eq i64 %946, %992
    %994 = const i64 11
    %995 = select i64 %993, %994, %991
    %996 = const i64 -9223372036854775796
    %997 = icmp eq i64 %946, %996
    %998 = const i64 12
    %999 = select i64 %997, %998, %995
    %1000 = const i64 -9223372036854775795
    %1001 = icmp eq i64 %946, %1000
    %1002 = const i64 13
    %1003 = select i64 %1001, %1002, %999
    %1004 = const i64 -9223372036854775794
    %1005 = icmp eq i64 %946, %1004
    %1006 = const i64 14
    %1007 = select i64 %1005, %1006, %1003
    %1008 = const i64 -9223372036854775793
    %1009 = icmp eq i64 %946, %1008
    %1010 = const i64 15
    %1011 = select i64 %1009, %1010, %1007
    %1012 = const i64 -9223372036854775792
    %1013 = icmp eq i64 %946, %1012
    %1014 = const i64 16
    %1015 = select i64 %1013, %1014, %1011
    %1016 = const i64 -9223372036854775791
    %1017 = icmp eq i64 %946, %1016
    %1018 = const i64 17
    %1019 = select i64 %1017, %1018, %1015
    %1020 = const i64 -9223372036854775790
    %1021 = icmp eq i64 %946, %1020
    %1022 = const i64 18
    %1023 = select i64 %1021, %1022, %1019
    %1024 = const i64 -9223372036854775789
    %1025 = icmp eq i64 %946, %1024
    %1026 = const i64 19
    %1027 = select i64 %1025, %1026, %1023
    %1028 = const i64 -9223372036854775788
    %1029 = icmp eq i64 %946, %1028
    %1030 = const i64 20
    %1031 = select i64 %1029, %1030, %1027
    %1032 = const i64 -9223372036854775786
    %1033 = icmp eq i64 %946, %1032
    %1034 = const i64 22
    %1035 = select i64 %1033, %1034, %1031
    %1036 = const i64 -9223372036854775785
    %1037 = icmp eq i64 %946, %1036
    %1038 = const i64 23
    %1039 = select i64 %1037, %1038, %1035
    %1040 = const i64 -9223372036854775784
    %1041 = icmp eq i64 %946, %1040
    %1042 = const i64 24
    %1043 = select i64 %1041, %1042, %1039
    %1044 = const i64 -9223372036854775783
    %1045 = icmp eq i64 %946, %1044
    %1046 = const i64 25
    %1047 = select i64 %1045, %1046, %1043
    %1048 = const i64 -9223372036854775782
    %1049 = icmp eq i64 %946, %1048
    %1050 = const i64 26
    %1051 = select i64 %1049, %1050, %1047
    %1052 = const i64 -9223372036854775781
    %1053 = icmp eq i64 %946, %1052
    %1054 = const i64 27
    %1055 = select i64 %1053, %1054, %1051
    %1056 = const i64 -9223372036854775780
    %1057 = icmp eq i64 %946, %1056
    %1058 = const i64 28
    %1059 = select i64 %1057, %1058, %1055
    %1060 = const i64 -9223372036854775779
    %1061 = icmp eq i64 %946, %1060
    %1062 = const i64 29
    %1063 = select i64 %1061, %1062, %1059
    %1064 = const i64 -9223372036854775778
    %1065 = icmp eq i64 %946, %1064
    %1066 = const i64 30
    %1067 = select i64 %1065, %1066, %1063
    %1068 = const i64 -9223372036854775777
    %1069 = icmp eq i64 %946, %1068
    %1070 = const i64 31
    %1071 = select i64 %1069, %1070, %1067
    %1072 = const i64 -9223372036854775776
    %1073 = icmp eq i64 %946, %1072
    %1074 = const i64 32
    %1075 = select i64 %1073, %1074, %1071
    switch %1075 [ 32: bb17 default: bb1 ]
bb10:
    %1076 = const i64 8
    %1077 = gep i8, ptr %5, %1076
    %1078 = load ptr, ptr %1077
    %1079 = load i64, ptr %1078
    %1080 = const i64 21
    %1081 = const i64 -9223372036854775808
    %1082 = icmp eq i64 %1079, %1081
    %1083 = const i64 0
    %1084 = select i64 %1082, %1083, %1080
    %1085 = const i64 -9223372036854775807
    %1086 = icmp eq i64 %1079, %1085
    %1087 = const i64 1
    %1088 = select i64 %1086, %1087, %1084
    %1089 = const i64 -9223372036854775806
    %1090 = icmp eq i64 %1079, %1089
    %1091 = const i64 2
    %1092 = select i64 %1090, %1091, %1088
    %1093 = const i64 -9223372036854775805
    %1094 = icmp eq i64 %1079, %1093
    %1095 = const i64 3
    %1096 = select i64 %1094, %1095, %1092
    %1097 = const i64 -9223372036854775804
    %1098 = icmp eq i64 %1079, %1097
    %1099 = const i64 4
    %1100 = select i64 %1098, %1099, %1096
    %1101 = const i64 -9223372036854775803
    %1102 = icmp eq i64 %1079, %1101
    %1103 = const i64 5
    %1104 = select i64 %1102, %1103, %1100
    %1105 = const i64 -9223372036854775802
    %1106 = icmp eq i64 %1079, %1105
    %1107 = const i64 6
    %1108 = select i64 %1106, %1107, %1104
    %1109 = const i64 -9223372036854775801
    %1110 = icmp eq i64 %1079, %1109
    %1111 = const i64 7
    %1112 = select i64 %1110, %1111, %1108
    %1113 = const i64 -9223372036854775800
    %1114 = icmp eq i64 %1079, %1113
    %1115 = const i64 8
    %1116 = select i64 %1114, %1115, %1112
    %1117 = const i64 -9223372036854775799
    %1118 = icmp eq i64 %1079, %1117
    %1119 = const i64 9
    %1120 = select i64 %1118, %1119, %1116
    %1121 = const i64 -9223372036854775798
    %1122 = icmp eq i64 %1079, %1121
    %1123 = const i64 10
    %1124 = select i64 %1122, %1123, %1120
    %1125 = const i64 -9223372036854775797
    %1126 = icmp eq i64 %1079, %1125
    %1127 = const i64 11
    %1128 = select i64 %1126, %1127, %1124
    %1129 = const i64 -9223372036854775796
    %1130 = icmp eq i64 %1079, %1129
    %1131 = const i64 12
    %1132 = select i64 %1130, %1131, %1128
    %1133 = const i64 -9223372036854775795
    %1134 = icmp eq i64 %1079, %1133
    %1135 = const i64 13
    %1136 = select i64 %1134, %1135, %1132
    %1137 = const i64 -9223372036854775794
    %1138 = icmp eq i64 %1079, %1137
    %1139 = const i64 14
    %1140 = select i64 %1138, %1139, %1136
    %1141 = const i64 -9223372036854775793
    %1142 = icmp eq i64 %1079, %1141
    %1143 = const i64 15
    %1144 = select i64 %1142, %1143, %1140
    %1145 = const i64 -9223372036854775792
    %1146 = icmp eq i64 %1079, %1145
    %1147 = const i64 16
    %1148 = select i64 %1146, %1147, %1144
    %1149 = const i64 -9223372036854775791
    %1150 = icmp eq i64 %1079, %1149
    %1151 = const i64 17
    %1152 = select i64 %1150, %1151, %1148
    %1153 = const i64 -9223372036854775790
    %1154 = icmp eq i64 %1079, %1153
    %1155 = const i64 18
    %1156 = select i64 %1154, %1155, %1152
    %1157 = const i64 -9223372036854775789
    %1158 = icmp eq i64 %1079, %1157
    %1159 = const i64 19
    %1160 = select i64 %1158, %1159, %1156
    %1161 = const i64 -9223372036854775788
    %1162 = icmp eq i64 %1079, %1161
    %1163 = const i64 20
    %1164 = select i64 %1162, %1163, %1160
    %1165 = const i64 -9223372036854775786
    %1166 = icmp eq i64 %1079, %1165
    %1167 = const i64 22
    %1168 = select i64 %1166, %1167, %1164
    %1169 = const i64 -9223372036854775785
    %1170 = icmp eq i64 %1079, %1169
    %1171 = const i64 23
    %1172 = select i64 %1170, %1171, %1168
    %1173 = const i64 -9223372036854775784
    %1174 = icmp eq i64 %1079, %1173
    %1175 = const i64 24
    %1176 = select i64 %1174, %1175, %1172
    %1177 = const i64 -9223372036854775783
    %1178 = icmp eq i64 %1079, %1177
    %1179 = const i64 25
    %1180 = select i64 %1178, %1179, %1176
    %1181 = const i64 -9223372036854775782
    %1182 = icmp eq i64 %1079, %1181
    %1183 = const i64 26
    %1184 = select i64 %1182, %1183, %1180
    %1185 = const i64 -9223372036854775781
    %1186 = icmp eq i64 %1079, %1185
    %1187 = const i64 27
    %1188 = select i64 %1186, %1187, %1184
    %1189 = const i64 -9223372036854775780
    %1190 = icmp eq i64 %1079, %1189
    %1191 = const i64 28
    %1192 = select i64 %1190, %1191, %1188
    %1193 = const i64 -9223372036854775779
    %1194 = icmp eq i64 %1079, %1193
    %1195 = const i64 29
    %1196 = select i64 %1194, %1195, %1192
    %1197 = const i64 -9223372036854775778
    %1198 = icmp eq i64 %1079, %1197
    %1199 = const i64 30
    %1200 = select i64 %1198, %1199, %1196
    %1201 = const i64 -9223372036854775777
    %1202 = icmp eq i64 %1079, %1201
    %1203 = const i64 31
    %1204 = select i64 %1202, %1203, %1200
    %1205 = const i64 -9223372036854775776
    %1206 = icmp eq i64 %1079, %1205
    %1207 = const i64 32
    %1208 = select i64 %1206, %1207, %1204
    switch %1208 [ 23: bb16 default: bb1 ]
bb11:
    %1209 = const i64 8
    %1210 = gep i8, ptr %5, %1209
    %1211 = load ptr, ptr %1210
    %1212 = load i64, ptr %1211
    %1213 = const i64 21
    %1214 = const i64 -9223372036854775808
    %1215 = icmp eq i64 %1212, %1214
    %1216 = const i64 0
    %1217 = select i64 %1215, %1216, %1213
    %1218 = const i64 -9223372036854775807
    %1219 = icmp eq i64 %1212, %1218
    %1220 = const i64 1
    %1221 = select i64 %1219, %1220, %1217
    %1222 = const i64 -9223372036854775806
    %1223 = icmp eq i64 %1212, %1222
    %1224 = const i64 2
    %1225 = select i64 %1223, %1224, %1221
    %1226 = const i64 -9223372036854775805
    %1227 = icmp eq i64 %1212, %1226
    %1228 = const i64 3
    %1229 = select i64 %1227, %1228, %1225
    %1230 = const i64 -9223372036854775804
    %1231 = icmp eq i64 %1212, %1230
    %1232 = const i64 4
    %1233 = select i64 %1231, %1232, %1229
    %1234 = const i64 -9223372036854775803
    %1235 = icmp eq i64 %1212, %1234
    %1236 = const i64 5
    %1237 = select i64 %1235, %1236, %1233
    %1238 = const i64 -9223372036854775802
    %1239 = icmp eq i64 %1212, %1238
    %1240 = const i64 6
    %1241 = select i64 %1239, %1240, %1237
    %1242 = const i64 -9223372036854775801
    %1243 = icmp eq i64 %1212, %1242
    %1244 = const i64 7
    %1245 = select i64 %1243, %1244, %1241
    %1246 = const i64 -9223372036854775800
    %1247 = icmp eq i64 %1212, %1246
    %1248 = const i64 8
    %1249 = select i64 %1247, %1248, %1245
    %1250 = const i64 -9223372036854775799
    %1251 = icmp eq i64 %1212, %1250
    %1252 = const i64 9
    %1253 = select i64 %1251, %1252, %1249
    %1254 = const i64 -9223372036854775798
    %1255 = icmp eq i64 %1212, %1254
    %1256 = const i64 10
    %1257 = select i64 %1255, %1256, %1253
    %1258 = const i64 -9223372036854775797
    %1259 = icmp eq i64 %1212, %1258
    %1260 = const i64 11
    %1261 = select i64 %1259, %1260, %1257
    %1262 = const i64 -9223372036854775796
    %1263 = icmp eq i64 %1212, %1262
    %1264 = const i64 12
    %1265 = select i64 %1263, %1264, %1261
    %1266 = const i64 -9223372036854775795
    %1267 = icmp eq i64 %1212, %1266
    %1268 = const i64 13
    %1269 = select i64 %1267, %1268, %1265
    %1270 = const i64 -9223372036854775794
    %1271 = icmp eq i64 %1212, %1270
    %1272 = const i64 14
    %1273 = select i64 %1271, %1272, %1269
    %1274 = const i64 -9223372036854775793
    %1275 = icmp eq i64 %1212, %1274
    %1276 = const i64 15
    %1277 = select i64 %1275, %1276, %1273
    %1278 = const i64 -9223372036854775792
    %1279 = icmp eq i64 %1212, %1278
    %1280 = const i64 16
    %1281 = select i64 %1279, %1280, %1277
    %1282 = const i64 -9223372036854775791
    %1283 = icmp eq i64 %1212, %1282
    %1284 = const i64 17
    %1285 = select i64 %1283, %1284, %1281
    %1286 = const i64 -9223372036854775790
    %1287 = icmp eq i64 %1212, %1286
    %1288 = const i64 18
    %1289 = select i64 %1287, %1288, %1285
    %1290 = const i64 -9223372036854775789
    %1291 = icmp eq i64 %1212, %1290
    %1292 = const i64 19
    %1293 = select i64 %1291, %1292, %1289
    %1294 = const i64 -9223372036854775788
    %1295 = icmp eq i64 %1212, %1294
    %1296 = const i64 20
    %1297 = select i64 %1295, %1296, %1293
    %1298 = const i64 -9223372036854775786
    %1299 = icmp eq i64 %1212, %1298
    %1300 = const i64 22
    %1301 = select i64 %1299, %1300, %1297
    %1302 = const i64 -9223372036854775785
    %1303 = icmp eq i64 %1212, %1302
    %1304 = const i64 23
    %1305 = select i64 %1303, %1304, %1301
    %1306 = const i64 -9223372036854775784
    %1307 = icmp eq i64 %1212, %1306
    %1308 = const i64 24
    %1309 = select i64 %1307, %1308, %1305
    %1310 = const i64 -9223372036854775783
    %1311 = icmp eq i64 %1212, %1310
    %1312 = const i64 25
    %1313 = select i64 %1311, %1312, %1309
    %1314 = const i64 -9223372036854775782
    %1315 = icmp eq i64 %1212, %1314
    %1316 = const i64 26
    %1317 = select i64 %1315, %1316, %1313
    %1318 = const i64 -9223372036854775781
    %1319 = icmp eq i64 %1212, %1318
    %1320 = const i64 27
    %1321 = select i64 %1319, %1320, %1317
    %1322 = const i64 -9223372036854775780
    %1323 = icmp eq i64 %1212, %1322
    %1324 = const i64 28
    %1325 = select i64 %1323, %1324, %1321
    %1326 = const i64 -9223372036854775779
    %1327 = icmp eq i64 %1212, %1326
    %1328 = const i64 29
    %1329 = select i64 %1327, %1328, %1325
    %1330 = const i64 -9223372036854775778
    %1331 = icmp eq i64 %1212, %1330
    %1332 = const i64 30
    %1333 = select i64 %1331, %1332, %1329
    %1334 = const i64 -9223372036854775777
    %1335 = icmp eq i64 %1212, %1334
    %1336 = const i64 31
    %1337 = select i64 %1335, %1336, %1333
    %1338 = const i64 -9223372036854775776
    %1339 = icmp eq i64 %1212, %1338
    %1340 = const i64 32
    %1341 = select i64 %1339, %1340, %1337
    switch %1341 [ 15: bb15 23: bb14 default: bb1 ]
bb12:
    %1342 = const i64 8
    %1343 = gep i8, ptr %5, %1342
    %1344 = load ptr, ptr %1343
    %1345 = load i64, ptr %1344
    %1346 = const i64 21
    %1347 = const i64 -9223372036854775808
    %1348 = icmp eq i64 %1345, %1347
    %1349 = const i64 0
    %1350 = select i64 %1348, %1349, %1346
    %1351 = const i64 -9223372036854775807
    %1352 = icmp eq i64 %1345, %1351
    %1353 = const i64 1
    %1354 = select i64 %1352, %1353, %1350
    %1355 = const i64 -9223372036854775806
    %1356 = icmp eq i64 %1345, %1355
    %1357 = const i64 2
    %1358 = select i64 %1356, %1357, %1354
    %1359 = const i64 -9223372036854775805
    %1360 = icmp eq i64 %1345, %1359
    %1361 = const i64 3
    %1362 = select i64 %1360, %1361, %1358
    %1363 = const i64 -9223372036854775804
    %1364 = icmp eq i64 %1345, %1363
    %1365 = const i64 4
    %1366 = select i64 %1364, %1365, %1362
    %1367 = const i64 -9223372036854775803
    %1368 = icmp eq i64 %1345, %1367
    %1369 = const i64 5
    %1370 = select i64 %1368, %1369, %1366
    %1371 = const i64 -9223372036854775802
    %1372 = icmp eq i64 %1345, %1371
    %1373 = const i64 6
    %1374 = select i64 %1372, %1373, %1370
    %1375 = const i64 -9223372036854775801
    %1376 = icmp eq i64 %1345, %1375
    %1377 = const i64 7
    %1378 = select i64 %1376, %1377, %1374
    %1379 = const i64 -9223372036854775800
    %1380 = icmp eq i64 %1345, %1379
    %1381 = const i64 8
    %1382 = select i64 %1380, %1381, %1378
    %1383 = const i64 -9223372036854775799
    %1384 = icmp eq i64 %1345, %1383
    %1385 = const i64 9
    %1386 = select i64 %1384, %1385, %1382
    %1387 = const i64 -9223372036854775798
    %1388 = icmp eq i64 %1345, %1387
    %1389 = const i64 10
    %1390 = select i64 %1388, %1389, %1386
    %1391 = const i64 -9223372036854775797
    %1392 = icmp eq i64 %1345, %1391
    %1393 = const i64 11
    %1394 = select i64 %1392, %1393, %1390
    %1395 = const i64 -9223372036854775796
    %1396 = icmp eq i64 %1345, %1395
    %1397 = const i64 12
    %1398 = select i64 %1396, %1397, %1394
    %1399 = const i64 -9223372036854775795
    %1400 = icmp eq i64 %1345, %1399
    %1401 = const i64 13
    %1402 = select i64 %1400, %1401, %1398
    %1403 = const i64 -9223372036854775794
    %1404 = icmp eq i64 %1345, %1403
    %1405 = const i64 14
    %1406 = select i64 %1404, %1405, %1402
    %1407 = const i64 -9223372036854775793
    %1408 = icmp eq i64 %1345, %1407
    %1409 = const i64 15
    %1410 = select i64 %1408, %1409, %1406
    %1411 = const i64 -9223372036854775792
    %1412 = icmp eq i64 %1345, %1411
    %1413 = const i64 16
    %1414 = select i64 %1412, %1413, %1410
    %1415 = const i64 -9223372036854775791
    %1416 = icmp eq i64 %1345, %1415
    %1417 = const i64 17
    %1418 = select i64 %1416, %1417, %1414
    %1419 = const i64 -9223372036854775790
    %1420 = icmp eq i64 %1345, %1419
    %1421 = const i64 18
    %1422 = select i64 %1420, %1421, %1418
    %1423 = const i64 -9223372036854775789
    %1424 = icmp eq i64 %1345, %1423
    %1425 = const i64 19
    %1426 = select i64 %1424, %1425, %1422
    %1427 = const i64 -9223372036854775788
    %1428 = icmp eq i64 %1345, %1427
    %1429 = const i64 20
    %1430 = select i64 %1428, %1429, %1426
    %1431 = const i64 -9223372036854775786
    %1432 = icmp eq i64 %1345, %1431
    %1433 = const i64 22
    %1434 = select i64 %1432, %1433, %1430
    %1435 = const i64 -9223372036854775785
    %1436 = icmp eq i64 %1345, %1435
    %1437 = const i64 23
    %1438 = select i64 %1436, %1437, %1434
    %1439 = const i64 -9223372036854775784
    %1440 = icmp eq i64 %1345, %1439
    %1441 = const i64 24
    %1442 = select i64 %1440, %1441, %1438
    %1443 = const i64 -9223372036854775783
    %1444 = icmp eq i64 %1345, %1443
    %1445 = const i64 25
    %1446 = select i64 %1444, %1445, %1442
    %1447 = const i64 -9223372036854775782
    %1448 = icmp eq i64 %1345, %1447
    %1449 = const i64 26
    %1450 = select i64 %1448, %1449, %1446
    %1451 = const i64 -9223372036854775781
    %1452 = icmp eq i64 %1345, %1451
    %1453 = const i64 27
    %1454 = select i64 %1452, %1453, %1450
    %1455 = const i64 -9223372036854775780
    %1456 = icmp eq i64 %1345, %1455
    %1457 = const i64 28
    %1458 = select i64 %1456, %1457, %1454
    %1459 = const i64 -9223372036854775779
    %1460 = icmp eq i64 %1345, %1459
    %1461 = const i64 29
    %1462 = select i64 %1460, %1461, %1458
    %1463 = const i64 -9223372036854775778
    %1464 = icmp eq i64 %1345, %1463
    %1465 = const i64 30
    %1466 = select i64 %1464, %1465, %1462
    %1467 = const i64 -9223372036854775777
    %1468 = icmp eq i64 %1345, %1467
    %1469 = const i64 31
    %1470 = select i64 %1468, %1469, %1466
    %1471 = const i64 -9223372036854775776
    %1472 = icmp eq i64 %1345, %1471
    %1473 = const i64 32
    %1474 = select i64 %1472, %1473, %1470
    switch %1474 [ 17: bb13 default: bb1 ]
bb13:
    %1475 = const bool true
    br bb33(%1475)
bb14:
    %1476 = const bool true
    br bb33(%1476)
bb15:
    %1477 = const bool true
    br bb33(%1477)
bb16:
    %1478 = const bool true
    br bb33(%1478)
bb17:
    %1479 = const bool true
    br bb33(%1479)
bb18:
    %1480 = const bool true
    br bb33(%1480)
bb19:
    %1481 = const bool true
    br bb33(%1481)
bb20:
    %1482 = const bool true
    br bb33(%1482)
bb21:
    %1483 = const bool true
    br bb33(%1483)
bb22:
    %1484 = const bool true
    br bb33(%1484)
bb23:
    %1485 = const bool true
    br bb33(%1485)
bb24:
    %1486 = const bool true
    br bb33(%1486)
bb25:
    %1487 = const i64 8
    %1488 = gep i8, ptr %5, %1487
    %1489 = load ptr, ptr %1488
    %1490 = call @func.9(%1489)
    br bb31(%1490)
bb26:
    %1491 = const bool true
    br bb33(%1491)
bb27:
    %1492 = const i64 8
    %1493 = gep i8, ptr %5, %1492
    %1494 = load ptr, ptr %1493
    %1495 = call @func.5(%1494)
    br bb28(%1495)
bb28(%2: bool):
    condbr %2, bb29, bb30
bb29:
    %1496 = const i64 8
    %1497 = gep i8, ptr %5, %1496
    %1498 = load ptr, ptr %1497
    %1499 = const bool true
    br bb33(%1499)
bb30:
    %1500 = const i64 8
    %1501 = gep i8, ptr %5, %1500
    %1502 = load ptr, ptr %1501
    %1503 = load i64, ptr %1502
    %1504 = const i64 21
    %1505 = const i64 -9223372036854775808
    %1506 = icmp eq i64 %1503, %1505
    %1507 = const i64 0
    %1508 = select i64 %1506, %1507, %1504
    %1509 = const i64 -9223372036854775807
    %1510 = icmp eq i64 %1503, %1509
    %1511 = const i64 1
    %1512 = select i64 %1510, %1511, %1508
    %1513 = const i64 -9223372036854775806
    %1514 = icmp eq i64 %1503, %1513
    %1515 = const i64 2
    %1516 = select i64 %1514, %1515, %1512
    %1517 = const i64 -9223372036854775805
    %1518 = icmp eq i64 %1503, %1517
    %1519 = const i64 3
    %1520 = select i64 %1518, %1519, %1516
    %1521 = const i64 -9223372036854775804
    %1522 = icmp eq i64 %1503, %1521
    %1523 = const i64 4
    %1524 = select i64 %1522, %1523, %1520
    %1525 = const i64 -9223372036854775803
    %1526 = icmp eq i64 %1503, %1525
    %1527 = const i64 5
    %1528 = select i64 %1526, %1527, %1524
    %1529 = const i64 -9223372036854775802
    %1530 = icmp eq i64 %1503, %1529
    %1531 = const i64 6
    %1532 = select i64 %1530, %1531, %1528
    %1533 = const i64 -9223372036854775801
    %1534 = icmp eq i64 %1503, %1533
    %1535 = const i64 7
    %1536 = select i64 %1534, %1535, %1532
    %1537 = const i64 -9223372036854775800
    %1538 = icmp eq i64 %1503, %1537
    %1539 = const i64 8
    %1540 = select i64 %1538, %1539, %1536
    %1541 = const i64 -9223372036854775799
    %1542 = icmp eq i64 %1503, %1541
    %1543 = const i64 9
    %1544 = select i64 %1542, %1543, %1540
    %1545 = const i64 -9223372036854775798
    %1546 = icmp eq i64 %1503, %1545
    %1547 = const i64 10
    %1548 = select i64 %1546, %1547, %1544
    %1549 = const i64 -9223372036854775797
    %1550 = icmp eq i64 %1503, %1549
    %1551 = const i64 11
    %1552 = select i64 %1550, %1551, %1548
    %1553 = const i64 -9223372036854775796
    %1554 = icmp eq i64 %1503, %1553
    %1555 = const i64 12
    %1556 = select i64 %1554, %1555, %1552
    %1557 = const i64 -9223372036854775795
    %1558 = icmp eq i64 %1503, %1557
    %1559 = const i64 13
    %1560 = select i64 %1558, %1559, %1556
    %1561 = const i64 -9223372036854775794
    %1562 = icmp eq i64 %1503, %1561
    %1563 = const i64 14
    %1564 = select i64 %1562, %1563, %1560
    %1565 = const i64 -9223372036854775793
    %1566 = icmp eq i64 %1503, %1565
    %1567 = const i64 15
    %1568 = select i64 %1566, %1567, %1564
    %1569 = const i64 -9223372036854775792
    %1570 = icmp eq i64 %1503, %1569
    %1571 = const i64 16
    %1572 = select i64 %1570, %1571, %1568
    %1573 = const i64 -9223372036854775791
    %1574 = icmp eq i64 %1503, %1573
    %1575 = const i64 17
    %1576 = select i64 %1574, %1575, %1572
    %1577 = const i64 -9223372036854775790
    %1578 = icmp eq i64 %1503, %1577
    %1579 = const i64 18
    %1580 = select i64 %1578, %1579, %1576
    %1581 = const i64 -9223372036854775789
    %1582 = icmp eq i64 %1503, %1581
    %1583 = const i64 19
    %1584 = select i64 %1582, %1583, %1580
    %1585 = const i64 -9223372036854775788
    %1586 = icmp eq i64 %1503, %1585
    %1587 = const i64 20
    %1588 = select i64 %1586, %1587, %1584
    %1589 = const i64 -9223372036854775786
    %1590 = icmp eq i64 %1503, %1589
    %1591 = const i64 22
    %1592 = select i64 %1590, %1591, %1588
    %1593 = const i64 -9223372036854775785
    %1594 = icmp eq i64 %1503, %1593
    %1595 = const i64 23
    %1596 = select i64 %1594, %1595, %1592
    %1597 = const i64 -9223372036854775784
    %1598 = icmp eq i64 %1503, %1597
    %1599 = const i64 24
    %1600 = select i64 %1598, %1599, %1596
    %1601 = const i64 -9223372036854775783
    %1602 = icmp eq i64 %1503, %1601
    %1603 = const i64 25
    %1604 = select i64 %1602, %1603, %1600
    %1605 = const i64 -9223372036854775782
    %1606 = icmp eq i64 %1503, %1605
    %1607 = const i64 26
    %1608 = select i64 %1606, %1607, %1604
    %1609 = const i64 -9223372036854775781
    %1610 = icmp eq i64 %1503, %1609
    %1611 = const i64 27
    %1612 = select i64 %1610, %1611, %1608
    %1613 = const i64 -9223372036854775780
    %1614 = icmp eq i64 %1503, %1613
    %1615 = const i64 28
    %1616 = select i64 %1614, %1615, %1612
    %1617 = const i64 -9223372036854775779
    %1618 = icmp eq i64 %1503, %1617
    %1619 = const i64 29
    %1620 = select i64 %1618, %1619, %1616
    %1621 = const i64 -9223372036854775778
    %1622 = icmp eq i64 %1503, %1621
    %1623 = const i64 30
    %1624 = select i64 %1622, %1623, %1620
    %1625 = const i64 -9223372036854775777
    %1626 = icmp eq i64 %1503, %1625
    %1627 = const i64 31
    %1628 = select i64 %1626, %1627, %1624
    %1629 = const i64 -9223372036854775776
    %1630 = icmp eq i64 %1503, %1629
    %1631 = const i64 32
    %1632 = select i64 %1630, %1631, %1628
    switch %1632 [ 15: bb26 default: bb1 ]
bb31(%3: bool):
    condbr %3, bb32, bb1
bb32:
    %1633 = const i64 8
    %1634 = gep i8, ptr %5, %1633
    %1635 = load ptr, ptr %1634
    %1636 = const bool true
    br bb33(%1636)
bb33(%4: bool):
    ret %4
bb34:
    unreachable
}

fn @Ty__is_integer(functy.5) {
bb0(%0: ptr):
    %5 = call @func.10(%0)
    br bb1(%0, %5)
bb1(%1: ptr, %2: bool):
    condbr %2, bb2, bb3(%1)
bb2:
    %6 = const bool true
    br bb4(%6)
bb3(%3: ptr):
    %7 = call @func.11(%3)
    br bb4(%7)
bb4(%4: bool):
    ret %4
}

fn @int_value_fits_ty(functy.6) {
bb0(%0: i128, %1: ptr):
    %20 = load i64, ptr %1
    %21 = const i64 21
    %22 = const i64 -9223372036854775808
    %23 = icmp eq i64 %20, %22
    %24 = const i64 0
    %25 = select i64 %23, %24, %21
    %26 = const i64 -9223372036854775807
    %27 = icmp eq i64 %20, %26
    %28 = const i64 1
    %29 = select i64 %27, %28, %25
    %30 = const i64 -9223372036854775806
    %31 = icmp eq i64 %20, %30
    %32 = const i64 2
    %33 = select i64 %31, %32, %29
    %34 = const i64 -9223372036854775805
    %35 = icmp eq i64 %20, %34
    %36 = const i64 3
    %37 = select i64 %35, %36, %33
    %38 = const i64 -9223372036854775804
    %39 = icmp eq i64 %20, %38
    %40 = const i64 4
    %41 = select i64 %39, %40, %37
    %42 = const i64 -9223372036854775803
    %43 = icmp eq i64 %20, %42
    %44 = const i64 5
    %45 = select i64 %43, %44, %41
    %46 = const i64 -9223372036854775802
    %47 = icmp eq i64 %20, %46
    %48 = const i64 6
    %49 = select i64 %47, %48, %45
    %50 = const i64 -9223372036854775801
    %51 = icmp eq i64 %20, %50
    %52 = const i64 7
    %53 = select i64 %51, %52, %49
    %54 = const i64 -9223372036854775800
    %55 = icmp eq i64 %20, %54
    %56 = const i64 8
    %57 = select i64 %55, %56, %53
    %58 = const i64 -9223372036854775799
    %59 = icmp eq i64 %20, %58
    %60 = const i64 9
    %61 = select i64 %59, %60, %57
    %62 = const i64 -9223372036854775798
    %63 = icmp eq i64 %20, %62
    %64 = const i64 10
    %65 = select i64 %63, %64, %61
    %66 = const i64 -9223372036854775797
    %67 = icmp eq i64 %20, %66
    %68 = const i64 11
    %69 = select i64 %67, %68, %65
    %70 = const i64 -9223372036854775796
    %71 = icmp eq i64 %20, %70
    %72 = const i64 12
    %73 = select i64 %71, %72, %69
    %74 = const i64 -9223372036854775795
    %75 = icmp eq i64 %20, %74
    %76 = const i64 13
    %77 = select i64 %75, %76, %73
    %78 = const i64 -9223372036854775794
    %79 = icmp eq i64 %20, %78
    %80 = const i64 14
    %81 = select i64 %79, %80, %77
    %82 = const i64 -9223372036854775793
    %83 = icmp eq i64 %20, %82
    %84 = const i64 15
    %85 = select i64 %83, %84, %81
    %86 = const i64 -9223372036854775792
    %87 = icmp eq i64 %20, %86
    %88 = const i64 16
    %89 = select i64 %87, %88, %85
    %90 = const i64 -9223372036854775791
    %91 = icmp eq i64 %20, %90
    %92 = const i64 17
    %93 = select i64 %91, %92, %89
    %94 = const i64 -9223372036854775790
    %95 = icmp eq i64 %20, %94
    %96 = const i64 18
    %97 = select i64 %95, %96, %93
    %98 = const i64 -9223372036854775789
    %99 = icmp eq i64 %20, %98
    %100 = const i64 19
    %101 = select i64 %99, %100, %97
    %102 = const i64 -9223372036854775788
    %103 = icmp eq i64 %20, %102
    %104 = const i64 20
    %105 = select i64 %103, %104, %101
    %106 = const i64 -9223372036854775786
    %107 = icmp eq i64 %20, %106
    %108 = const i64 22
    %109 = select i64 %107, %108, %105
    %110 = const i64 -9223372036854775785
    %111 = icmp eq i64 %20, %110
    %112 = const i64 23
    %113 = select i64 %111, %112, %109
    %114 = const i64 -9223372036854775784
    %115 = icmp eq i64 %20, %114
    %116 = const i64 24
    %117 = select i64 %115, %116, %113
    %118 = const i64 -9223372036854775783
    %119 = icmp eq i64 %20, %118
    %120 = const i64 25
    %121 = select i64 %119, %120, %117
    %122 = const i64 -9223372036854775782
    %123 = icmp eq i64 %20, %122
    %124 = const i64 26
    %125 = select i64 %123, %124, %121
    %126 = const i64 -9223372036854775781
    %127 = icmp eq i64 %20, %126
    %128 = const i64 27
    %129 = select i64 %127, %128, %125
    %130 = const i64 -9223372036854775780
    %131 = icmp eq i64 %20, %130
    %132 = const i64 28
    %133 = select i64 %131, %132, %129
    %134 = const i64 -9223372036854775779
    %135 = icmp eq i64 %20, %134
    %136 = const i64 29
    %137 = select i64 %135, %136, %133
    %138 = const i64 -9223372036854775778
    %139 = icmp eq i64 %20, %138
    %140 = const i64 30
    %141 = select i64 %139, %140, %137
    %142 = const i64 -9223372036854775777
    %143 = icmp eq i64 %20, %142
    %144 = const i64 31
    %145 = select i64 %143, %144, %141
    %146 = const i64 -9223372036854775776
    %147 = icmp eq i64 %20, %146
    %148 = const i64 32
    %149 = select i64 %147, %148, %145
    switch %149 [ 0: bb11(%0) 1: bb10(%0) 2: bb9(%0) 3: bb8(%0) 4: bb7 5: bb6(%0) 6: bb5(%0) 7: bb4(%0) 8: bb3(%0) 9: bb2(%0) default: bb1 ]
bb1:
    %150 = const bool false
    br bb28(%150)
bb2(%2: i128):
    %151 = const i128 0
    %152 = icmp sge i128 %2, %151
    br bb28(%152)
bb3(%3: i128):
    %153 = const i128 0
    %154 = icmp sge i128 %3, %153
    condbr %154, bb26(%3), bb27
bb4(%4: i128):
    %155 = const i128 0
    %156 = icmp sge i128 %4, %155
    condbr %156, bb24(%4), bb25
bb5(%5: i128):
    %157 = const i128 0
    %158 = icmp sge i128 %5, %157
    condbr %158, bb22(%5), bb23
bb6(%6: i128):
    %159 = const i128 0
    %160 = icmp sge i128 %6, %159
    condbr %160, bb20(%6), bb21
bb7:
    %161 = const bool true
    br bb28(%161)
bb8(%7: i128):
    %162 = const i64 -9223372036854775808
    %163 = sext i64 %162 to i128
    %164 = icmp sge i128 %7, %163
    condbr %164, bb18(%7), bb19
bb9(%8: i128):
    %165 = const i32 -2147483648
    %166 = sext i32 %165 to i128
    %167 = icmp sge i128 %8, %166
    condbr %167, bb16(%8), bb17
bb10(%9: i128):
    %168 = const i16 -32768
    %169 = sext i16 %168 to i128
    %170 = icmp sge i128 %9, %169
    condbr %170, bb14(%9), bb15
bb11(%10: i128):
    %171 = const i8 -128
    %172 = sext i8 %171 to i128
    %173 = icmp sge i128 %10, %172
    condbr %173, bb12(%10), bb13
bb12(%11: i128):
    %174 = const i8 127
    %175 = sext i8 %174 to i128
    %176 = icmp sle i128 %11, %175
    br bb28(%176)
bb13:
    %177 = const bool false
    br bb28(%177)
bb14(%12: i128):
    %178 = const i16 32767
    %179 = sext i16 %178 to i128
    %180 = icmp sle i128 %12, %179
    br bb28(%180)
bb15:
    %181 = const bool false
    br bb28(%181)
bb16(%13: i128):
    %182 = const i32 2147483647
    %183 = sext i32 %182 to i128
    %184 = icmp sle i128 %13, %183
    br bb28(%184)
bb17:
    %185 = const bool false
    br bb28(%185)
bb18(%14: i128):
    %186 = const i64 9223372036854775807
    %187 = sext i64 %186 to i128
    %188 = icmp sle i128 %14, %187
    br bb28(%188)
bb19:
    %189 = const bool false
    br bb28(%189)
bb20(%15: i128):
    %190 = const u8 255
    %191 = zext u8 %190 to i128
    %192 = icmp sle i128 %15, %191
    br bb28(%192)
bb21:
    %193 = const bool false
    br bb28(%193)
bb22(%16: i128):
    %194 = const u16 65535
    %195 = zext u16 %194 to i128
    %196 = icmp sle i128 %16, %195
    br bb28(%196)
bb23:
    %197 = const bool false
    br bb28(%197)
bb24(%17: i128):
    %198 = const u32 4294967295
    %199 = zext u32 %198 to i128
    %200 = icmp sle i128 %17, %199
    br bb28(%200)
bb25:
    %201 = const bool false
    br bb28(%201)
bb26(%18: i128):
    %202 = const u64 18446744073709551615
    %203 = zext u64 %202 to i128
    %204 = icmp sle i128 %18, %203
    br bb28(%204)
bb27:
    %205 = const bool false
    br bb28(%205)
bb28(%19: bool):
    ret %19
}

fn @_RNvNvMs9_NtCs2EYQwhfuABO_4core3numj13unchecked_sub18precondition_checkCs8vhpJKEIjU0_25trust_value_matches_slice(functy.7) {
}

fn @_std__slice__Iter__a__T__as_std__iter__Iterator___all__mono1fb6f13493f87eef(functy.8) {
bb0(%0: ptr, %1: ptr):
    %20 = alloca i64, align 8
    %21 = alloca i64, align 8
    %22 = alloca i64, align 8
    %23 = alloca i64, align 8
    %24 = alloca i64, align 8
    %25 = alloca i64, align 8
    br bb1(%0)
bb1(%2: ptr):
    %26 = load i64, ptr %2
    store i64 %26, ptr %22
    %27 = const i64 8
    %28 = gep i8, ptr %2, %27
    %29 = load ptr, ptr %28
    %30 = const bool false
    condbr %30, bb6(%2, %29), bb9(%2, %29)
bb2(%3: ptr, %4: bool):
    condbr %4, bb3(%3), bb4
bb3(%5: ptr):
    br bb1(%5)
bb4:
    %31 = const bool false
    br bb5(%31)
bb5(%6: bool):
    ret %6
bb6(%7: ptr, %8: ptr):
    %32 = ptrtoint ptr %8 to u64
    switch %32 [ 0: bb7 default: bb8(%7, %32) ]
bb7:
    br bb15
bb8(%9: ptr, %10: u64):
    %33 = const bool true
    condbr %33, bb13(%9, %10), bb14(%9, %10)
bb9(%11: ptr, %12: ptr):
    store ptr %12, ptr %23
    %34 = load ptr, ptr %22
    %35 = load ptr, ptr %23
    %36 = icmp eq ptr %34, %35
    condbr %36, bb10, bb11(%11, %34)
bb10:
    br bb15
bb11(%13: ptr, %14: ptr):
    %37 = const u64 1
    %38 = bitcast u64 %37 to i64
    %39 = const i64 48
    %40 = mul i64 %38, %39
    %41 = gep i8, ptr %14, %40
    store ptr %41, ptr %24
    %42 = load i64, ptr %24
    store i64 %42, ptr %13
    br bb12(%13)
bb12(%15: ptr):
    %43 = load ptr, ptr %22
    store ptr %43, ptr %25
    %44 = load ptr, ptr %25
    store ptr %44, ptr %20
    %45 = load ptr, ptr %20
    store ptr %45, ptr %21
    %46 = load ptr, ptr %21
    %47 = call @func.12(%1, %46)
    br bb2(%15, %47)
bb13(%16: ptr, %17: u64):
    %48 = const u64 1
    call @func.7(%17, %48)
    br bb14(%16, %17)
bb14(%18: ptr, %19: u64):
    %49 = const u64 1
    %50 = sub u64 %19, %49
    %51 = inttoptr u64 %50 to ptr
    %52 = const i64 8
    %53 = gep i8, ptr %18, %52
    store ptr %51, ptr %53
    br bb12(%18)
bb15:
    %54 = const bool true
    br bb5(%54)
}

fn @Ty__is_float(functy.9) {
bb0(%0: ptr):
    %2 = load i64, ptr %0
    %3 = const i64 21
    %4 = const i64 -9223372036854775808
    %5 = icmp eq i64 %2, %4
    %6 = const i64 0
    %7 = select i64 %5, %6, %3
    %8 = const i64 -9223372036854775807
    %9 = icmp eq i64 %2, %8
    %10 = const i64 1
    %11 = select i64 %9, %10, %7
    %12 = const i64 -9223372036854775806
    %13 = icmp eq i64 %2, %12
    %14 = const i64 2
    %15 = select i64 %13, %14, %11
    %16 = const i64 -9223372036854775805
    %17 = icmp eq i64 %2, %16
    %18 = const i64 3
    %19 = select i64 %17, %18, %15
    %20 = const i64 -9223372036854775804
    %21 = icmp eq i64 %2, %20
    %22 = const i64 4
    %23 = select i64 %21, %22, %19
    %24 = const i64 -9223372036854775803
    %25 = icmp eq i64 %2, %24
    %26 = const i64 5
    %27 = select i64 %25, %26, %23
    %28 = const i64 -9223372036854775802
    %29 = icmp eq i64 %2, %28
    %30 = const i64 6
    %31 = select i64 %29, %30, %27
    %32 = const i64 -9223372036854775801
    %33 = icmp eq i64 %2, %32
    %34 = const i64 7
    %35 = select i64 %33, %34, %31
    %36 = const i64 -9223372036854775800
    %37 = icmp eq i64 %2, %36
    %38 = const i64 8
    %39 = select i64 %37, %38, %35
    %40 = const i64 -9223372036854775799
    %41 = icmp eq i64 %2, %40
    %42 = const i64 9
    %43 = select i64 %41, %42, %39
    %44 = const i64 -9223372036854775798
    %45 = icmp eq i64 %2, %44
    %46 = const i64 10
    %47 = select i64 %45, %46, %43
    %48 = const i64 -9223372036854775797
    %49 = icmp eq i64 %2, %48
    %50 = const i64 11
    %51 = select i64 %49, %50, %47
    %52 = const i64 -9223372036854775796
    %53 = icmp eq i64 %2, %52
    %54 = const i64 12
    %55 = select i64 %53, %54, %51
    %56 = const i64 -9223372036854775795
    %57 = icmp eq i64 %2, %56
    %58 = const i64 13
    %59 = select i64 %57, %58, %55
    %60 = const i64 -9223372036854775794
    %61 = icmp eq i64 %2, %60
    %62 = const i64 14
    %63 = select i64 %61, %62, %59
    %64 = const i64 -9223372036854775793
    %65 = icmp eq i64 %2, %64
    %66 = const i64 15
    %67 = select i64 %65, %66, %63
    %68 = const i64 -9223372036854775792
    %69 = icmp eq i64 %2, %68
    %70 = const i64 16
    %71 = select i64 %69, %70, %67
    %72 = const i64 -9223372036854775791
    %73 = icmp eq i64 %2, %72
    %74 = const i64 17
    %75 = select i64 %73, %74, %71
    %76 = const i64 -9223372036854775790
    %77 = icmp eq i64 %2, %76
    %78 = const i64 18
    %79 = select i64 %77, %78, %75
    %80 = const i64 -9223372036854775789
    %81 = icmp eq i64 %2, %80
    %82 = const i64 19
    %83 = select i64 %81, %82, %79
    %84 = const i64 -9223372036854775788
    %85 = icmp eq i64 %2, %84
    %86 = const i64 20
    %87 = select i64 %85, %86, %83
    %88 = const i64 -9223372036854775786
    %89 = icmp eq i64 %2, %88
    %90 = const i64 22
    %91 = select i64 %89, %90, %87
    %92 = const i64 -9223372036854775785
    %93 = icmp eq i64 %2, %92
    %94 = const i64 23
    %95 = select i64 %93, %94, %91
    %96 = const i64 -9223372036854775784
    %97 = icmp eq i64 %2, %96
    %98 = const i64 24
    %99 = select i64 %97, %98, %95
    %100 = const i64 -9223372036854775783
    %101 = icmp eq i64 %2, %100
    %102 = const i64 25
    %103 = select i64 %101, %102, %99
    %104 = const i64 -9223372036854775782
    %105 = icmp eq i64 %2, %104
    %106 = const i64 26
    %107 = select i64 %105, %106, %103
    %108 = const i64 -9223372036854775781
    %109 = icmp eq i64 %2, %108
    %110 = const i64 27
    %111 = select i64 %109, %110, %107
    %112 = const i64 -9223372036854775780
    %113 = icmp eq i64 %2, %112
    %114 = const i64 28
    %115 = select i64 %113, %114, %111
    %116 = const i64 -9223372036854775779
    %117 = icmp eq i64 %2, %116
    %118 = const i64 29
    %119 = select i64 %117, %118, %115
    %120 = const i64 -9223372036854775778
    %121 = icmp eq i64 %2, %120
    %122 = const i64 30
    %123 = select i64 %121, %122, %119
    %124 = const i64 -9223372036854775777
    %125 = icmp eq i64 %2, %124
    %126 = const i64 31
    %127 = select i64 %125, %126, %123
    %128 = const i64 -9223372036854775776
    %129 = icmp eq i64 %2, %128
    %130 = const i64 32
    %131 = select i64 %129, %130, %127
    switch %131 [ 10: bb2 11: bb2 12: bb2 default: bb1 ]
bb1:
    %132 = const bool false
    br bb3(%132)
bb2:
    %133 = const bool true
    br bb3(%133)
bb3(%1: bool):
    ret %1
}

fn @Ty__is_signed(functy.10) {
bb0(%0: ptr):
    %2 = load i64, ptr %0
    %3 = const i64 21
    %4 = const i64 -9223372036854775808
    %5 = icmp eq i64 %2, %4
    %6 = const i64 0
    %7 = select i64 %5, %6, %3
    %8 = const i64 -9223372036854775807
    %9 = icmp eq i64 %2, %8
    %10 = const i64 1
    %11 = select i64 %9, %10, %7
    %12 = const i64 -9223372036854775806
    %13 = icmp eq i64 %2, %12
    %14 = const i64 2
    %15 = select i64 %13, %14, %11
    %16 = const i64 -9223372036854775805
    %17 = icmp eq i64 %2, %16
    %18 = const i64 3
    %19 = select i64 %17, %18, %15
    %20 = const i64 -9223372036854775804
    %21 = icmp eq i64 %2, %20
    %22 = const i64 4
    %23 = select i64 %21, %22, %19
    %24 = const i64 -9223372036854775803
    %25 = icmp eq i64 %2, %24
    %26 = const i64 5
    %27 = select i64 %25, %26, %23
    %28 = const i64 -9223372036854775802
    %29 = icmp eq i64 %2, %28
    %30 = const i64 6
    %31 = select i64 %29, %30, %27
    %32 = const i64 -9223372036854775801
    %33 = icmp eq i64 %2, %32
    %34 = const i64 7
    %35 = select i64 %33, %34, %31
    %36 = const i64 -9223372036854775800
    %37 = icmp eq i64 %2, %36
    %38 = const i64 8
    %39 = select i64 %37, %38, %35
    %40 = const i64 -9223372036854775799
    %41 = icmp eq i64 %2, %40
    %42 = const i64 9
    %43 = select i64 %41, %42, %39
    %44 = const i64 -9223372036854775798
    %45 = icmp eq i64 %2, %44
    %46 = const i64 10
    %47 = select i64 %45, %46, %43
    %48 = const i64 -9223372036854775797
    %49 = icmp eq i64 %2, %48
    %50 = const i64 11
    %51 = select i64 %49, %50, %47
    %52 = const i64 -9223372036854775796
    %53 = icmp eq i64 %2, %52
    %54 = const i64 12
    %55 = select i64 %53, %54, %51
    %56 = const i64 -9223372036854775795
    %57 = icmp eq i64 %2, %56
    %58 = const i64 13
    %59 = select i64 %57, %58, %55
    %60 = const i64 -9223372036854775794
    %61 = icmp eq i64 %2, %60
    %62 = const i64 14
    %63 = select i64 %61, %62, %59
    %64 = const i64 -9223372036854775793
    %65 = icmp eq i64 %2, %64
    %66 = const i64 15
    %67 = select i64 %65, %66, %63
    %68 = const i64 -9223372036854775792
    %69 = icmp eq i64 %2, %68
    %70 = const i64 16
    %71 = select i64 %69, %70, %67
    %72 = const i64 -9223372036854775791
    %73 = icmp eq i64 %2, %72
    %74 = const i64 17
    %75 = select i64 %73, %74, %71
    %76 = const i64 -9223372036854775790
    %77 = icmp eq i64 %2, %76
    %78 = const i64 18
    %79 = select i64 %77, %78, %75
    %80 = const i64 -9223372036854775789
    %81 = icmp eq i64 %2, %80
    %82 = const i64 19
    %83 = select i64 %81, %82, %79
    %84 = const i64 -9223372036854775788
    %85 = icmp eq i64 %2, %84
    %86 = const i64 20
    %87 = select i64 %85, %86, %83
    %88 = const i64 -9223372036854775786
    %89 = icmp eq i64 %2, %88
    %90 = const i64 22
    %91 = select i64 %89, %90, %87
    %92 = const i64 -9223372036854775785
    %93 = icmp eq i64 %2, %92
    %94 = const i64 23
    %95 = select i64 %93, %94, %91
    %96 = const i64 -9223372036854775784
    %97 = icmp eq i64 %2, %96
    %98 = const i64 24
    %99 = select i64 %97, %98, %95
    %100 = const i64 -9223372036854775783
    %101 = icmp eq i64 %2, %100
    %102 = const i64 25
    %103 = select i64 %101, %102, %99
    %104 = const i64 -9223372036854775782
    %105 = icmp eq i64 %2, %104
    %106 = const i64 26
    %107 = select i64 %105, %106, %103
    %108 = const i64 -9223372036854775781
    %109 = icmp eq i64 %2, %108
    %110 = const i64 27
    %111 = select i64 %109, %110, %107
    %112 = const i64 -9223372036854775780
    %113 = icmp eq i64 %2, %112
    %114 = const i64 28
    %115 = select i64 %113, %114, %111
    %116 = const i64 -9223372036854775779
    %117 = icmp eq i64 %2, %116
    %118 = const i64 29
    %119 = select i64 %117, %118, %115
    %120 = const i64 -9223372036854775778
    %121 = icmp eq i64 %2, %120
    %122 = const i64 30
    %123 = select i64 %121, %122, %119
    %124 = const i64 -9223372036854775777
    %125 = icmp eq i64 %2, %124
    %126 = const i64 31
    %127 = select i64 %125, %126, %123
    %128 = const i64 -9223372036854775776
    %129 = icmp eq i64 %2, %128
    %130 = const i64 32
    %131 = select i64 %129, %130, %127
    switch %131 [ 0: bb2 1: bb2 2: bb2 3: bb2 4: bb2 default: bb1 ]
bb1:
    %132 = const bool false
    br bb3(%132)
bb2:
    %133 = const bool true
    br bb3(%133)
bb3(%1: bool):
    ret %1
}

fn @Ty__is_unsigned(functy.11) {
bb0(%0: ptr):
    %2 = load i64, ptr %0
    %3 = const i64 21
    %4 = const i64 -9223372036854775808
    %5 = icmp eq i64 %2, %4
    %6 = const i64 0
    %7 = select i64 %5, %6, %3
    %8 = const i64 -9223372036854775807
    %9 = icmp eq i64 %2, %8
    %10 = const i64 1
    %11 = select i64 %9, %10, %7
    %12 = const i64 -9223372036854775806
    %13 = icmp eq i64 %2, %12
    %14 = const i64 2
    %15 = select i64 %13, %14, %11
    %16 = const i64 -9223372036854775805
    %17 = icmp eq i64 %2, %16
    %18 = const i64 3
    %19 = select i64 %17, %18, %15
    %20 = const i64 -9223372036854775804
    %21 = icmp eq i64 %2, %20
    %22 = const i64 4
    %23 = select i64 %21, %22, %19
    %24 = const i64 -9223372036854775803
    %25 = icmp eq i64 %2, %24
    %26 = const i64 5
    %27 = select i64 %25, %26, %23
    %28 = const i64 -9223372036854775802
    %29 = icmp eq i64 %2, %28
    %30 = const i64 6
    %31 = select i64 %29, %30, %27
    %32 = const i64 -9223372036854775801
    %33 = icmp eq i64 %2, %32
    %34 = const i64 7
    %35 = select i64 %33, %34, %31
    %36 = const i64 -9223372036854775800
    %37 = icmp eq i64 %2, %36
    %38 = const i64 8
    %39 = select i64 %37, %38, %35
    %40 = const i64 -9223372036854775799
    %41 = icmp eq i64 %2, %40
    %42 = const i64 9
    %43 = select i64 %41, %42, %39
    %44 = const i64 -9223372036854775798
    %45 = icmp eq i64 %2, %44
    %46 = const i64 10
    %47 = select i64 %45, %46, %43
    %48 = const i64 -9223372036854775797
    %49 = icmp eq i64 %2, %48
    %50 = const i64 11
    %51 = select i64 %49, %50, %47
    %52 = const i64 -9223372036854775796
    %53 = icmp eq i64 %2, %52
    %54 = const i64 12
    %55 = select i64 %53, %54, %51
    %56 = const i64 -9223372036854775795
    %57 = icmp eq i64 %2, %56
    %58 = const i64 13
    %59 = select i64 %57, %58, %55
    %60 = const i64 -9223372036854775794
    %61 = icmp eq i64 %2, %60
    %62 = const i64 14
    %63 = select i64 %61, %62, %59
    %64 = const i64 -9223372036854775793
    %65 = icmp eq i64 %2, %64
    %66 = const i64 15
    %67 = select i64 %65, %66, %63
    %68 = const i64 -9223372036854775792
    %69 = icmp eq i64 %2, %68
    %70 = const i64 16
    %71 = select i64 %69, %70, %67
    %72 = const i64 -9223372036854775791
    %73 = icmp eq i64 %2, %72
    %74 = const i64 17
    %75 = select i64 %73, %74, %71
    %76 = const i64 -9223372036854775790
    %77 = icmp eq i64 %2, %76
    %78 = const i64 18
    %79 = select i64 %77, %78, %75
    %80 = const i64 -9223372036854775789
    %81 = icmp eq i64 %2, %80
    %82 = const i64 19
    %83 = select i64 %81, %82, %79
    %84 = const i64 -9223372036854775788
    %85 = icmp eq i64 %2, %84
    %86 = const i64 20
    %87 = select i64 %85, %86, %83
    %88 = const i64 -9223372036854775786
    %89 = icmp eq i64 %2, %88
    %90 = const i64 22
    %91 = select i64 %89, %90, %87
    %92 = const i64 -9223372036854775785
    %93 = icmp eq i64 %2, %92
    %94 = const i64 23
    %95 = select i64 %93, %94, %91
    %96 = const i64 -9223372036854775784
    %97 = icmp eq i64 %2, %96
    %98 = const i64 24
    %99 = select i64 %97, %98, %95
    %100 = const i64 -9223372036854775783
    %101 = icmp eq i64 %2, %100
    %102 = const i64 25
    %103 = select i64 %101, %102, %99
    %104 = const i64 -9223372036854775782
    %105 = icmp eq i64 %2, %104
    %106 = const i64 26
    %107 = select i64 %105, %106, %103
    %108 = const i64 -9223372036854775781
    %109 = icmp eq i64 %2, %108
    %110 = const i64 27
    %111 = select i64 %109, %110, %107
    %112 = const i64 -9223372036854775780
    %113 = icmp eq i64 %2, %112
    %114 = const i64 28
    %115 = select i64 %113, %114, %111
    %116 = const i64 -9223372036854775779
    %117 = icmp eq i64 %2, %116
    %118 = const i64 29
    %119 = select i64 %117, %118, %115
    %120 = const i64 -9223372036854775778
    %121 = icmp eq i64 %2, %120
    %122 = const i64 30
    %123 = select i64 %121, %122, %119
    %124 = const i64 -9223372036854775777
    %125 = icmp eq i64 %2, %124
    %126 = const i64 31
    %127 = select i64 %125, %126, %123
    %128 = const i64 -9223372036854775776
    %129 = icmp eq i64 %2, %128
    %130 = const i64 32
    %131 = select i64 %129, %130, %127
    switch %131 [ 5: bb2 6: bb2 7: bb2 8: bb2 9: bb2 default: bb1 ]
bb1:
    %132 = const bool false
    br bb3(%132)
bb2:
    %133 = const bool true
    br bb3(%133)
bb3(%1: bool):
    ret %1
}

fn @Constant__value_matches_ty___closure_0_(functy.12) {
bb0(%0: ptr, %1: ptr):
    %5 = alloca i64, align 8
    %6 = alloca i64, align 8
    %7 = load ptr, ptr %0
    %8 = load ptr, ptr %7
    %9 = load i64, ptr %8
    store i64 %9, ptr %5
    %10 = load ptr, ptr %5
    store ptr %10, ptr %6
    %11 = load ptr, ptr %6
    %12 = ptrtoint ptr %11 to u64
    %13 = const u64 8
    %14 = const u64 1
    %15 = sub u64 %13, %14
    %16 = and u64 %12, %15
    %17 = const u64 0
    %18 = icmp eq u64 %16, %17
    condbr %18, bb2(%1), bb4
bb1(%2: bool):
    ret %2
bb2(%3: ptr):
    %19 = load ptr, ptr %6
    %20 = ptrtoint ptr %19 to u64
    %21 = const u64 0
    %22 = icmp eq u64 %20, %21
    %23 = const bool true
    %24 = const bool false
    %25 = select bool %22, %23, %24
    %26 = const bool false
    %27 = icmp eq bool %25, %26
    condbr %27, bb3(%3), bb4
bb3(%4: ptr):
    %28 = load ptr, ptr %6
    %29 = call @func.3(%4, %28)
    br bb1(%29)
bb4:
    unreachable
}
"#;

// ===========================================================================
// shape_matches_ty / value_matches_ty (the 13-arm deep-select-chain family).
// Both aarch64 host and x86_64 target are LP64 with identical data layout, so
// values built on the host are byte-identical to what the x86 code expects. We
// bake the bytes into the C driver and pass pointers; the 4 container externs
// (Vec::len/deref, slice::iter, unchecked_sub precondition) are never reached by
// these SCALAR cases, so they get abort stubs.
// ===========================================================================

#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct VmStructId(u32);
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct VmTyId(u32);
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct VmFuncTyId(u32);
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct VmEnumId(u32);
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct VmRecordId(u32);
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct VmClosureTyId(u32);
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
struct VmFuncId(u32);
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq, Default)]
enum VmSetRepr {
    Bitset,
    #[default]
    Boxed,
}
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)]
enum VmFatPtrKind {
    Slice(VmTyId),
    Str,
    TraitObject { trait_id: u32 },
}

#[allow(dead_code)]
#[derive(Clone, PartialEq, Eq)]
enum VmTy {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    U128,
    F16,
    F32,
    F64,
    Bool,
    Vector(Box<VmTy>, u32),
    Ptr,
    FatPtr(VmFatPtrKind),
    Unit,
    Never,
    Struct(VmStructId),
    Array(VmTyId, u64),
    Tuple(Vec<VmTy>),
    Enum(VmEnumId),
    Func(VmFuncTyId),
    Ref(Box<VmTy>),
    RefMut(Box<VmTy>),
    PtrConst(Box<VmTy>),
    PtrMut(Box<VmTy>),
    Rc(Box<VmTy>),
    Set(VmTyId, VmSetRepr),
    Sequence(VmTyId),
    Record(VmRecordId),
    Closure(VmClosureTyId),
}
impl VmTy {
    fn is_integer(&self) -> bool {
        self.is_signed() || self.is_unsigned()
    }
    fn is_signed(&self) -> bool {
        matches!(
            self,
            VmTy::I8 | VmTy::I16 | VmTy::I32 | VmTy::I64 | VmTy::I128
        )
    }
    fn is_unsigned(&self) -> bool {
        matches!(
            self,
            VmTy::U8 | VmTy::U16 | VmTy::U32 | VmTy::U64 | VmTy::U128
        )
    }
    fn is_float(&self) -> bool {
        matches!(self, VmTy::F16 | VmTy::F32 | VmTy::F64)
    }
}
#[allow(dead_code)]
#[derive(Clone)]
enum VmConstant {
    Int(i128),
    Float(f64),
    Bool(bool),
    Aggregate(Vec<VmConstant>),
    Array(Vec<VmConstant>),
    Vector(Vec<VmConstant>),
    Sequence(Vec<VmConstant>),
    Set(Vec<VmConstant>),
    Record(Vec<(String, VmConstant)>),
    Closure {
        func: VmFuncId,
        captures: Vec<VmConstant>,
    },
    FnDef(VmFuncId),
    SymbolAddr {
        symbol: String,
        addend: i64,
    },
    PhantomData,
}
impl VmConstant {
    fn shape_matches_ty(&self, ty: &VmTy) -> bool {
        match (self, ty) {
            (VmConstant::Int(_), t) if t.is_integer() => true,
            (VmConstant::Int(_), VmTy::Ptr) => true,
            (VmConstant::Float(_), t) if t.is_float() => true,
            (VmConstant::Bool(_), VmTy::Bool) => true,
            (VmConstant::Aggregate(_), VmTy::Tuple(_))
            | (VmConstant::Aggregate(_), VmTy::Array(_, _))
            | (VmConstant::Aggregate(_), VmTy::Struct(_))
            | (VmConstant::Aggregate(_), VmTy::Record(_)) => true,
            (VmConstant::Array(_), VmTy::Array(_, _)) => true,
            (VmConstant::Vector(_), VmTy::Vector(_, _)) => true,
            (VmConstant::Sequence(_), VmTy::Sequence(_)) => true,
            (VmConstant::Set(_), VmTy::Set(_, _)) => true,
            (VmConstant::Record(_), VmTy::Record(_)) => true,
            (VmConstant::Closure { .. }, VmTy::Closure(_)) => true,
            (VmConstant::FnDef(_), VmTy::Func(_)) => true,
            (VmConstant::SymbolAddr { .. }, VmTy::Ptr) => true,
            (VmConstant::SymbolAddr { .. }, VmTy::Func(_)) => true,
            (VmConstant::PhantomData, VmTy::Unit) => true,
            _ => false,
        }
    }
}

fn bytes_of<T>(v: &T) -> Vec<u8> {
    unsafe {
        std::slice::from_raw_parts(v as *const T as *const u8, std::mem::size_of::<T>()).to_vec()
    }
}
fn c_array(name: &str, bytes: &[u8]) -> String {
    let elems: Vec<String> = bytes.iter().map(|b| format!("0x{b:02x}")).collect();
    format!("static unsigned char {name}[] = {{{}}};", elems.join(","))
}

fn shape_driver_c(cases: &[(Vec<u8>, Vec<u8>, bool, String)]) -> String {
    let mut decls = String::new();
    let mut calls = String::new();
    for (i, (cb, tb, _exp, _label)) in cases.iter().enumerate() {
        decls.push_str(&c_array(&format!("c{i}"), cb));
        decls.push('\n');
        decls.push_str(&c_array(&format!("t{i}"), tb));
        decls.push('\n');
        calls.push_str(&format!(
            "    printf(\"%d %d %d\\n\", {i}, (int)shape_matches((const void*)c{i}, (const void*)t{i}), (int)value_matches((const void*)c{i}, (const void*)t{i}));\n"
        ));
    }
    format!(
        r####"
#include <stdio.h>
#include <stdlib.h>
typedef int bool_t;
extern bool_t shape_matches(const void* c, const void* ty) __asm__("_Constant__shape_matches_ty");
extern bool_t value_matches(const void* c, const void* ty) __asm__("_Constant__value_matches_ty");
// unused container externs (never reached by scalar cases) -> abort stubs.
void stub_iter(void) __asm__("__RNvMNtCs2EYQwhfuABO_4core5sliceSNtCs8vhpJKEIjU0_25trust_value_matches_slice8Constant4iterBw_");
void stub_iter(void) {{ abort(); }}
void stub_len(void) __asm__("__RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCs8vhpJKEIjU0_25trust_value_matches_slice8ConstantE3lenBG_");
void stub_len(void) {{ abort(); }}
void stub_precond(void) __asm__("__RNvNvMs9_NtCs2EYQwhfuABO_4core3numj13unchecked_sub18precondition_checkCs8vhpJKEIjU0_25trust_value_matches_slice");
void stub_precond(void) {{ abort(); }}
void stub_deref(void) __asm__("__RNvXs7_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCs8vhpJKEIjU0_25trust_value_matches_slice8ConstantENtNtNtCs2EYQwhfuABO_4core3ops5deref5Deref5derefBH_");
void stub_deref(void) {{ abort(); }}
{decls}
int main(void) {{
{calls}
    return 0;
}}
"####
    )
}

#[test]
fn x86_64_shape_matches_ty_faithful() {
    if !common::rosetta::has_cc_x86_64_link_run() {
        eprintln!("skip: cc -arch x86_64 link/run unavailable");
        return;
    }
    // (constant, ty, label). The first two are the aarch64-JIT MISCOMPILE cases.
    let raw_cases: Vec<(VmConstant, VmTy, &str)> = vec![
        (
            VmConstant::Int(5),
            VmTy::Ptr,
            "Int vs Ptr [aarch64 MISCOMPILE -> false]",
        ),
        (
            VmConstant::Float(1.0),
            VmTy::F64,
            "Float vs F64 [aarch64 MISCOMPILE -> false]",
        ),
        (VmConstant::Int(5), VmTy::I32, "Int vs I32 -> true"),
        (VmConstant::Int(5), VmTy::U64, "Int vs U64 -> true"),
        (VmConstant::Int(5), VmTy::Bool, "Int vs Bool -> false"),
        (VmConstant::Bool(true), VmTy::Bool, "Bool vs Bool -> true"),
        (VmConstant::Float(2.5), VmTy::I32, "Float vs I32 -> false"),
        (VmConstant::Int(5), VmTy::Unit, "Int vs Unit -> false"),
        (
            VmConstant::PhantomData,
            VmTy::Unit,
            "PhantomData vs Unit -> true",
        ),
    ];
    let cases: Vec<(Vec<u8>, Vec<u8>, bool, String)> = raw_cases
        .iter()
        .map(|(c, t, l)| {
            (
                bytes_of(c),
                bytes_of(t),
                c.shape_matches_ty(t),
                l.to_string(),
            )
        })
        .collect();

    let module =
        trust_ir::parser::parse_module(MIR_VALUE_MATCHES_TRUST_IR).expect("parse value_matches");
    let mut any_miscompile = false;
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let obj = match compile_x86_64_at(&module, opt) {
            Ok(b) => b,
            Err(e) => {
                eprintln!("[shape_matches {opt:?}] not compiled: {e}");
                continue;
            }
        };
        let dir = std::env::temp_dir().join(format!("trust_cg_scale_shape_{opt:?}"));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let obj_path = dir.join("vm.o");
        std::fs::write(&obj_path, &obj).unwrap();
        let drv_path = dir.join("driver.c");
        std::fs::write(&drv_path, shape_driver_c(&cases)).unwrap();
        let bin = dir.join("test_shape");
        let link = Command::new("cc")
            .args(if cfg!(target_os = "macos") {
                &["-arch", "x86_64"][..]
            } else {
                &[][..]
            })
            .args([
                "-O0",
                "-o",
                bin.to_str().unwrap(),
                drv_path.to_str().unwrap(),
                obj_path.to_str().unwrap(),
            ])
            .output()
            .unwrap();
        if !link.status.success() {
            eprintln!(
                "[shape_matches {opt:?}] LINK FAIL: {}\n{}",
                String::from_utf8_lossy(&link.stderr),
                nm_dump(&obj_path)
            );
            continue;
        }
        let run = Command::new(&bin).output().unwrap();
        if !run.status.success() {
            eprintln!(
                "[shape_matches {opt:?}] RUN FAIL code={:?}: {}",
                run.status.code(),
                String::from_utf8_lossy(&run.stderr)
            );
            continue;
        }
        let stdout = String::from_utf8_lossy(&run.stdout).to_string();
        for line in stdout.lines() {
            let p: Vec<&str> = line.split_whitespace().collect();
            if p.len() != 3 {
                continue;
            }
            let idx: usize = p[0].parse().unwrap();
            let shape_r: i32 = p[1].parse().unwrap();
            let value_r: i32 = p[2].parse().unwrap();
            let want = cases[idx].2;
            if (shape_r != 0) != want {
                any_miscompile = true;
                eprintln!(
                    "*** x86_64 MISCOMPILE shape_matches_ty case {idx} ({}) at {opt:?}: got {} want {}",
                    cases[idx].3,
                    shape_r != 0,
                    want
                );
            }
            if (value_r != 0) != want {
                any_miscompile = true;
                eprintln!(
                    "*** x86_64 MISCOMPILE value_matches_ty case {idx} ({}) at {opt:?}: got {} want {}",
                    cases[idx].3,
                    value_r != 0,
                    want
                );
            }
        }
        eprintln!(
            "[shape_matches {opt:?}] {} cases checked (both entries)",
            cases.len()
        );
    }
    assert!(
        !any_miscompile,
        "x86_64 shape_matches_ty/value_matches_ty miscompile detected — LIVE x86 BUG"
    );
}

const MIR_EDGE_BOUNDS_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::edge_bounds_entry"

functy.0 = (u32, u32, i64, u64, u32) -> (u64)

functy.1 = (ptr, u32) -> ()

functy.2 = (ptr, u8, ptr, bool) -> ()

functy.3 = (u128, u128) -> (u128)

functy.4 = (ptr, u8, ptr) -> ()

fn @edge_bounds_entry(functy.0) {
bb0(%0: u32, %1: u32, %2: i64, %3: u64, %4: u32):
    %21 = alloca (i128, i128), align 16
    %22 = alloca i8, align 1
    %23 = alloca (i128, i128), align 16
    %24 = alloca (i128, i128), align 16
    %25 = const u32 0
    %26 = icmp ne u32 %1, %25
    condbr %26, bb1(%0, %2, %3, %4), bb3(%0, %4)
bb1(%5: u32, %6: i64, %7: u64, %8: u32):
    %27 = sext i64 %6 to i128
    %28 = const i32 64
    %29 = bitcast i32 %28 to u32
    %30 = const u32 128
    %31 = icmp ult u32 %29, %30
    condbr %31, bb2(%5, %7, %8, %27), bb19
bb2(%9: u32, %10: u64, %11: u32, %12: i128):
    %32 = const i32 64
    %33 = zext i32 %32 to i128
    %34 = shl i128 %12, %33
    %35 = zext u64 %10 to i128
    %36 = or i128 %34, %35
    %37 = const i64 16
    %38 = gep i8, ptr %21, %37
    store i128 %36, ptr %38
    %39 = const i128 1
    store i128 %39, ptr %21
    br bb4(%9, %11)
bb3(%13: u32, %14: u32):
    %40 = const i128 0
    store i128 %40, ptr %21
    br bb4(%13, %14)
bb4(%15: u32, %16: u32):
    call @func.1(%22, %15)
    br bb5(%16)
bb5(%17: u32):
    %41 = const u32 3
    %42 = icmp ult u32 %17, %41
    %43 = load i128, ptr %21
    store i128 %43, ptr %24
    %44 = const i64 16
    %45 = gep i8, ptr %21, %44
    %46 = const i64 16
    %47 = gep i8, ptr %24, %46
    %48 = load i128, ptr %45
    store i128 %48, ptr %47
    %49 = load u8, ptr %22
    call @func.2(%23, %49, %24, %42)
    br bb6(%17)
bb6(%18: u32):
    switch %18 [ 0: bb9 3: bb9 1: bb8 4: bb8 default: bb7 ]
bb7:
    %50 = load i128, ptr %23
    %51 = trunc i128 %50 to i64
    switch %51 [ 0: bb15 1: bb16 default: bb10 ]
bb8:
    %52 = load i128, ptr %23
    %53 = trunc i128 %52 to i64
    switch %53 [ 0: bb13 1: bb14 default: bb10 ]
bb9:
    %54 = load i128, ptr %23
    %55 = trunc i128 %54 to i64
    switch %55 [ 0: bb11 1: bb12 default: bb10 ]
bb10:
    unreachable
bb11:
    %56 = const u64 0
    br bb18(%56)
bb12:
    %57 = const u64 1
    br bb18(%57)
bb13:
    %58 = const u64 0
    br bb18(%58)
bb14:
    %59 = const i64 16
    %60 = gep i8, ptr %23, %59
    %61 = load u128, ptr %60
    %62 = trunc u128 %61 to u64
    br bb18(%62)
bb15:
    %63 = const u64 0
    br bb18(%63)
bb16:
    %64 = const i64 16
    %65 = gep i8, ptr %23, %64
    %66 = load u128, ptr %65
    %67 = const i32 64
    %68 = bitcast i32 %67 to u32
    %69 = const u32 128
    %70 = icmp ult u32 %68, %69
    condbr %70, bb17(%66), bb19
bb17(%19: u128):
    %71 = const i32 64
    %72 = zext i32 %71 to u128
    %73 = lshr u128 %19, %72
    %74 = trunc u128 %73 to u64
    br bb18(%74)
bb18(%20: u64):
    ret %20
bb19:
    unreachable
}

fn @op_for_tag(functy.1) {
bb0(%0: ptr, %1: u32):
    switch %1 [ 0: bb10 1: bb9 2: bb8 3: bb7 4: bb6 5: bb5 6: bb4 7: bb3 8: bb2 default: bb1 ]
bb1:
    %2 = const i8 9
    store i8 %2, ptr %0
    br bb11
bb2:
    %3 = const i8 8
    store i8 %3, ptr %0
    br bb11
bb3:
    %4 = const i8 7
    store i8 %4, ptr %0
    br bb11
bb4:
    %5 = const i8 6
    store i8 %5, ptr %0
    br bb11
bb5:
    %6 = const i8 5
    store i8 %6, ptr %0
    br bb11
bb6:
    %7 = const i8 4
    store i8 %7, ptr %0
    br bb11
bb7:
    %8 = const i8 3
    store i8 %8, ptr %0
    br bb11
bb8:
    %9 = const i8 2
    store i8 %9, ptr %0
    br bb11
bb9:
    %10 = const i8 1
    store i8 %10, ptr %0
    br bb11
bb10:
    %11 = const i8 0
    store i8 %11, ptr %0
    br bb11
bb11:
    ret
}

fn @edge_bound_pick(functy.2) {
bb0(%0: ptr, %1: u8, %2: ptr, %3: bool):
    %5 = alloca i8, align 1
    %6 = alloca (i128, i128, i128, i128), align 16
    store u8 %1, ptr %5
    %7 = load u8, ptr %5
    call @func.4(%6, %7, %2)
    br bb1(%3)
bb1(%4: bool):
    condbr %4, bb2, bb3
bb2:
    %8 = load i128, ptr %6
    store i128 %8, ptr %0
    %9 = const i64 16
    %10 = gep i8, ptr %6, %9
    %11 = const i64 16
    %12 = gep i8, ptr %0, %11
    %13 = load i128, ptr %10
    store i128 %13, ptr %12
    br bb4
bb3:
    %14 = const i64 32
    %15 = gep i8, ptr %6, %14
    %16 = load i128, ptr %15
    store i128 %16, ptr %0
    %17 = const i64 16
    %18 = gep i8, ptr %15, %17
    %19 = const i64 16
    %20 = gep i8, ptr %0, %19
    %21 = load i128, ptr %18
    store i128 %21, ptr %20
    br bb4
bb4:
    ret
}

fn @_RNvMs8_NtCs2EYQwhfuABO_4core3numo14saturating_sub(functy.3) {
}

fn @edge_bounds(functy.4) {
bb0(%0: ptr, %1: u8, %2: ptr):
    %12 = alloca i8, align 1
    %13 = alloca (i128, i128), align 16
    %14 = alloca (i128, i128), align 16
    %15 = alloca (i128, i128), align 16
    %16 = alloca (i128, i128), align 16
    %17 = alloca (i128, i128), align 16
    %18 = alloca (i128, i128), align 16
    %19 = alloca (i128, i128), align 16
    %20 = alloca (i128, i128), align 16
    %21 = alloca (i128, i128), align 16
    %22 = alloca (i128, i128), align 16
    %23 = alloca (i128, i128), align 16
    %24 = alloca (i128, i128), align 16
    %25 = alloca (i128, i128), align 16
    %26 = alloca (i128, i128), align 16
    %27 = alloca (i128, i128), align 16
    %28 = alloca (i128, i128), align 16
    store u8 %1, ptr %12
    %29 = load i128, ptr %2
    %30 = trunc i128 %29 to i64
    switch %30 [ 1: bb2 0: bb1 default: bb6 ]
bb1:
    %31 = const i128 0
    store i128 %31, ptr %13
    %32 = const i128 0
    store i128 %32, ptr %14
    %33 = load i128, ptr %13
    store i128 %33, ptr %0
    %34 = const i64 16
    %35 = gep i8, ptr %13, %34
    %36 = const i64 16
    %37 = gep i8, ptr %0, %36
    %38 = load i128, ptr %35
    store i128 %38, ptr %37
    %39 = const i64 32
    %40 = gep i8, ptr %0, %39
    %41 = load i128, ptr %14
    store i128 %41, ptr %40
    %42 = const i64 16
    %43 = gep i8, ptr %14, %42
    %44 = const i64 16
    %45 = gep i8, ptr %40, %44
    %46 = load i128, ptr %43
    store i128 %46, ptr %45
    br bb13
bb2:
    %47 = const i64 16
    %48 = gep i8, ptr %2, %47
    %49 = load i128, ptr %48
    %50 = const i128 0
    %51 = icmp slt i128 %49, %50
    condbr %51, bb3, bb4(%49)
bb3:
    %52 = const i128 0
    store i128 %52, ptr %15
    %53 = const i128 0
    store i128 %53, ptr %16
    %54 = load i128, ptr %15
    store i128 %54, ptr %0
    %55 = const i64 16
    %56 = gep i8, ptr %15, %55
    %57 = const i64 16
    %58 = gep i8, ptr %0, %57
    %59 = load i128, ptr %56
    store i128 %59, ptr %58
    %60 = const i64 32
    %61 = gep i8, ptr %0, %60
    %62 = load i128, ptr %16
    store i128 %62, ptr %61
    %63 = const i64 16
    %64 = gep i8, ptr %16, %63
    %65 = const i64 16
    %66 = gep i8, ptr %61, %65
    %67 = load i128, ptr %64
    store i128 %67, ptr %66
    br bb13
bb4(%3: i128):
    %68 = bitcast i128 %3 to u128
    %69 = const u128 1
    %70 = call @func.3(%68, %69)
    br bb5(%68, %70)
bb5(%4: u128, %5: u128):
    %71 = load i8, ptr %12
    %72 = sext i8 %71 to i64
    switch %72 [ 0: bb8(%4) 1: bb7(%4) 2: bb12(%5) 3: bb11(%4) 4: bb10(%4) 5: bb9(%5) 6: bb12(%5) 7: bb11(%4) 8: bb10(%4) 9: bb9(%5) default: bb6 ]
bb6:
    unreachable
bb7(%6: u128):
    %73 = const i128 0
    store i128 %73, ptr %27
    %74 = const i64 16
    %75 = gep i8, ptr %28, %74
    store u128 %6, ptr %75
    %76 = const i128 1
    store i128 %76, ptr %28
    %77 = load i128, ptr %27
    store i128 %77, ptr %0
    %78 = const i64 16
    %79 = gep i8, ptr %27, %78
    %80 = const i64 16
    %81 = gep i8, ptr %0, %80
    %82 = load i128, ptr %79
    store i128 %82, ptr %81
    %83 = const i64 32
    %84 = gep i8, ptr %0, %83
    %85 = load i128, ptr %28
    store i128 %85, ptr %84
    %86 = const i64 16
    %87 = gep i8, ptr %28, %86
    %88 = const i64 16
    %89 = gep i8, ptr %84, %88
    %90 = load i128, ptr %87
    store i128 %90, ptr %89
    br bb13
bb8(%7: u128):
    %91 = const i64 16
    %92 = gep i8, ptr %25, %91
    store u128 %7, ptr %92
    %93 = const i128 1
    store i128 %93, ptr %25
    %94 = const i128 0
    store i128 %94, ptr %26
    %95 = load i128, ptr %25
    store i128 %95, ptr %0
    %96 = const i64 16
    %97 = gep i8, ptr %25, %96
    %98 = const i64 16
    %99 = gep i8, ptr %0, %98
    %100 = load i128, ptr %97
    store i128 %100, ptr %99
    %101 = const i64 32
    %102 = gep i8, ptr %0, %101
    %103 = load i128, ptr %26
    store i128 %103, ptr %102
    %104 = const i64 16
    %105 = gep i8, ptr %26, %104
    %106 = const i64 16
    %107 = gep i8, ptr %102, %106
    %108 = load i128, ptr %105
    store i128 %108, ptr %107
    br bb13
bb9(%8: u128):
    %109 = const i128 0
    store i128 %109, ptr %23
    %110 = const i64 16
    %111 = gep i8, ptr %24, %110
    store u128 %8, ptr %111
    %112 = const i128 1
    store i128 %112, ptr %24
    %113 = load i128, ptr %23
    store i128 %113, ptr %0
    %114 = const i64 16
    %115 = gep i8, ptr %23, %114
    %116 = const i64 16
    %117 = gep i8, ptr %0, %116
    %118 = load i128, ptr %115
    store i128 %118, ptr %117
    %119 = const i64 32
    %120 = gep i8, ptr %0, %119
    %121 = load i128, ptr %24
    store i128 %121, ptr %120
    %122 = const i64 16
    %123 = gep i8, ptr %24, %122
    %124 = const i64 16
    %125 = gep i8, ptr %120, %124
    %126 = load i128, ptr %123
    store i128 %126, ptr %125
    br bb13
bb10(%9: u128):
    %127 = const i128 0
    store i128 %127, ptr %21
    %128 = const i64 16
    %129 = gep i8, ptr %22, %128
    store u128 %9, ptr %129
    %130 = const i128 1
    store i128 %130, ptr %22
    %131 = load i128, ptr %21
    store i128 %131, ptr %0
    %132 = const i64 16
    %133 = gep i8, ptr %21, %132
    %134 = const i64 16
    %135 = gep i8, ptr %0, %134
    %136 = load i128, ptr %133
    store i128 %136, ptr %135
    %137 = const i64 32
    %138 = gep i8, ptr %0, %137
    %139 = load i128, ptr %22
    store i128 %139, ptr %138
    %140 = const i64 16
    %141 = gep i8, ptr %22, %140
    %142 = const i64 16
    %143 = gep i8, ptr %138, %142
    %144 = load i128, ptr %141
    store i128 %144, ptr %143
    br bb13
bb11(%10: u128):
    %145 = const i64 16
    %146 = gep i8, ptr %19, %145
    store u128 %10, ptr %146
    %147 = const i128 1
    store i128 %147, ptr %19
    %148 = const i128 0
    store i128 %148, ptr %20
    %149 = load i128, ptr %19
    store i128 %149, ptr %0
    %150 = const i64 16
    %151 = gep i8, ptr %19, %150
    %152 = const i64 16
    %153 = gep i8, ptr %0, %152
    %154 = load i128, ptr %151
    store i128 %154, ptr %153
    %155 = const i64 32
    %156 = gep i8, ptr %0, %155
    %157 = load i128, ptr %20
    store i128 %157, ptr %156
    %158 = const i64 16
    %159 = gep i8, ptr %20, %158
    %160 = const i64 16
    %161 = gep i8, ptr %156, %160
    %162 = load i128, ptr %159
    store i128 %162, ptr %161
    br bb13
bb12(%11: u128):
    %163 = const i64 16
    %164 = gep i8, ptr %17, %163
    store u128 %11, ptr %164
    %165 = const i128 1
    store i128 %165, ptr %17
    %166 = const i128 0
    store i128 %166, ptr %18
    %167 = load i128, ptr %17
    store i128 %167, ptr %0
    %168 = const i64 16
    %169 = gep i8, ptr %17, %168
    %170 = const i64 16
    %171 = gep i8, ptr %0, %170
    %172 = load i128, ptr %169
    store i128 %172, ptr %171
    %173 = const i64 32
    %174 = gep i8, ptr %0, %173
    %175 = load i128, ptr %18
    store i128 %175, ptr %174
    %176 = const i64 16
    %177 = gep i8, ptr %18, %176
    %178 = const i64 16
    %179 = gep i8, ptr %174, %178
    %180 = load i128, ptr %177
    store i128 %180, ptr %179
    br bb13
bb13:
    ret
}
"#;

// `@edge_bounds` ABI (read off IR functy.4 + body): (out: *mut (Option<u128>,
// Option<u128>) [64B], op: u8 [ICmpOp discr], k: *const Option<i128> [32B]).
// First Option<u128> at offset 0, second at offset 32; each {disc i128 @0, val @16}.
// ICmpOp discr: Eq=0,Ne=1,Ult=2,Ule=3,Ugt=4,Uge=5,Slt=6,Sle=7,Sgt=8,Sge=9.
// Sole extern: saturating_sub(u128,u128)->u128 (value-return).

/// Native oracle, VERBATIM alloc_bound.rs:427 `edge_bounds`. op is the ICmpOp discr.
fn edge_bounds_oracle(op: u8, k: Option<i128>) -> ((bool, u128), (bool, u128)) {
    let k = match k {
        Some(k) => k,
        None => return ((false, 0), (false, 0)),
    };
    if k < 0 {
        return ((false, 0), (false, 0));
    }
    let k = k as u128;
    let km1 = k.saturating_sub(1);
    match op {
        2 | 6 => ((true, km1), (false, 0)), // Ult | Slt
        3 | 7 => ((true, k), (false, 0)),   // Ule | Sle
        4 | 8 => ((false, 0), (true, k)),   // Ugt | Sgt
        5 | 9 => ((false, 0), (true, km1)), // Uge | Sge
        0 => ((true, k), (false, 0)),       // Eq
        1 => ((false, 0), (true, k)),       // Ne
        _ => unreachable!(),
    }
}

fn edge_bounds_driver_c() -> String {
    format!(
        r####"
#include <stdio.h>
typedef struct __attribute__((aligned(16))) {{ __int128 disc; unsigned __int128 val; }} OptU128;
typedef struct __attribute__((aligned(16))) {{ __int128 disc; __int128 val; }} OptI128;
typedef struct __attribute__((aligned(16))) {{ OptU128 a; OptU128 b; }} Pair;

unsigned __int128 sat_sub(unsigned __int128 a, unsigned __int128 b) __asm__("{sat}");
unsigned __int128 sat_sub(unsigned __int128 a, unsigned __int128 b) {{ return a < b ? (unsigned __int128)0 : a - b; }}

extern void edge_bounds(Pair* out, unsigned char op, const OptI128* k) __asm__("_edge_bounds");

// op, k_disc(0=None,1=Some), k_val
extern unsigned char G_OP[]; extern int G_KD[]; extern long long G_KV[]; extern int G_N;

int main(void) {{
    for (int i = 0; i < G_N; i++) {{
        OptI128 k; k.disc = G_KD[i]; k.val = (__int128)G_KV[i];
        Pair out; out.a.disc = 99; out.a.val = 0; out.b.disc = 99; out.b.val = 0;
        edge_bounds(&out, G_OP[i], &k);
        unsigned long long avlo=(unsigned long long)out.a.val, avhi=(unsigned long long)(out.a.val>>64);
        unsigned long long bvlo=(unsigned long long)out.b.val, bvhi=(unsigned long long)(out.b.val>>64);
        printf("%d %d %016llx%016llx %d %016llx%016llx\n", i, (int)out.a.disc, avhi,avlo, (int)out.b.disc, bvhi,bvlo);
    }}
    return 0;
}}
"####,
        sat = "__RNvMs8_NtCs2EYQwhfuABO_4core3numo14saturating_sub",
    )
}

#[test]
fn x86_64_edge_bounds_faithful() {
    if !common::rosetta::has_cc_x86_64_link_run() {
        eprintln!("skip: cc -arch x86_64 link/run unavailable");
        return;
    }
    // op 0..=9 crossed with a range of k (None, negative, 0, 1, small, u8-edge, wide).
    // k values are i64-representable so the C driver table can use `long long`.
    let ks: Vec<Option<i128>> = vec![
        None,
        Some(-1),
        Some(0),
        Some(1),
        Some(10),
        Some(255),
        Some(1_000_000_000_000i128),
    ];
    let mut cases: Vec<(u8, Option<i128>)> = Vec::new();
    for op in 0u8..=9 {
        for k in &ks {
            cases.push((op, *k));
        }
    }
    let g_op: Vec<String> = cases.iter().map(|(op, _)| op.to_string()).collect();
    let g_kd: Vec<String> = cases
        .iter()
        .map(|(_, k)| if k.is_some() { "1" } else { "0" }.to_string())
        .collect();
    let g_kv: Vec<String> = cases
        .iter()
        .map(|(_, k)| (k.unwrap_or(0) as i64).to_string())
        .collect();
    let table_c = format!(
        "unsigned char G_OP[] = {{{}}};\nint G_KD[] = {{{}}};\nlong long G_KV[] = {{{}}};\nint G_N = {};\n",
        g_op.join(","),
        g_kd.join(","),
        g_kv.join(","),
        cases.len()
    );

    let module =
        trust_ir::parser::parse_module(MIR_EDGE_BOUNDS_TRUST_IR).expect("edge_bounds parse");
    let mut any_miscompile = false;
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let obj = match compile_x86_64_at(&module, opt) {
            Ok(b) => b,
            Err(e) => {
                eprintln!("[edge_bounds {opt:?}] FAIL-CLOSED (sound): {e}");
                continue;
            }
        };
        let dir = std::env::temp_dir().join(format!("trust_cg_scale_edge_{opt:?}"));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let obj_path = dir.join("eb.o");
        std::fs::write(&obj_path, &obj).unwrap();
        let drv_path = dir.join("driver.c");
        std::fs::write(
            &drv_path,
            format!("{}\n{}", edge_bounds_driver_c(), table_c),
        )
        .unwrap();
        let bin = dir.join("test_eb");
        let link = Command::new("cc")
            .args(if cfg!(target_os = "macos") {
                &["-arch", "x86_64"][..]
            } else {
                &[][..]
            })
            .args([
                "-O0",
                "-o",
                bin.to_str().unwrap(),
                drv_path.to_str().unwrap(),
                obj_path.to_str().unwrap(),
            ])
            .output()
            .unwrap();
        if !link.status.success() {
            eprintln!(
                "[edge_bounds {opt:?}] LINK FAIL: {}\n{}",
                String::from_utf8_lossy(&link.stderr),
                nm_dump(&obj_path)
            );
            continue;
        }
        let run = Command::new(&bin).output().unwrap();
        if !run.status.success() {
            eprintln!(
                "[edge_bounds {opt:?}] RUN FAIL code={:?}: {}",
                run.status.code(),
                String::from_utf8_lossy(&run.stderr)
            );
            continue;
        }
        let stdout = String::from_utf8_lossy(&run.stdout).to_string();
        for line in stdout.lines() {
            let p: Vec<&str> = line.split_whitespace().collect();
            if p.len() != 5 {
                continue;
            }
            let idx: usize = p[0].parse().unwrap();
            let ad: i32 = p[1].parse().unwrap();
            let av = u128::from_str_radix(p[2], 16).unwrap();
            let bd: i32 = p[3].parse().unwrap();
            let bv = u128::from_str_radix(p[4], 16).unwrap();
            let (op, k) = cases[idx];
            let ((wad, wav), (wbd, wbv)) = edge_bounds_oracle(op, k);
            let a_ok = (ad != 0) == wad && (!wad || av == wav);
            let b_ok = (bd != 0) == wbd && (!wbd || bv == wbv);
            if !a_ok || !b_ok {
                any_miscompile = true;
                eprintln!(
                    "*** x86_64 MISCOMPILE edge_bounds op={op} k={k:?} at {opt:?}: got (({},{:#x}),({},{:#x})) want (({wad},{wav:#x}),({wbd},{wbv:#x}))",
                    ad != 0,
                    av,
                    bd != 0,
                    bv
                );
            }
        }
        eprintln!("[edge_bounds {opt:?}] {} cases checked", cases.len());
    }
    assert!(
        !any_miscompile,
        "x86_64 edge_bounds miscompile detected — LIVE x86 BUG (x86 lowers the 4xi128 sret that aarch64 cannot; verify it lowers CORRECTLY)"
    );
}

const MIR_CAST_SHAPE_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::cast_shape_entry"

functy.0 = (u32, u32) -> (u32)

functy.1 = (ptr, u32) -> ()

functy.2 = (ptr, u8) -> ()

functy.3 = (u8) -> (u32)

functy.4 = (u8) -> (bool)

fn @cast_shape_entry(functy.0) {
bb0(%0: u32, %1: u32):
    %6 = alloca i8, align 1
    %7 = alloca i8, align 1
    call @func.1(%6, %0)
    br bb1(%1)
bb1(%2: u32):
    %8 = const u32 0
    %9 = icmp eq u32 %2, %8
    condbr %9, bb2, bb4
bb2:
    %10 = load u8, ptr %6
    call @func.2(%7, %10)
    br bb3
bb3:
    %11 = load u8, ptr %7
    %12 = call @func.3(%11)
    br bb7(%12)
bb4:
    %13 = load u8, ptr %6
    %14 = call @func.4(%13)
    br bb5(%14)
bb5(%3: bool):
    %15 = const u32 1
    %16 = const u32 0
    %17 = select u32 %3, %15, %16
    br bb6(%17)
bb6(%4: u32):
    ret %4
bb7(%5: u32):
    br bb6(%5)
}

fn @cast_op_for_tag(functy.1) {
bb0(%0: ptr, %1: u32):
    switch %1 [ 0: bb15 1: bb14 2: bb13 3: bb12 4: bb11 5: bb10 6: bb9 7: bb8 8: bb7 9: bb6 10: bb5 11: bb4 12: bb3 13: bb2 default: bb1 ]
bb1:
    %2 = const i8 14
    store i8 %2, ptr %0
    br bb16
bb2:
    %3 = const i8 13
    store i8 %3, ptr %0
    br bb16
bb3:
    %4 = const i8 12
    store i8 %4, ptr %0
    br bb16
bb4:
    %5 = const i8 11
    store i8 %5, ptr %0
    br bb16
bb5:
    %6 = const i8 10
    store i8 %6, ptr %0
    br bb16
bb6:
    %7 = const i8 9
    store i8 %7, ptr %0
    br bb16
bb7:
    %8 = const i8 8
    store i8 %8, ptr %0
    br bb16
bb8:
    %9 = const i8 7
    store i8 %9, ptr %0
    br bb16
bb9:
    %10 = const i8 6
    store i8 %10, ptr %0
    br bb16
bb10:
    %11 = const i8 5
    store i8 %11, ptr %0
    br bb16
bb11:
    %12 = const i8 4
    store i8 %12, ptr %0
    br bb16
bb12:
    %13 = const i8 3
    store i8 %13, ptr %0
    br bb16
bb13:
    %14 = const i8 2
    store i8 %14, ptr %0
    br bb16
bb14:
    %15 = const i8 1
    store i8 %15, ptr %0
    br bb16
bb15:
    %16 = const i8 0
    store i8 %16, ptr %0
    br bb16
bb16:
    ret
}

fn @CastOp__shape(functy.2) {
bb0(%0: ptr, %1: u8):
    %2 = alloca i8, align 1
    store u8 %1, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 0: bb9 1: bb9 2: bb9 3: bb8 4: bb8 5: bb7 6: bb7 7: bb7 8: bb7 9: bb6 10: bb6 11: bb5 12: bb4 13: bb3 14: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %5 = const i8 7
    store i8 %5, ptr %0
    br bb10
bb3:
    %6 = const i8 6
    store i8 %6, ptr %0
    br bb10
bb4:
    %7 = const i8 5
    store i8 %7, ptr %0
    br bb10
bb5:
    %8 = const i8 4
    store i8 %8, ptr %0
    br bb10
bb6:
    %9 = const i8 3
    store i8 %9, ptr %0
    br bb10
bb7:
    %10 = const i8 2
    store i8 %10, ptr %0
    br bb10
bb8:
    %11 = const i8 1
    store i8 %11, ptr %0
    br bb10
bb9:
    %12 = const i8 0
    store i8 %12, ptr %0
    br bb10
bb10:
    ret
}

fn @cast_shape_tag(functy.3) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 0: bb9 1: bb8 2: bb7 3: bb6 4: bb5 5: bb4 6: bb3 7: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %5 = const u32 7
    br bb10(%5)
bb3:
    %6 = const u32 6
    br bb10(%6)
bb4:
    %7 = const u32 5
    br bb10(%7)
bb5:
    %8 = const u32 4
    br bb10(%8)
bb6:
    %9 = const u32 3
    br bb10(%9)
bb7:
    %10 = const u32 2
    br bb10(%10)
bb8:
    %11 = const u32 1
    br bb10(%11)
bb9:
    %12 = const u32 0
    br bb10(%12)
bb10(%1: u32):
    ret %1
}

fn @CastOp__is_layout_sensitive(functy.4) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 11: bb2 12: bb2 13: bb2 14: bb2 default: bb1 ]
bb1:
    %5 = const bool false
    br bb3(%5)
bb2:
    %6 = const bool true
    br bb3(%6)
bb3(%1: bool):
    ret %1
}
"#;

const MIR_LANE_COUNT_TRUST_IR: &str = r#"; TrustIr text format v1
module "mir::closure::lane_count_entry"

functy.0 = (u32, u64, u32) -> (i64)

functy.1 = (ptr, u32, u64) -> ()

functy.2 = (ptr, ptr) -> ()

functy.3 = (ptr) -> (bool)

functy.4 = (ptr, u32) -> ()

fn @lane_count_entry(functy.0) {
bb0(%0: u32, %1: u64, %2: u32):
    %7 = alloca (i64, i64, i64), align 8
    %8 = alloca (i32, i32), align 4
    call @func.1(%7, %0, %1)
    br bb1(%2)
bb1(%3: u32):
    %9 = const u32 0
    %10 = icmp eq u32 %3, %9
    condbr %10, bb2, bb7
bb2:
    call @func.2(%8, %7)
    br bb3
bb3:
    %11 = load i32, ptr %8
    %12 = sext i32 %11 to i64
    switch %12 [ 0: bb5 1: bb6 default: bb4 ]
bb4:
    unreachable
bb5:
    %13 = const i64 -1
    br bb9(%13)
bb6:
    %14 = const i64 4
    %15 = gep i8, ptr %8, %14
    %16 = load u32, ptr %15
    %17 = zext u32 %16 to i64
    br bb9(%17)
bb7:
    %18 = call @func.3(%7)
    br bb8(%18)
bb8(%4: bool):
    %19 = const i64 1
    %20 = const i64 0
    %21 = select i64 %4, %19, %20
    br bb9(%21)
bb9(%5: i64):
    br bb10(%5)
bb10(%6: i64):
    ret %6
}

fn @ty_for_tag(functy.1) {
bb0(%0: ptr, %1: u32, %2: u64):
    %5 = alloca i32, align 4
    %6 = alloca i32, align 4
    %7 = alloca i32, align 4
    %8 = alloca i32, align 4
    %9 = alloca i8, align 1
    %10 = alloca i32, align 4
    switch %1 [ 1: bb11(%2) 2: bb10 3: bb9 4: bb8 5: bb7 7: bb6 8: bb5 9: bb4 10: bb3 11: bb2 default: bb1 ]
bb1:
    %11 = const i64 -9223372036854775806
    store i64 %11, ptr %0
    br bb15
bb2:
    %12 = const u32 0
    store u32 %12, ptr %10
    %13 = const i64 8
    %14 = gep i8, ptr %0, %13
    %15 = load i32, ptr %10
    store i32 %15, ptr %14
    %16 = const i64 -9223372036854775777
    store i64 %16, ptr %0
    br bb15
bb3:
    %17 = const u32 0
    call @func.4(%8, %17)
    br bb14
bb4:
    %18 = const i64 -9223372036854775790
    store i64 %18, ptr %0
    br bb15
bb5:
    %19 = const u32 0
    call @func.4(%7, %19)
    br bb13
bb6:
    %20 = const i64 -9223372036854775791
    store i64 %20, ptr %0
    br bb15
bb7:
    %21 = const u32 0
    store u32 %21, ptr %6
    %22 = const i64 8
    %23 = gep i8, ptr %0, %22
    %24 = load i32, ptr %6
    store i32 %24, ptr %23
    %25 = const i64 -9223372036854775789
    store i64 %25, ptr %0
    br bb15
bb8:
    %26 = const i64 -9223372036854775793
    store i64 %26, ptr %0
    br bb15
bb9:
    %27 = const i64 -9223372036854775795
    store i64 %27, ptr %0
    br bb15
bb10:
    %28 = const i64 -9223372036854775805
    store i64 %28, ptr %0
    br bb15
bb11(%3: u64):
    %29 = const u32 0
    call @func.4(%5, %29)
    br bb12(%3)
bb12(%4: u64):
    %30 = const i64 16
    %31 = gep i8, ptr %0, %30
    %32 = load i32, ptr %5
    store i32 %32, ptr %31
    %33 = const i64 8
    %34 = gep i8, ptr %0, %33
    store u64 %4, ptr %34
    %35 = const i64 -9223372036854775788
    store i64 %35, ptr %0
    br bb15
bb13:
    %36 = const i64 8
    %37 = gep i8, ptr %0, %36
    %38 = load i32, ptr %7
    store i32 %38, ptr %37
    %39 = const i64 -9223372036854775778
    store i64 %39, ptr %0
    br bb15
bb14:
    %40 = const i8 1
    store i8 %40, ptr %9
    %41 = const i64 8
    %42 = gep i8, ptr %0, %41
    %43 = load i32, ptr %8
    store i32 %43, ptr %42
    %44 = const i64 12
    %45 = gep i8, ptr %0, %44
    %46 = load i8, ptr %9
    store i8 %46, ptr %45
    %47 = const i64 -9223372036854775779
    store i64 %47, ptr %0
    br bb15
bb15:
    ret
}

fn @Ty__element_op_lane_count(functy.2) {
bb0(%0: ptr, %1: ptr):
    %3 = alloca i64, align 8
    store ptr %1, ptr %3
    %4 = load ptr, ptr %3
    %5 = load i64, ptr %4
    %6 = const i64 21
    %7 = const i64 -9223372036854775808
    %8 = icmp eq i64 %5, %7
    %9 = const i64 0
    %10 = select i64 %8, %9, %6
    %11 = const i64 -9223372036854775807
    %12 = icmp eq i64 %5, %11
    %13 = const i64 1
    %14 = select i64 %12, %13, %10
    %15 = const i64 -9223372036854775806
    %16 = icmp eq i64 %5, %15
    %17 = const i64 2
    %18 = select i64 %16, %17, %14
    %19 = const i64 -9223372036854775805
    %20 = icmp eq i64 %5, %19
    %21 = const i64 3
    %22 = select i64 %20, %21, %18
    %23 = const i64 -9223372036854775804
    %24 = icmp eq i64 %5, %23
    %25 = const i64 4
    %26 = select i64 %24, %25, %22
    %27 = const i64 -9223372036854775803
    %28 = icmp eq i64 %5, %27
    %29 = const i64 5
    %30 = select i64 %28, %29, %26
    %31 = const i64 -9223372036854775802
    %32 = icmp eq i64 %5, %31
    %33 = const i64 6
    %34 = select i64 %32, %33, %30
    %35 = const i64 -9223372036854775801
    %36 = icmp eq i64 %5, %35
    %37 = const i64 7
    %38 = select i64 %36, %37, %34
    %39 = const i64 -9223372036854775800
    %40 = icmp eq i64 %5, %39
    %41 = const i64 8
    %42 = select i64 %40, %41, %38
    %43 = const i64 -9223372036854775799
    %44 = icmp eq i64 %5, %43
    %45 = const i64 9
    %46 = select i64 %44, %45, %42
    %47 = const i64 -9223372036854775798
    %48 = icmp eq i64 %5, %47
    %49 = const i64 10
    %50 = select i64 %48, %49, %46
    %51 = const i64 -9223372036854775797
    %52 = icmp eq i64 %5, %51
    %53 = const i64 11
    %54 = select i64 %52, %53, %50
    %55 = const i64 -9223372036854775796
    %56 = icmp eq i64 %5, %55
    %57 = const i64 12
    %58 = select i64 %56, %57, %54
    %59 = const i64 -9223372036854775795
    %60 = icmp eq i64 %5, %59
    %61 = const i64 13
    %62 = select i64 %60, %61, %58
    %63 = const i64 -9223372036854775794
    %64 = icmp eq i64 %5, %63
    %65 = const i64 14
    %66 = select i64 %64, %65, %62
    %67 = const i64 -9223372036854775793
    %68 = icmp eq i64 %5, %67
    %69 = const i64 15
    %70 = select i64 %68, %69, %66
    %71 = const i64 -9223372036854775792
    %72 = icmp eq i64 %5, %71
    %73 = const i64 16
    %74 = select i64 %72, %73, %70
    %75 = const i64 -9223372036854775791
    %76 = icmp eq i64 %5, %75
    %77 = const i64 17
    %78 = select i64 %76, %77, %74
    %79 = const i64 -9223372036854775790
    %80 = icmp eq i64 %5, %79
    %81 = const i64 18
    %82 = select i64 %80, %81, %78
    %83 = const i64 -9223372036854775789
    %84 = icmp eq i64 %5, %83
    %85 = const i64 19
    %86 = select i64 %84, %85, %82
    %87 = const i64 -9223372036854775788
    %88 = icmp eq i64 %5, %87
    %89 = const i64 20
    %90 = select i64 %88, %89, %86
    %91 = const i64 -9223372036854775786
    %92 = icmp eq i64 %5, %91
    %93 = const i64 22
    %94 = select i64 %92, %93, %90
    %95 = const i64 -9223372036854775785
    %96 = icmp eq i64 %5, %95
    %97 = const i64 23
    %98 = select i64 %96, %97, %94
    %99 = const i64 -9223372036854775784
    %100 = icmp eq i64 %5, %99
    %101 = const i64 24
    %102 = select i64 %100, %101, %98
    %103 = const i64 -9223372036854775783
    %104 = icmp eq i64 %5, %103
    %105 = const i64 25
    %106 = select i64 %104, %105, %102
    %107 = const i64 -9223372036854775782
    %108 = icmp eq i64 %5, %107
    %109 = const i64 26
    %110 = select i64 %108, %109, %106
    %111 = const i64 -9223372036854775781
    %112 = icmp eq i64 %5, %111
    %113 = const i64 27
    %114 = select i64 %112, %113, %110
    %115 = const i64 -9223372036854775780
    %116 = icmp eq i64 %5, %115
    %117 = const i64 28
    %118 = select i64 %116, %117, %114
    %119 = const i64 -9223372036854775779
    %120 = icmp eq i64 %5, %119
    %121 = const i64 29
    %122 = select i64 %120, %121, %118
    %123 = const i64 -9223372036854775778
    %124 = icmp eq i64 %5, %123
    %125 = const i64 30
    %126 = select i64 %124, %125, %122
    %127 = const i64 -9223372036854775777
    %128 = icmp eq i64 %5, %127
    %129 = const i64 31
    %130 = select i64 %128, %129, %126
    %131 = const i64 -9223372036854775776
    %132 = icmp eq i64 %5, %131
    %133 = const i64 32
    %134 = select i64 %132, %133, %130
    switch %134 [ 14: bb3 20: bb2 default: bb1 ]
bb1:
    %135 = const i32 0
    store i32 %135, ptr %0
    br bb6
bb2:
    %136 = load ptr, ptr %3
    %137 = const i64 8
    %138 = gep i8, ptr %136, %137
    %139 = load u64, ptr %138
    %140 = const u32 4294967295
    %141 = zext u32 %140 to u64
    %142 = icmp ule u64 %139, %141
    condbr %142, bb4(%138), bb5
bb3:
    %143 = load ptr, ptr %3
    %144 = const i64 16
    %145 = gep i8, ptr %143, %144
    %146 = load u32, ptr %145
    %147 = const i64 4
    %148 = gep i8, ptr %0, %147
    store u32 %146, ptr %148
    %149 = const i32 1
    store i32 %149, ptr %0
    br bb6
bb4(%2: ptr):
    %150 = load u64, ptr %2
    %151 = trunc u64 %150 to u32
    %152 = const i64 4
    %153 = gep i8, ptr %0, %152
    store u32 %151, ptr %153
    %154 = const i32 1
    store i32 %154, ptr %0
    br bb6
bb5:
    %155 = const i32 0
    store i32 %155, ptr %0
    br bb6
bb6:
    ret
}

fn @Ty__supports_element_ops(functy.3) {
bb0(%0: ptr):
    %2 = load i64, ptr %0
    %3 = const i64 21
    %4 = const i64 -9223372036854775808
    %5 = icmp eq i64 %2, %4
    %6 = const i64 0
    %7 = select i64 %5, %6, %3
    %8 = const i64 -9223372036854775807
    %9 = icmp eq i64 %2, %8
    %10 = const i64 1
    %11 = select i64 %9, %10, %7
    %12 = const i64 -9223372036854775806
    %13 = icmp eq i64 %2, %12
    %14 = const i64 2
    %15 = select i64 %13, %14, %11
    %16 = const i64 -9223372036854775805
    %17 = icmp eq i64 %2, %16
    %18 = const i64 3
    %19 = select i64 %17, %18, %15
    %20 = const i64 -9223372036854775804
    %21 = icmp eq i64 %2, %20
    %22 = const i64 4
    %23 = select i64 %21, %22, %19
    %24 = const i64 -9223372036854775803
    %25 = icmp eq i64 %2, %24
    %26 = const i64 5
    %27 = select i64 %25, %26, %23
    %28 = const i64 -9223372036854775802
    %29 = icmp eq i64 %2, %28
    %30 = const i64 6
    %31 = select i64 %29, %30, %27
    %32 = const i64 -9223372036854775801
    %33 = icmp eq i64 %2, %32
    %34 = const i64 7
    %35 = select i64 %33, %34, %31
    %36 = const i64 -9223372036854775800
    %37 = icmp eq i64 %2, %36
    %38 = const i64 8
    %39 = select i64 %37, %38, %35
    %40 = const i64 -9223372036854775799
    %41 = icmp eq i64 %2, %40
    %42 = const i64 9
    %43 = select i64 %41, %42, %39
    %44 = const i64 -9223372036854775798
    %45 = icmp eq i64 %2, %44
    %46 = const i64 10
    %47 = select i64 %45, %46, %43
    %48 = const i64 -9223372036854775797
    %49 = icmp eq i64 %2, %48
    %50 = const i64 11
    %51 = select i64 %49, %50, %47
    %52 = const i64 -9223372036854775796
    %53 = icmp eq i64 %2, %52
    %54 = const i64 12
    %55 = select i64 %53, %54, %51
    %56 = const i64 -9223372036854775795
    %57 = icmp eq i64 %2, %56
    %58 = const i64 13
    %59 = select i64 %57, %58, %55
    %60 = const i64 -9223372036854775794
    %61 = icmp eq i64 %2, %60
    %62 = const i64 14
    %63 = select i64 %61, %62, %59
    %64 = const i64 -9223372036854775793
    %65 = icmp eq i64 %2, %64
    %66 = const i64 15
    %67 = select i64 %65, %66, %63
    %68 = const i64 -9223372036854775792
    %69 = icmp eq i64 %2, %68
    %70 = const i64 16
    %71 = select i64 %69, %70, %67
    %72 = const i64 -9223372036854775791
    %73 = icmp eq i64 %2, %72
    %74 = const i64 17
    %75 = select i64 %73, %74, %71
    %76 = const i64 -9223372036854775790
    %77 = icmp eq i64 %2, %76
    %78 = const i64 18
    %79 = select i64 %77, %78, %75
    %80 = const i64 -9223372036854775789
    %81 = icmp eq i64 %2, %80
    %82 = const i64 19
    %83 = select i64 %81, %82, %79
    %84 = const i64 -9223372036854775788
    %85 = icmp eq i64 %2, %84
    %86 = const i64 20
    %87 = select i64 %85, %86, %83
    %88 = const i64 -9223372036854775786
    %89 = icmp eq i64 %2, %88
    %90 = const i64 22
    %91 = select i64 %89, %90, %87
    %92 = const i64 -9223372036854775785
    %93 = icmp eq i64 %2, %92
    %94 = const i64 23
    %95 = select i64 %93, %94, %91
    %96 = const i64 -9223372036854775784
    %97 = icmp eq i64 %2, %96
    %98 = const i64 24
    %99 = select i64 %97, %98, %95
    %100 = const i64 -9223372036854775783
    %101 = icmp eq i64 %2, %100
    %102 = const i64 25
    %103 = select i64 %101, %102, %99
    %104 = const i64 -9223372036854775782
    %105 = icmp eq i64 %2, %104
    %106 = const i64 26
    %107 = select i64 %105, %106, %103
    %108 = const i64 -9223372036854775781
    %109 = icmp eq i64 %2, %108
    %110 = const i64 27
    %111 = select i64 %109, %110, %107
    %112 = const i64 -9223372036854775780
    %113 = icmp eq i64 %2, %112
    %114 = const i64 28
    %115 = select i64 %113, %114, %111
    %116 = const i64 -9223372036854775779
    %117 = icmp eq i64 %2, %116
    %118 = const i64 29
    %119 = select i64 %117, %118, %115
    %120 = const i64 -9223372036854775778
    %121 = icmp eq i64 %2, %120
    %122 = const i64 30
    %123 = select i64 %121, %122, %119
    %124 = const i64 -9223372036854775777
    %125 = icmp eq i64 %2, %124
    %126 = const i64 31
    %127 = select i64 %125, %126, %123
    %128 = const i64 -9223372036854775776
    %129 = icmp eq i64 %2, %128
    %130 = const i64 32
    %131 = select i64 %129, %130, %127
    switch %131 [ 14: bb2 20: bb2 default: bb1 ]
bb1:
    %132 = const bool false
    br bb3(%132)
bb2:
    %133 = const bool true
    br bb3(%133)
bb3(%1: bool):
    ret %1
}

fn @TyId__new(functy.4) {
bb0(%0: ptr, %1: u32):
    store u32 %1, ptr %0
    ret
}
"#;

// ===========================================================================
// cast_shape (15-arm CastOp switch) and lane_count (Ty-discriminant dispatch +
// u64->u32 checked narrowing) — two more pinned WORKING trust functions the
// integrator verified native==JIT on aarch64. Both are 0-extern, scalar-in /
// scalar-out via their `*_entry` wrappers, so the x86 faithful test needs no
// shims and no enum layout: call the entry over the same case grid under Rosetta
// and compare to the VERBATIM native oracle. Confirms x86 handles these
// multi-arm functions correctly too. (Native oracles copied verbatim from
// e2e_frontend_roundtrip.rs.)
// ===========================================================================

fn cast_shape_tag_native(op_tag: u32) -> u32 {
    match op_tag {
        0 | 1 | 2 => 0,
        3 | 4 => 1,
        5 | 6 | 7 | 8 => 2,
        9 | 10 => 3,
        11 => 4,
        12 => 5,
        13 => 6,
        14 => 7,
        _ => unreachable!("bad CastOp tag"),
    }
}
fn is_layout_sensitive_native(op_tag: u32) -> u32 {
    matches!(op_tag, 11 | 12 | 13 | 14) as u32
}
fn lane_count_native(tag: u32, aux: u64) -> i64 {
    match tag {
        1 => {
            if aux <= u32::MAX as u64 {
                aux as i64
            } else {
                -1
            }
        }
        _ => -1,
    }
}
fn supports_element_ops_native(tag: u32) -> i64 {
    (tag == 1) as i64
}

fn run_scalar_entry(test: &str, ir: &str, driver_c: &str) -> Result<String, String> {
    if !common::rosetta::has_cc_x86_64_link_run() {
        return Err("skip: cc -arch x86_64 link/run unavailable".to_string());
    }
    let module = trust_ir::parser::parse_module(ir).map_err(|e| format!("parse: {e:?}"))?;
    let mut out = String::new();
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let obj = compile_x86_64_at(&module, opt)?;
        let dir = std::env::temp_dir().join(format!("trust_cg_scale_{test}_{opt:?}"));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let obj_path = dir.join("f.o");
        std::fs::write(&obj_path, &obj).unwrap();
        let drv = dir.join("driver.c");
        std::fs::write(&drv, driver_c).unwrap();
        let bin = dir.join("bin");
        let link = Command::new("cc")
            .args(if cfg!(target_os = "macos") {
                &["-arch", "x86_64"][..]
            } else {
                &[][..]
            })
            .args([
                "-O0",
                "-o",
                bin.to_str().unwrap(),
                drv.to_str().unwrap(),
                obj_path.to_str().unwrap(),
            ])
            .output()
            .map_err(|e| format!("cc: {e}"))?;
        if !link.status.success() {
            return Err(format!(
                "LINK FAIL ({opt:?}): {}\n{}",
                String::from_utf8_lossy(&link.stderr),
                nm_dump(&obj_path)
            ));
        }
        let run = Command::new(&bin)
            .output()
            .map_err(|e| format!("run: {e}"))?;
        if !run.status.success() {
            return Err(format!("RUN FAIL ({opt:?}): {:?}", run.status.code()));
        }
        // All opt levels must agree with each other and the oracle; return O0's text,
        // but verify every opt level produces identical stdout (determinism).
        let s = String::from_utf8_lossy(&run.stdout).to_string();
        if opt == OptLevel::O0 {
            out = s;
        } else if s != out {
            return Err(format!(
                "opt {opt:?} stdout differs from O0:\n O0={out}\n{opt:?}={s}"
            ));
        }
    }
    Ok(out)
}

#[test]
fn x86_64_cast_shape_faithful() {
    if !common::rosetta::has_cc_x86_64_link_run() {
        eprintln!("skip: cc -arch x86_64 link/run unavailable");
        return;
    }
    let driver = r####"
#include <stdio.h>
extern unsigned cast_shape_entry(unsigned op_tag, unsigned which) __asm__("_cast_shape_entry");
int main(void) {
    for (unsigned t = 0; t < 15; t++) {
        printf("%u %u %u\n", t, cast_shape_entry(t, 0), cast_shape_entry(t, 1));
    }
    return 0;
}
"####;
    let out = run_scalar_entry("cast_shape", MIR_CAST_SHAPE_TRUST_IR, driver)
        .unwrap_or_else(|e| panic!("cast_shape x86 run failed: {e}"));
    let mut checked = 0;
    for line in out.lines() {
        let p: Vec<&str> = line.split_whitespace().collect();
        if p.len() != 3 {
            continue;
        }
        let tag: u32 = p[0].parse().unwrap();
        let shape: u32 = p[1].parse().unwrap();
        let ls: u32 = p[2].parse().unwrap();
        assert_eq!(
            shape,
            cast_shape_tag_native(tag),
            "cast_shape SHAPE mismatch tag={tag}"
        );
        assert_eq!(
            ls,
            is_layout_sensitive_native(tag),
            "cast_shape is_layout_sensitive mismatch tag={tag}"
        );
        checked += 1;
    }
    assert_eq!(checked, 15, "all 15 CastOp arms must be checked");
    eprintln!("[cast_shape] 15 arms x {{shape,is_layout_sensitive}} x O0/O1/O2/O3 all correct");
}

#[test]
fn x86_64_lane_count_faithful() {
    if !common::rosetta::has_cc_x86_64_link_run() {
        eprintln!("skip: cc -arch x86_64 link/run unavailable");
        return;
    }
    // (tag, name) menu and aux grid VERBATIM from the integrator's test.
    let tags: [u32; 11] = [1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12];
    let auxes: [u64; 6] = [0, 1, 1000, u32::MAX as u64, (u32::MAX as u64) + 1, u64::MAX];
    let mut decl = String::from("static unsigned T[]={");
    decl.push_str(
        &tags
            .iter()
            .map(|t| t.to_string())
            .collect::<Vec<_>>()
            .join(","),
    );
    decl.push_str("}; static unsigned long long A[]={");
    decl.push_str(
        &auxes
            .iter()
            .map(|a| format!("{a}ull"))
            .collect::<Vec<_>>()
            .join(","),
    );
    decl.push_str("};");
    let driver = format!(
        r####"
#include <stdio.h>
extern long long lane_count_entry(unsigned tag, unsigned long long aux, unsigned which) __asm__("_lane_count_entry");
{decl}
int main(void) {{
    for (int i = 0; i < 11; i++) {{
        for (int j = 0; j < 6; j++) {{
            printf("%u %llu %lld %lld\n", T[i], A[j],
                   lane_count_entry(T[i], A[j], 0), lane_count_entry(T[i], A[j], 1));
        }}
    }}
    return 0;
}}
"####
    );
    let out = run_scalar_entry("lane_count", MIR_LANE_COUNT_TRUST_IR, &driver)
        .unwrap_or_else(|e| panic!("lane_count x86 run failed: {e}"));
    let mut checked = 0;
    for line in out.lines() {
        let p: Vec<&str> = line.split_whitespace().collect();
        if p.len() != 4 {
            continue;
        }
        let tag: u32 = p[0].parse().unwrap();
        let aux: u64 = p[1].parse().unwrap();
        let lc: i64 = p[2].parse().unwrap();
        let se: i64 = p[3].parse().unwrap();
        assert_eq!(
            lc,
            lane_count_native(tag, aux),
            "element_op_lane_count mismatch tag={tag} aux={aux}"
        );
        assert_eq!(
            se,
            supports_element_ops_native(tag),
            "supports_element_ops mismatch tag={tag}"
        );
        checked += 1;
    }
    assert_eq!(checked, 11 * 6, "all tag x aux cases must be checked");
    eprintln!(
        "[lane_count] 11 tys x 6 auxes x {{lane_count,supports_element_ops}} x O0/O1/O2/O3 all correct"
    );
}
