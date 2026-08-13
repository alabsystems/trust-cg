// trust-cg-codegen/tests/e2e_aarch64_fp_loop_carried_reduction.rs
//
// End-to-end differential for SCALAR FP loop-carried reductions — the FPR
// block-argument copy P0.
//
// ISel lowered EVERY block-argument copy (the adapter's single-arg-Iadd COPY)
// to `AArch64Opcode::MovR`, which encodes as `ORR Rd, XZR, Rm` — a GPR-ONLY
// instruction. For a loop-carried f32/f64 accumulator the register allocator
// correctly assigned S/D registers, but the GPR `MovR` encoding then named the
// FPR's 5-bit hw index as an unrelated GPR: the FP value never moved AND a
// live GPR (in the original repro, the array pointer) was clobbered —
// SIGSEGV/garbage at ALL opt levels (-O0/-O1/-O2). Integer kernels never hit
// it because `MovR` is the correct copy for GPRs.
//
// These tests pin the fix end-to-end: f32 AND f64 loop-carried sum,
// dot-product, and max-reduction, each compiled at -O0/-O1/-O2 through the
// full module pipeline, linked against a clang -O0 C reference and compared
// BIT-EXACTLY (both sides evaluate in strict IEEE program order — trust-cg
// must not reassociate these scalar loops) across n = 0/1/edge sweeps and
// rounding-sensitive value patterns.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{BinOp, FCmpOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

/// Build one module with the three scalar loop-carried FP reduction kernels
/// for float type `fty`:
///
///   fsum(ptr a, i32 n) -> fty:        s = 0.0;    for i: s += a[i]
///   fdot(ptr a, ptr b, i32 n) -> fty: s = 0.0;    for i: s += a[i] * b[i]
///   fmax(ptr a, i32 n) -> fty:        m = -inf;   for i: m = a[i] > m ? a[i] : m
///
/// All three carry the FP accumulator through block arguments across the loop
/// back-edge — the exact shape whose FPR copies were miscompiled as GPR movs.
fn build_module(fty: Ty) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("fp_loop_carried_reduction");

    // fsum
    let sum_ty = mb.add_func_type(vec![Ty::Ptr, Ty::I32], vec![fty.clone()]);
    {
        let mut fb = mb.function("fsum", sum_ty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::Ptr);
        let n = fb.add_block_param(entry, Ty::I32);

        let header = fb.create_block();
        let iv = fb.add_block_param(header, Ty::I32);
        let acc = fb.add_block_param(header, fty.clone());

        let body = fb.create_block();
        let biv = fb.add_block_param(body, Ty::I32);
        let bacc = fb.add_block_param(body, fty.clone());

        let exit = fb.create_block();
        let result = fb.add_block_param(exit, fty.clone());

        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::I32, 0);
        let fzero = fb.fconst(fty.clone(), 0.0);
        fb.br(header, vec![zero, fzero]);

        fb.switch_to_block(header);
        let in_range = fb.icmp(ICmpOp::Slt, Ty::I32, iv, n);
        fb.condbr(in_range, body, vec![iv, acc], exit, vec![acc]);

        fb.switch_to_block(body);
        let one = fb.iconst(Ty::I32, 1);
        let ptr = fb.gep(fty.clone(), a, vec![biv]);
        let x = fb.load(fty.clone(), ptr);
        let acc2 = fb.binop(BinOp::FAdd, fty.clone(), bacc, x);
        let iv2 = fb.binop(BinOp::Add, Ty::I32, biv, one);
        fb.br(header, vec![iv2, acc2]);

        fb.switch_to_block(exit);
        fb.ret(vec![result]);
        fb.build();
    }

    // fdot
    let dot_ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::I32], vec![fty.clone()]);
    {
        let mut fb = mb.function("fdot", dot_ty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::Ptr);
        let b = fb.add_block_param(entry, Ty::Ptr);
        let n = fb.add_block_param(entry, Ty::I32);

        let header = fb.create_block();
        let iv = fb.add_block_param(header, Ty::I32);
        let acc = fb.add_block_param(header, fty.clone());

        let body = fb.create_block();
        let biv = fb.add_block_param(body, Ty::I32);
        let bacc = fb.add_block_param(body, fty.clone());

        let exit = fb.create_block();
        let result = fb.add_block_param(exit, fty.clone());

        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::I32, 0);
        let fzero = fb.fconst(fty.clone(), 0.0);
        fb.br(header, vec![zero, fzero]);

        fb.switch_to_block(header);
        let in_range = fb.icmp(ICmpOp::Slt, Ty::I32, iv, n);
        fb.condbr(in_range, body, vec![iv, acc], exit, vec![acc]);

        fb.switch_to_block(body);
        let one = fb.iconst(Ty::I32, 1);
        let pa = fb.gep(fty.clone(), a, vec![biv]);
        let pb = fb.gep(fty.clone(), b, vec![biv]);
        let xa = fb.load(fty.clone(), pa);
        let xb = fb.load(fty.clone(), pb);
        let prod = fb.binop(BinOp::FMul, fty.clone(), xa, xb);
        let acc2 = fb.binop(BinOp::FAdd, fty.clone(), bacc, prod);
        let iv2 = fb.binop(BinOp::Add, Ty::I32, biv, one);
        fb.br(header, vec![iv2, acc2]);

        fb.switch_to_block(exit);
        fb.ret(vec![result]);
        fb.build();
    }

    // fmax
    let max_ty = mb.add_func_type(vec![Ty::Ptr, Ty::I32], vec![fty.clone()]);
    {
        let mut fb = mb.function("fmax_red", max_ty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::Ptr);
        let n = fb.add_block_param(entry, Ty::I32);

        let header = fb.create_block();
        let iv = fb.add_block_param(header, Ty::I32);
        let acc = fb.add_block_param(header, fty.clone());

        let body = fb.create_block();
        let biv = fb.add_block_param(body, Ty::I32);
        let bacc = fb.add_block_param(body, fty.clone());

        let exit = fb.create_block();
        let result = fb.add_block_param(exit, fty.clone());

        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::I32, 0);
        let ninf = fb.fconst(fty.clone(), f64::NEG_INFINITY);
        fb.br(header, vec![zero, ninf]);

        fb.switch_to_block(header);
        let in_range = fb.icmp(ICmpOp::Slt, Ty::I32, iv, n);
        fb.condbr(in_range, body, vec![iv, acc], exit, vec![acc]);

        fb.switch_to_block(body);
        let one = fb.iconst(Ty::I32, 1);
        let ptr = fb.gep(fty.clone(), a, vec![biv]);
        let x = fb.load(fty.clone(), ptr);
        // Ordered greater-than + select mirrors the C `a[i] > m ? a[i] : m`.
        let gt = fb.fcmp(FCmpOp::OGt, fty.clone(), x, bacc);
        let m2 = fb.select(fty.clone(), gt, x, bacc);
        let iv2 = fb.binop(BinOp::Add, Ty::I32, biv, one);
        fb.br(header, vec![iv2, m2]);

        fb.switch_to_block(exit);
        fb.ret(vec![result]);
        fb.build();
    }

    mb.build()
}

fn compile_at(module: &trust_ir::Module, opt: OptLevel) -> Result<Vec<u8>, String> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    });
    compiler
        .compile(module)
        .map(|r| r.object_code)
        .map_err(|e| format!("{e:?}"))
}

/// C driver template. `FT` is substituted with `float` / `double`, `SUF` with
/// the printf-safe tag. The reference loops are compiled by clang at -O0
/// (no flags => -O0): strict IEEE program order on both sides, so results
/// must match BIT-exactly.
const DRIVER_TEMPLATE: &str = r#"
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

typedef FT ft;
extern ft fsum(ft*, int32_t);
extern ft fdot(ft*, ft*, int32_t);
extern ft fmax_red(ft*, int32_t);

static ft ref_sum(const ft* a, int n) {
    ft s = (ft)0.0;
    for (int i = 0; i < n; i++) s += a[i];
    return s;
}
static ft ref_dot(const ft* a, const ft* b, int n) {
    ft s = (ft)0.0;
    for (int i = 0; i < n; i++) s += a[i] * b[i];
    return s;
}
static ft ref_max(const ft* a, int n) {
    ft m = (ft)-INFINITY;
    for (int i = 0; i < n; i++) m = a[i] > m ? a[i] : m;
    return m;
}

static int bits_equal(ft x, ft y) { return memcmp(&x, &y, sizeof(ft)) == 0; }

int main(void) {
    /* n sweep: empty, single, small, boundary-adjacent, large. */
    int ns[] = {0, 1, 2, 3, 4, 7, 8, 15, 16, 17, 33, 100, 1000};
    static ft a[1000], b[1000];
    for (int pat = 0; pat < 5; pat++) {
        for (unsigned k = 0; k < sizeof(ns) / sizeof(ns[0]); k++) {
            int n = ns[k];
            uint32_t seed = 0x9E3779B9u + (uint32_t)pat * 2654435761u;
            for (int i = 0; i < n; i++) {
                switch (pat) {
                    case 0: /* simple ramp */
                        a[i] = (ft)(i + 1) * (ft)0.5;
                        b[i] = (ft)(n - i) * (ft)0.25;
                        break;
                    case 1: /* alternating signs — cancellation order matters */
                        a[i] = (i & 1) ? (ft)-1.5 : (ft)2.25;
                        b[i] = (i & 1) ? (ft)3.5 : (ft)-0.125;
                        break;
                    case 2: /* rounding-sensitive: non-representable steps */
                        a[i] = (ft)0.1 * (ft)(i + 1);
                        b[i] = (ft)0.3;
                        break;
                    case 3: /* mixed magnitudes — reassociation diverges here */
                        a[i] = (i % 3 == 0) ? (ft)1e8 : (ft)-1.0;
                        b[i] = (i % 3 == 1) ? (ft)1e-8 : (ft)7.0;
                        break;
                    default: /* pseudo-random in [-1, 1] */
                        seed = seed * 1664525u + 1013904223u;
                        a[i] = ((ft)(int32_t)seed) / (ft)2147483648.0;
                        seed = seed * 1664525u + 1013904223u;
                        b[i] = ((ft)(int32_t)seed) / (ft)2147483648.0;
                        break;
                }
            }
            ft ws = ref_sum(a, n),        gs = fsum(a, n);
            ft wd = ref_dot(a, b, n),     gd = fdot(a, b, n);
            ft wm = ref_max(a, n),        gm = fmax_red(a, n);
            if (!bits_equal(gs, ws)) {
                printf("SUM MISMATCH pat=%d n=%d got=%a want=%a\n",
                       pat, n, (double)gs, (double)ws);
                return 1;
            }
            if (!bits_equal(gd, wd)) {
                printf("DOT MISMATCH pat=%d n=%d got=%a want=%a\n",
                       pat, n, (double)gd, (double)wd);
                return 1;
            }
            if (!bits_equal(gm, wm)) {
                printf("MAX MISMATCH pat=%d n=%d got=%a want=%a\n",
                       pat, n, (double)gm, (double)wm);
                return 1;
            }
        }
    }
    printf("fp loop-carried reductions: all differential checks passed\n");
    return 0;
}
"#;

/// Link `obj` against the type-specialized driver, run it, and return
/// (exit_code, kernel object disassembly).
fn link_run_disasm(tag: &str, obj: &[u8], c_float_ty: &str) -> Option<(i32, String, String)> {
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
    fs::write(&drv_path, DRIVER_TEMPLATE.replace("FT", c_float_ty)).unwrap();
    // -ffp-contract=off: clang's DEFAULT (-ffp-contract=on, even at -O0)
    // fuses `s += a[i] * b[i]` into FMADD inside the C REFERENCE, which
    // rounds once instead of twice — a 1-ulp divergence that is a property
    // of the reference, not of trust-cg. trust-ir FMul/FAdd are separate,
    // strictly-rounded IEEE ops (trust-cg emits fmul+fadd, never fmadd,
    // at every opt level), so the reference must match that evaluation.
    let link = Command::new("cc")
        .args([
            "-ffp-contract=off",
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
    let run = Command::new(bin_path.to_str().unwrap()).output().unwrap();
    let code = run.status.code().unwrap_or(-1);
    let stdout = String::from_utf8_lossy(&run.stdout).to_string();
    let disasm = Command::new("objdump")
        .args(["-d", obj_path.to_str().unwrap()])
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).to_string())
        .unwrap_or_default();
    let _ = fs::remove_dir_all(&dir);
    Some((code, disasm, stdout))
}

fn run_case(fty: Ty, c_float_ty: &str, fadd_mnemonic: &str, tag: &str) {
    let module = build_module(fty);
    for (opt, opt_tag) in [
        (OptLevel::O0, "o0"),
        (OptLevel::O1, "o1"),
        (OptLevel::O2, "o2"),
    ] {
        let obj = compile_at(&module, opt)
            .unwrap_or_else(|e| panic!("{tag} {opt_tag} must compile: {e}"));
        let Some((code, disasm, stdout)) =
            link_run_disasm(&format!("{tag}_{opt_tag}"), &obj, c_float_ty)
        else {
            return;
        };
        // Non-vacuity: the scalar FP kernels are really in the object.
        if !disasm.is_empty() {
            assert!(
                disasm.contains(fadd_mnemonic),
                "{tag} {opt_tag}: expected `{fadd_mnemonic}` in the kernel object; disasm:\n{disasm}"
            );
        }
        // The P0 signature: an FPR block-arg copy encoded as a GPR `mov x_, x_`
        // clobbers a live GPR / never moves the FP value. Before the fix this
        // exact differential SEGFAULTed at every opt level.
        assert_eq!(
            code, 0,
            "{tag} {opt_tag}: FP loop-carried reduction differential failed \
             (exit {code}); stdout:\n{stdout}\ndisasm:\n{disasm}"
        );
    }
}

#[test]
fn e2e_aarch64_f32_loop_carried_reductions_bitexact() {
    run_case(Ty::F32, "float", "fadd\ts", "fp_red_f32");
}

#[test]
fn e2e_aarch64_f64_loop_carried_reductions_bitexact() {
    run_case(Ty::F64, "double", "fadd\td", "fp_red_f64");
}
