// trust-cg-codegen/tests/e2e_aarch64_ext_stencil.rs
//
// End-to-end fail-closed differential for the stencil vectorizer.  The source
// carries public `noalias` attributes, but those producer-owned labels cannot
// authorize vectorization until exact validator replay is wired.  O2 must keep
// the scalar loop and remain bit-exact against the reference.
//
// The historical EXT formation remains covered by structural optimizer tests.
// This production-path test pins the authority boundary and the scalar fallback.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{ICmpOp, ParamAttrs, Ty};
use trust_ir_build::ModuleBuilder;

fn can_link_and_run_aarch64_macho() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

/// `kernel(ptr o, ptr a, i32 n)`: `for i in [1, n-1): o[i] = a[i-1]+a[i]+a[i+1]`
/// — the exact 3-point stencil shape `neon_stencil` recognizes. Both pointer
/// params carry public `noalias` observations; without validator replay the
/// loop must nevertheless stay scalar.
fn build_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("ext_stencil");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::I32], vec![]);
    {
        let mut fb = mb.function("kernel", ty);
        let entry = fb.create_block();
        let o = fb.add_block_param(entry, Ty::Ptr);
        let a = fb.add_block_param(entry, Ty::Ptr);
        let n = fb.add_block_param(entry, Ty::I32);

        let header = fb.create_block();
        let iv = fb.add_block_param(header, Ty::I32);

        let body = fb.create_block();
        let biv = fb.add_block_param(body, Ty::I32);

        let exit = fb.create_block();

        fb.switch_to_block(entry);
        let one_e = fb.iconst(Ty::I32, 1);
        fb.br(header, vec![one_e]);

        fb.switch_to_block(header);
        let one_h = fb.iconst(Ty::I32, 1);
        let hi = fb.binop(trust_ir::BinOp::Sub, Ty::I32, n, one_h);
        let in_range = fb.icmp(ICmpOp::Slt, Ty::I32, iv, hi);
        fb.condbr(in_range, body, vec![iv], exit, vec![]);

        fb.switch_to_block(body);
        let one = fb.iconst(Ty::I32, 1);
        let im1 = fb.binop(trust_ir::BinOp::Sub, Ty::I32, biv, one);
        let ip1 = fb.binop(trust_ir::BinOp::Add, Ty::I32, biv, one);
        let pm1 = fb.gep(Ty::I32, a, vec![im1]);
        let p0 = fb.gep(Ty::I32, a, vec![biv]);
        let pp1 = fb.gep(Ty::I32, a, vec![ip1]);
        let xm1 = fb.load(Ty::I32, pm1);
        let x0 = fb.load(Ty::I32, p0);
        let xp1 = fb.load(Ty::I32, pp1);
        let s0 = fb.binop(trust_ir::BinOp::Add, Ty::I32, xm1, x0);
        let s = fb.binop(trust_ir::BinOp::Add, Ty::I32, s0, xp1);
        let po = fb.gep(Ty::I32, o, vec![biv]);
        fb.store(Ty::I32, po, s);
        let iv2 = fb.binop(trust_ir::BinOp::Add, Ty::I32, biv, one);
        fb.br(header, vec![iv2]);

        fb.switch_to_block(exit);
        fb.ret(vec![]);
        fb.build();
    }
    let mut module = mb.build();
    // Mark BOTH pointer params `noalias` — the stencil pass's aliasing gate.
    let f = module
        .functions
        .iter_mut()
        .find(|f| f.name == "kernel")
        .expect("kernel fn");
    f.attrs.params = vec![
        ParamAttrs {
            noalias: true,
            ..Default::default()
        },
        ParamAttrs {
            noalias: true,
            ..Default::default()
        },
        ParamAttrs::default(),
    ];
    module
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

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
#include <string.h>
extern void kernel(uint32_t*, uint32_t*, int32_t);

static void ref_stencil(uint32_t* o, const uint32_t* a, int n) {
    for (int i = 1; i < n - 1; i++) o[i] = a[i-1] + a[i] + a[i+1];
}

int main(void) {
    /* n sweeps the vector-width boundaries (block = 16 lanes) plus scalar
       tails; n <= 2 leaves the loop range empty. */
    int ns[] = {0, 1, 2, 3, 4, 15, 16, 17, 18, 19, 31, 32, 33, 100, 1000};
    static uint32_t a[1000], got[1000], want[1000];
    for (int pat = 0; pat < 6; pat++) {
        for (unsigned k = 0; k < sizeof(ns) / sizeof(ns[0]); k++) {
            int n = ns[k];
            uint32_t seed = 0x9E3779B9u + (uint32_t)pat * 2654435761u;
            for (int i = 0; i < n; i++) {
                switch (pat) {
                    case 0: a[i] = 0u; break;
                    /* INT_MIN everywhere: any window misalignment changes the
                       wraparound sums */
                    case 1: a[i] = 0x80000000u; break;
                    case 2: a[i] = 0x7FFFFFFFu; break;                 /* INT_MAX */
                    /* position-sensitive ramp: a shifted window ALWAYS differs */
                    case 3: a[i] = (uint32_t)i * 0x01000193u; break;
                    case 4: a[i] = (i & 1) ? 0xFFFFFFFFu : 1u; break;
                    default:
                        seed = seed * 1664525u + 1013904223u;
                        a[i] = seed;
                        break;
                }
            }
            memset(got, 0xCC, sizeof(got));
            memset(want, 0xCC, sizeof(want));
            kernel(got, a, n);
            ref_stencil(want, a, n);
            if (memcmp(got, want, sizeof(uint32_t) * (n > 0 ? (unsigned)n : 1u)) != 0) {
                for (int i = 0; i < n; i++)
                    if (got[i] != want[i]) {
                        printf("MISMATCH pat=%d n=%d i=%d got=%u want=%u\n",
                               pat, n, i, got[i], want[i]);
                        return 1;
                    }
                return 1;
            }
        }
    }
    printf("ext stencil: all differential checks passed\n");
    return 0;
}
"#;

/// Link `obj` against the driver, run it, and return (exit_code, disassembly).
fn link_run_disasm(tag: &str, obj: &[u8]) -> Option<(i32, String)> {
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
    // Disassemble the kernel OBJECT (not the linked binary, so the -O0 driver's
    // code cannot pollute the mnemonic scan).
    let disasm = Command::new("objdump")
        .args(["-d", obj_path.to_str().unwrap()])
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).to_string())
        .unwrap_or_default();
    let _ = fs::remove_dir_all(&dir);
    Some((code, disasm))
}

#[test]
fn e2e_aarch64_forged_noalias_stencil_stays_scalar_and_bit_exact() {
    let module = build_module();

    // -O0: scalar baseline must already match the reference.
    let obj0 = compile_at(&module, OptLevel::O0).expect("O0 must compile");
    if let Some((code, _)) = link_run_disasm("ext_sten_o0", &obj0) {
        assert_eq!(code, 0, "O0 scalar stencil mismatch");
    } else {
        return;
    }

    // -O2: public noalias labels remain report-only, so retain the scalar body.
    let obj2 = compile_at(&module, OptLevel::O2).expect("O2 must compile");
    let Some((code, disasm)) = link_run_disasm("ext_sten_o2", &obj2) else {
        return;
    };

    if !disasm.is_empty() {
        let ext_count = disasm.matches("ext.16b").count();
        let ldp_q_count = disasm
            .lines()
            .filter(|l| l.contains("ldp") && l.contains("q"))
            .count();
        assert_eq!(
            ext_count, 0,
            "label-only noalias must not authorize EXT: {disasm}"
        );
        assert_eq!(
            ldp_q_count, 0,
            "label-only noalias must not authorize vector loads: {disasm}"
        );
        assert!(
            disasm
                .lines()
                .any(|line| line.contains("ldr") && line.contains("w"))
                && disasm
                    .lines()
                    .any(|line| line.contains("str") && line.contains("w")),
            "scalar fallback loads/stores must remain present; disasm:\n{disasm}"
        );
    }

    assert_eq!(code, 0, "O2 scalar fallback mismatch vs scalar reference");
}
