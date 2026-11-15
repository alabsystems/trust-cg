// trust-cg-codegen/tests/e2e_aarch64_udot_popcount.rs
//
// End-to-end differential for the popcount-reduction UDOT fast path:
// `for i in 0..n: s += ctpop(a[i])` compiled at -O2 vectorizes via
// CNT.16B + the ACCUMULATING `UDOT.4S` (`UDOT(acc, cnt, ones)`, FEAT_DotProd).
//
// UDOT's Vd is BOTH source and destination (a tied def-use, see
// has_tied_def_use in trust-cg-opt/effects.rs): the running vector accumulator
// must SURVIVE register allocation, scheduling, DCE and coalescing across the
// op. If any of those treated operand 0 as a plain def — the historical
// "op0 is def" P0 class — the accumulator register would be considered dead
// before the UDOT (its MOVI-zero initializer dropped, or its register reused
// mid-loop) and the running sum silently corrupted. This test PINS the
// preservation end-to-end: it runs the full pipeline (regalloc included),
// asserts the linked binary actually CONTAINS a `udot` (so the check is not
// vacuous), and diffs the results bit-exactly against __builtin_popcount over
// edge patterns — including 0x80-heavy bytes, where a UDOT->SDOT confusion
// (sign-extension) diverges.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{AArch64IsaProfile, TargetSpec};

use trust_ir::{ICmpOp, Ty, UnOp};
use trust_ir_build::ModuleBuilder;

#[path = "common/native_host.rs"]
mod native_host;

/// AArch64 Linux GNU (ELF) or macOS (Mach-O) can link and run the objects.
fn can_link_and_run_aarch64_native() -> bool {
    native_host::NATIVE
}

/// UDOT (vector, by element size S): `0 Q 1 01110 10 0 Rm 100101 Rn Rd`.
fn is_udot_4s(word: u32) -> bool {
    word & 0xbfe0_fc00 == 0x2e80_9400
}

/// Darwin's AOT target contract admits FEAT_DotProd, so the production
/// `Compiler` lane runs there. Generic Linux AOT does not admit it and keeps
/// the non-UDOT lowering (pinned below), so every native host also runs the
/// explicit-DotProd pipeline lane, the only UDOT lane on Linux GNU. A host CPU
/// without DotProd is a failure, never a skip.
fn lanes() -> Vec<&'static str> {
    let mut lanes = Vec::new();
    if !native_host::LINUX_GNU {
        lanes.push("darwin-aot");
    }
    if native_host::NATIVE {
        assert!(
            AArch64IsaProfile::DOTPROD.is_supported_by_host(),
            "the explicit DotProd native lane requires host DotProd"
        );
        lanes.push("explicit-dotprod");
    }
    lanes
}

fn compile_lane(lane: &str, module: &trust_ir::Module, opt: OptLevel) -> Result<Vec<u8>, String> {
    match lane {
        "darwin-aot" => compile_at(module, opt),
        "explicit-dotprod" => {
            native_host::compile_with_isa_profile(module, opt, AArch64IsaProfile::DOTPROD)
        }
        _ => unreachable!("unknown lane {lane}"),
    }
}

/// `kernel(ptr a, i32 n) -> i32`: `s = 0; for i in 0..n: s += ctpop(a[i])` —
/// the exact loop shape the NEON array-reduction pass recognizes (the `ctpop`
/// expands to the width-32 SWAR tree in isel, which the pass folds to
/// CNT + UDOT at -O2).
fn build_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("udot_popcount");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I32], vec![Ty::I32]);
    {
        let mut fb = mb.function("kernel", ty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::Ptr);
        let n = fb.add_block_param(entry, Ty::I32);

        let header = fb.create_block();
        let iv = fb.add_block_param(header, Ty::I32);
        let acc = fb.add_block_param(header, Ty::I32);

        let body = fb.create_block();
        let biv = fb.add_block_param(body, Ty::I32);
        let bacc = fb.add_block_param(body, Ty::I32);

        let exit = fb.create_block();
        let result = fb.add_block_param(exit, Ty::I32);

        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::I32, 0);
        fb.br(header, vec![zero, zero]);

        fb.switch_to_block(header);
        let in_range = fb.icmp(ICmpOp::Slt, Ty::I32, iv, n);
        fb.condbr(in_range, body, vec![iv, acc], exit, vec![acc]);

        fb.switch_to_block(body);
        let one = fb.iconst(Ty::I32, 1);
        let ptr = fb.gep(Ty::I32, a, vec![biv]);
        let x = fb.load(Ty::I32, ptr);
        let c = fb.unop(UnOp::CtPop, Ty::I32, x);
        let acc2 = fb.binop(trust_ir::BinOp::Add, Ty::I32, bacc, c);
        let iv2 = fb.binop(trust_ir::BinOp::Add, Ty::I32, biv, one);
        fb.br(header, vec![iv2, acc2]);

        fb.switch_to_block(exit);
        fb.ret(vec![result]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn compile_at(module: &trust_ir::Module, opt: OptLevel) -> Result<Vec<u8>, String> {
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
extern int32_t kernel(uint32_t*, int32_t);

static uint32_t ref_sum(const uint32_t* a, int n) {
    uint32_t s = 0;
    for (int i = 0; i < n; i++) s += (uint32_t)__builtin_popcount(a[i]);
    return s;
}

int main(void) {
    // n sweeps the vector-width boundaries (block = 16 lanes) plus scalar tails.
    int ns[] = {0, 1, 3, 4, 7, 8, 15, 16, 17, 31, 32, 33, 100, 1000};
    static uint32_t buf[1000];
    for (int pat = 0; pat < 6; pat++) {
        for (unsigned k = 0; k < sizeof(ns) / sizeof(ns[0]); k++) {
            int n = ns[k];
            uint32_t seed = 0x12345678u + (uint32_t)pat * 2654435761u;
            for (int i = 0; i < n; i++) {
                switch (pat) {
                    case 0: buf[i] = 0u; break;                     /* popcount 0  */
                    case 1: buf[i] = 0xFFFFFFFFu; break;            /* popcount 32 */
                    /* every byte >= 0x80: a UDOT-as-SDOT confusion sign-extends
                       these bytes and diverges — the SDOT-sensitive pattern */
                    case 2: buf[i] = 0x80808080u; break;
                    case 3: buf[i] = 0xDEADBEEFu; break;
                    case 4: buf[i] = (i & 1) ? 0xAAAAAAAAu : 0x55555555u; break;
                    default:
                        seed = seed * 1664525u + 1013904223u;
                        buf[i] = seed;
                        break;
                }
            }
            uint32_t want = ref_sum(buf, n);
            uint32_t got = (uint32_t)kernel(buf, n);
            if (got != want) {
                printf("MISMATCH pat=%d n=%d got=%u want=%u\n", pat, n, got, want);
                return 1;
            }
        }
    }
    printf("udot popcount: all differential checks passed\n");
    return 0;
}
"#;

/// Link `obj` against the driver, run it, and return (exit_code, disassembly).
fn link_run_disasm(tag: &str, obj: &[u8]) -> Option<(i32, String)> {
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
fn e2e_aarch64_udot_popcount_accumulator_preserved() {
    let module = build_module();
    let lanes = lanes();
    if lanes.is_empty() {
        eprintln!("SKIP: needs an AArch64 Linux GNU or macOS host");
        return;
    }
    for lane in lanes {
        // -O0: scalar SWAR baseline must already match the reference.
        let obj0 = compile_lane(lane, &module, OptLevel::O0)
            .unwrap_or_else(|error| panic!("{lane} O0 must compile: {error}"));
        if let Some((code, _)) = link_run_disasm(&format!("udot_pc_o0_{lane}"), &obj0) {
            assert_eq!(code, 0, "{lane} O0 scalar popcount reduction mismatch");
        } else {
            return;
        }

        // -O2: the NEON popcount fold with the accumulating UDOT.
        let obj2 = compile_lane(lane, &module, OptLevel::O2)
            .unwrap_or_else(|error| panic!("{lane} O2 must compile: {error}"));
        // Independent of any disassembler: the object's code carries UDOT.
        assert!(
            native_host::text_words(&obj2).into_iter().any(is_udot_4s),
            "{lane}: expected the accumulating UDOT in the -O2 kernel words"
        );
        let Some((code, disasm)) = link_run_disasm(&format!("udot_pc_o2_{lane}"), &obj2) else {
            return;
        };

        // The differential is only meaningful if the UDOT path actually fired.
        if !disasm.is_empty() {
            assert!(
                disasm.contains("udot"),
                "{lane}: expected the accumulating UDOT in the -O2 kernel body; disasm:\n{disasm}"
            );
            assert!(
                !disasm.contains("uaddlp"),
                "{lane}: term-root ctpop must take the UDOT fast path, not the UADDLP chain"
            );
        }

        // Bit-exact vs __builtin_popcount across edge patterns (incl. the
        // SDOT-sensitive 0x80-heavy bytes) and vector/tail boundaries. A regalloc /
        // DCE / scheduling violation of the UDOT's tied accumulator (operand 0
        // def-use) corrupts the running sum and fails here.
        assert_eq!(
            code, 0,
            "{lane} O2 UDOT popcount reduction mismatch vs reference"
        );
    }
}

/// Generic Linux AOT does not admit FEAT_DotProd: it must compile the same
/// kernel without any UDOT word. Object-level, so it runs on every host.
#[test]
fn generic_linux_aot_never_emits_udot() {
    let object = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O2,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&build_module())
    .expect("generic Linux AOT keeps the non-UDOT popcount lowering")
    .object_code;
    native_host::assert_elf_aarch64_object(&object);
    assert!(
        !native_host::text_words(&object).into_iter().any(is_udot_4s),
        "generic Linux AOT emitted UDOT without FEAT_DotProd admission"
    );
}

/// The Linux GNU explicit-DotProd lane's object, checked at object level on
/// every host: it compiles for the generic Linux triple and carries UDOT.
#[test]
fn explicit_dotprod_linux_object_carries_udot() {
    let object = native_host::compile_with_isa_profile_for(
        "aarch64-unknown-linux-gnu",
        &build_module(),
        OptLevel::O2,
        AArch64IsaProfile::DOTPROD,
    )
    .expect("explicit DotProd Linux object");
    native_host::assert_elf_aarch64_object(&object);
    assert!(native_host::text_words(&object).into_iter().any(is_udot_4s));
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
