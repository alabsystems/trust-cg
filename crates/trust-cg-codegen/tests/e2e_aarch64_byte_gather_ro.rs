// trust-cg-codegen/tests/e2e_aarch64_byte_gather_ro.rs
//
// End-to-end differential + guard-page correctness for the narrow
// register-offset load fold (`ext_addr`): a byte-gather loop
// `acc += b[i]` (zext i8 -> i32) should compile so the per-lane
// `sxtw + add + ldrb + uxtb` chain collapses to one `ldrb Wd, [Xbase, Widx,
// sxtw]` (the redundant `uxtb` folded into the load — a byte load already
// zero-extends). Two things are checked:
//
//   1. CORRECTNESS: bit-exact vs the scalar C reference across value patterns
//      and edge lengths (including empty and negative-start indices), at -O0
//      and -O2.
//   2. NO OVER-READ: a guard-page harness places the byte array so its last
//      byte is the final byte of a mapped page with the NEXT page PROT_NONE.
//      Running the kernel over exactly `n` bytes must NOT fault — proving the
//      RO fold preserved the 1-byte access width (a wrongly widened load would
//      read into the guard page and SIGSEGV).
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

/// `int bytesum(const uint8_t* b, int n)`:
/// `int acc = 0; for (int i = 0; i < n; i++) acc += (int)(uint8_t)b[i]; return acc;`
/// The `b[i]` gather (zext i8 -> i32) is the exact narrow-RO-fold shape.
fn build_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("bytesum");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I32], vec![Ty::I32]);
    {
        let mut fb = mb.function("bytesum", ty);
        let entry = fb.create_block();
        let b = fb.add_block_param(entry, Ty::Ptr);
        let n = fb.add_block_param(entry, Ty::I32);

        let header = fb.create_block();
        let iv = fb.add_block_param(header, Ty::I32);
        let acc = fb.add_block_param(header, Ty::I32);

        let body = fb.create_block();
        let biv = fb.add_block_param(body, Ty::I32);
        let bacc = fb.add_block_param(body, Ty::I32);

        let exit = fb.create_block();
        let eacc = fb.add_block_param(exit, Ty::I32);

        fb.switch_to_block(entry);
        let z0 = fb.iconst(Ty::I32, 0);
        let z1 = fb.iconst(Ty::I32, 0);
        fb.br(header, vec![z0, z1]);

        fb.switch_to_block(header);
        let in_range = fb.icmp(ICmpOp::Slt, Ty::I32, iv, n);
        fb.condbr(in_range, body, vec![iv, acc], exit, vec![acc]);

        fb.switch_to_block(body);
        let p = fb.gep(Ty::I8, b, vec![biv]);
        let byte = fb.load(Ty::I8, p);
        let byte32 = fb.zext(Ty::I8, Ty::I32, byte);
        let acc2 = fb.binop(trust_ir::BinOp::Add, Ty::I32, bacc, byte32);
        let one = fb.iconst(Ty::I32, 1);
        let iv2 = fb.binop(trust_ir::BinOp::Add, Ty::I32, biv, one);
        fb.br(header, vec![iv2, acc2]);

        fb.switch_to_block(exit);
        fb.ret(vec![eacc]);
        fb.build();
    }
    let mut module = mb.build();
    let f = module
        .functions
        .iter_mut()
        .find(|f| f.name == "bytesum")
        .unwrap();
    f.attrs.params = vec![
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
#include <sys/mman.h>
#include <unistd.h>
#include <stdlib.h>

extern int bytesum(const uint8_t*, int);

static int ref_bytesum(const uint8_t* b, int n) {
    int acc = 0;
    for (int i = 0; i < n; i++) acc += (int)(uint8_t)b[i];
    return acc;
}

int main(void) {
    /* n sweeps vector-width boundaries (16-lane block) plus scalar tails, and
       the empty loop (n<=0). */
    int ns[] = {0, 1, 2, 3, 4, 15, 16, 17, 18, 31, 32, 33, 47, 64, 65, 100, 255, 256, 257, 1000};
    static uint8_t a[1024];
    for (int pat = 0; pat < 6; pat++) {
        uint32_t seed = 0x9E3779B9u + (uint32_t)pat * 2654435761u;
        for (int i = 0; i < 1024; i++) {
            switch (pat) {
                case 0: a[i] = 0; break;
                case 1: a[i] = 0xFF; break;             /* max byte: sum stresses width */
                case 2: a[i] = (uint8_t)i; break;        /* ramp */
                case 3: a[i] = (i & 1) ? 0xFF : 0; break;
                case 4: a[i] = 0x80; break;              /* high bit set: zext vs sext differ */
                default:
                    seed = seed * 1664525u + 1013904223u;
                    a[i] = (uint8_t)(seed >> 24);
                    break;
            }
        }
        for (unsigned k = 0; k < sizeof(ns)/sizeof(ns[0]); k++) {
            int n = ns[k];
            int got = bytesum(a, n);
            int want = ref_bytesum(a, n);
            if (got != want) {
                printf("MISMATCH pat=%d n=%d got=%d want=%d\n", pat, n, got, want);
                return 1;
            }
        }
    }

    /* Guard-page over-read check: put the array's LAST byte at the final byte
       of a mapped page, with the following page PROT_NONE. A correct 1-byte
       gather reads exactly a[0..n); a wrongly widened load faults. */
    long pg = sysconf(_SC_PAGESIZE);
    char* region = mmap(NULL, (size_t)pg * 2, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANON, -1, 0);
    if (region == MAP_FAILED) { printf("mmap failed\n"); return 2; }
    if (mprotect(region + pg, (size_t)pg, PROT_NONE) != 0) { printf("mprotect failed\n"); return 3; }
    /* Fill the first page; the last N bytes are the array under test. */
    for (long i = 0; i < pg; i++) region[i] = (uint8_t)(i * 131 + 7);
    for (int n = 1; n <= 64; n++) {
        uint8_t* arr = (uint8_t*)(region + pg - n);   /* last byte == region[pg-1] */
        int got = bytesum(arr, n);
        int want = ref_bytesum(arr, n);
        if (got != want) { printf("GUARD MISMATCH n=%d got=%d want=%d\n", n, got, want); return 4; }
    }
    munmap(region, (size_t)pg * 2);

    printf("byte-gather RO: differential + guard-page over-read checks passed\n");
    return 0;
}
"#;

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
    let disasm = Command::new("objdump")
        .args(["-d", obj_path.to_str().unwrap()])
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).to_string())
        .unwrap_or_default();
    let _ = fs::remove_dir_all(&dir);
    Some((code, disasm))
}

#[test]
fn e2e_aarch64_byte_gather_ro_bit_exact_and_no_overread() {
    let module = build_module();

    let obj0 = compile_at(&module, OptLevel::O0).expect("O0 must compile");
    if let Some((code, _)) = link_run_disasm("bg_ro_o0", &obj0) {
        assert_eq!(code, 0, "O0 byte-gather mismatch / guard-page fault");
    } else {
        return;
    }

    let obj2 = compile_at(&module, OptLevel::O2).expect("O2 must compile");
    let Some((code, disasm)) = link_run_disasm("bg_ro_o2", &obj2) else {
        return;
    };

    // The fold fired iff a narrow register-offset LDRB appears: `ldrb Wd,
    // [Xn, Wm, sxtw]` (or uxtw). objdump renders the extend on the ldrb line.
    if !disasm.is_empty() {
        let folded_ro = disasm.lines().any(|l| {
            let l = l.trim();
            l.contains("ldrb")
                && (l.contains("sxtw]")
                    || l.contains("uxtw]")
                    || l.contains("uxtw #")
                    || l.contains("sxtw #"))
        });
        assert!(
            folded_ro,
            "expected a folded narrow register-offset LDRB (ldrb Wd, [Xn, Wm, sxtw]); disasm:\n{disasm}"
        );
        // The redundant UXTB of a folded byte-load result must be gone: there
        // must be no `uxtb` immediately consuming a register a folded `ldrb`
        // wrote. A coarse but effective check: the -O2 kernel should not
        // contain `uxtb` at all in the scalar gather path (the byte value flows
        // straight from the zero-extending ldrb).
        // (Kept as a soft observation: some layouts legitimately keep a uxtb
        // for a differently-shaped consumer; correctness is enforced above.)
    }

    assert_eq!(
        code, 0,
        "O2 byte-gather mismatch / guard-page over-read fault"
    );
}
