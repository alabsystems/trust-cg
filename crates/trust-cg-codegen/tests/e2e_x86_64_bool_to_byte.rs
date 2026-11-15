// trust-cg-codegen/tests/e2e_x86_64_bool_to_byte.rs - `bool as u8` on x86-64, linked and run
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `bool as u8` is the LIR `Uextend { from_ty: B1, to_ty: I8 }`. The x86-64
//! selector refused it (`unsupported opcode for x86-64 ISel: Uextend {
//! from_ty: B1, to_ty: I8 }`), which failed `core::num::<impl u8>::carrying_add`
//! (`carry as u8`) on the Darwin x86-64 `core` census. It now zero-extends the
//! bool's low byte, as the wider `B1` extensions do.
//!
//! Three trust-ir functions, each compiled through the AOT `Compiler` at
//! O0..O3 and checked to carry the extension in its LIR:
//!
//! * `tcg_bool_as_u8(b: bool) -> u8`: the extension of a parameter;
//! * `tcg_lt_as_u8(a: u64, b: u64) -> u8`: of a compare's result;
//! * `tcg_carrying_add_u8(a: u8, b: u8, c: bool) -> (u8, bool)`: `core`'s
//!   `carrying_add` for `u8`, `(a + b + c as u8, carry out)`.
//!
//! Native leg (an x86-64 host that links and runs x86-64): a C driver's
//! trampoline fills every general-purpose register it does not pass with
//! `0xA5` bytes and sets bits 8..63 of each `u8` and `bool` argument register
//! to `0xA5` too (System V defines only the low byte of a `u8`, and of a
//! `bool` bit 0 with bits 1..7 clear). The returned AL must be the exact byte,
//! and `carrying_add`'s carry lane the backend's clean 32-bit bool in EDX, for
//! both bool values and every pair of the edge bytes.

mod common;

use std::fs;

use common::rosetta::{
    codegen_link_timeout, codegen_run_timeout, command_output_with_timeout,
    run_executable_with_timeout, x86_64_cc, x86_64_link_run_or_skip,
};
use common::x86_64_object::{HOST_IS_MACHO, assert_host_x86_64_object};
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::types::Type;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const BOOL_AS_U8: &str = "tcg_bool_as_u8";
const LT_AS_U8: &str = "tcg_lt_as_u8";
const CARRYING_ADD: &str = "tcg_carrying_add_u8";
const FUNCTIONS: [&str; 3] = [BOOL_AS_U8, LT_AS_U8, CARRYING_ADD];

const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn module() -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("e2e_x86_64_bool_to_byte");

    // tcg_bool_as_u8(b) = b as u8
    let ty = builder.add_func_type(vec![Ty::Bool], vec![Ty::U8]);
    let mut f = builder.function(BOOL_AS_U8, ty);
    let entry = f.create_block();
    let b = f.add_block_param(entry, Ty::Bool);
    f.switch_to_block(entry);
    let byte = f.zext(Ty::Bool, Ty::U8, b);
    f.ret(vec![byte]);
    f.build();

    // tcg_lt_as_u8(a, b) = (a < b) as u8
    let ty = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U8]);
    let mut f = builder.function(LT_AS_U8, ty);
    let entry = f.create_block();
    let a = f.add_block_param(entry, Ty::U64);
    let b = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let less = f.icmp(ICmpOp::Ult, Ty::U64, a, b);
    let byte = f.zext(Ty::Bool, Ty::U8, less);
    f.ret(vec![byte]);
    f.build();

    // tcg_carrying_add_u8(a, b, c), as `core` writes it:
    //   let (s, c1) = a.overflowing_add(b);
    //   let (t, c2) = s.overflowing_add(c as u8);
    //   (t, c1 | c2)
    let ty = builder.add_func_type(vec![Ty::U8, Ty::U8, Ty::Bool], vec![Ty::U8, Ty::Bool]);
    let mut f = builder.function(CARRYING_ADD, ty);
    let entry = f.create_block();
    let a = f.add_block_param(entry, Ty::U8);
    let b = f.add_block_param(entry, Ty::U8);
    let c = f.add_block_param(entry, Ty::Bool);
    f.switch_to_block(entry);
    let s = f.add(Ty::U8, a, b);
    let c1 = f.icmp(ICmpOp::Ult, Ty::U8, s, a);
    let carry_in = f.zext(Ty::Bool, Ty::U8, c);
    let t = f.add(Ty::U8, s, carry_in);
    let c2 = f.icmp(ICmpOp::Ult, Ty::U8, t, s);
    let carry_out = f.binop(BinOp::Or, Ty::Bool, c1, c2);
    f.ret(vec![t, carry_out]);
    f.build();

    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// Each fixture reaches the selector with the `B1 -> I8` extension, so the
/// native leg exercises it rather than some other spelling of the cast.
#[test]
fn every_fixture_lowers_its_cast_to_a_bool_to_byte_extension() {
    let module = module();
    for name in FUNCTIONS {
        let function = module
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap_or_else(|| panic!("missing function {name}"));
        let (lir, _) = trust_cg_lower::translate_function_with_license(
            function,
            &module,
            &permit_unlicensed(),
        )
        .unwrap_or_else(|error| panic!("{name}: the adapter must lower it: {error:?}"));
        let extensions = lir
            .blocks
            .values()
            .flat_map(|block| &block.instructions)
            .filter(|inst| {
                inst.opcode
                    == Opcode::Uextend {
                        from_ty: Type::B1,
                        to_ty: Type::I8,
                    }
            })
            .count();
        assert_eq!(extensions, 1, "{name}: {lir:?}");
    }
}

/// `call_dirty(fn, rdi, rsi, rdx, out)` calls `fn` with exactly those three
/// argument registers and every other general-purpose register (other than
/// RSP/RBP) filled with `0xA5` bytes, then stores RAX and RDX whole into
/// `out[0]` and `out[1]`. System V: entry RSP is 8 mod 16; `push rbp`, five
/// more pushes and the 8-byte `out` slot align it for the call.
const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>

#if defined(__APPLE__)
#define SYM(name) "_" #name
#else
#define SYM(name) #name
#endif

__asm__(
    ".text\n"
    ".globl " SYM(call_dirty) "\n"
    SYM(call_dirty) ":\n"
    "  pushq %rbp\n  movq %rsp, %rbp\n"
    "  pushq %rbx\n  pushq %r12\n  pushq %r13\n  pushq %r14\n  pushq %r15\n"
    "  subq $8, %rsp\n"
    "  movq %r8, (%rsp)\n"
    "  movq %rdi, %r11\n"
    "  movq %rsi, %rdi\n  movq %rdx, %rsi\n  movq %rcx, %rdx\n"
    "  movabsq $0xa5a5a5a5a5a5a5a5, %rax\n"
    "  movq %rax, %rbx\n  movq %rax, %rcx\n  movq %rax, %r8\n"
    "  movq %rax, %r9\n  movq %rax, %r10\n  movq %rax, %r12\n"
    "  movq %rax, %r13\n  movq %rax, %r14\n  movq %rax, %r15\n"
    "  callq *%r11\n"
    "  movq (%rsp), %rcx\n"
    "  movq %rax, (%rcx)\n  movq %rdx, 8(%rcx)\n"
    "  addq $8, %rsp\n"
    "  popq %r15\n  popq %r14\n  popq %r13\n  popq %r12\n  popq %rbx\n"
    "  popq %rbp\n  retq\n");

void call_dirty(void *fn, uint64_t rdi, uint64_t rsi, uint64_t rdx, uint64_t out[2]);

/* Only their addresses are taken; `call_dirty` makes every call. */
extern void tcg_bool_as_u8(void);
extern void tcg_lt_as_u8(void);
extern void tcg_carrying_add_u8(void);

/* Bits 8..63 of a `u8` or `bool` argument register, which the callee must
   not read. */
#define ABOVE_BYTE 0xa5a5a5a5a5a5a500ull

int main(void) {
    static const uint64_t bytes[] = {0, 1, 2, 0x7f, 0x80, 0xfe, 0xff};
    static const uint64_t words[] = {0, 1, 2, 0xff, 0x100, 0x7fffffffffffffffull,
                                     0x8000000000000000ull, 0xffffffffffffffffull};
    const unsigned nbytes = sizeof bytes / sizeof bytes[0];
    const unsigned nwords = sizeof words / sizeof words[0];
    uint64_t out[2];
    int checks = 0, failures = 0;
    for (uint64_t c = 0; c < 2; c++) {
        call_dirty((void *)tcg_bool_as_u8, ABOVE_BYTE | c, ABOVE_BYTE, ABOVE_BYTE, out);
        checks++;
        if ((uint8_t)out[0] != c) {
            printf("bool_as_u8(%llu): al=0x%02x\n", (unsigned long long)c, (uint8_t)out[0]);
            failures++;
        }
        for (unsigned i = 0; i < nbytes; i++) {
            for (unsigned j = 0; j < nbytes; j++) {
                uint64_t a = bytes[i], b = bytes[j];
                uint64_t sum = a + b + c;
                call_dirty((void *)tcg_carrying_add_u8, ABOVE_BYTE | a, ABOVE_BYTE | b,
                           ABOVE_BYTE | c, out);
                checks++;
                if ((uint8_t)out[0] != (uint8_t)sum || (uint32_t)out[1] != (sum > 0xff)) {
                    printf("carrying_add_u8(0x%02llx, 0x%02llx, %llu): al=0x%02x edx=0x%08x, "
                           "want 0x%02x and %d\n",
                           (unsigned long long)a, (unsigned long long)b, (unsigned long long)c,
                           (uint8_t)out[0], (uint32_t)out[1], (uint8_t)sum, sum > 0xff);
                    failures++;
                }
            }
        }
    }
    for (unsigned i = 0; i < nwords; i++) {
        for (unsigned j = 0; j < nwords; j++) {
            uint64_t a = words[i], b = words[j];
            call_dirty((void *)tcg_lt_as_u8, a, b, ABOVE_BYTE, out);
            checks++;
            if ((uint8_t)out[0] != (a < b)) {
                printf("lt_as_u8(0x%llx, 0x%llx): al=0x%02x\n", (unsigned long long)a,
                       (unsigned long long)b, (uint8_t)out[0]);
                failures++;
            }
        }
    }
    printf("checks=%d failures=%d\n", checks, failures);
    return failures == 0 ? 0 : 1;
}
"#;

#[test]
fn bool_to_byte_extensions_run_exactly_with_dirty_argument_registers() {
    let test = "bool_to_byte_extensions_run_exactly_with_dirty_argument_registers";
    let triple = if HOST_IS_MACHO {
        "x86_64-apple-darwin"
    } else {
        "x86_64-unknown-linux-gnu"
    };
    let spec = TargetSpec::parse(triple).expect("x86-64 triple");
    let module = module();
    let mut objects = Vec::new();
    for opt_level in OPT_LEVELS {
        let compiler = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level,
                emit_proofs: false,
                parallel: false,
                ..CompilerConfig::default()
            },
            spec,
        )
        .with_codegen_license(permit_unlicensed());
        let result = compiler
            .compile(&module)
            .unwrap_or_else(|error| panic!("{opt_level:?}: compile: {error}"));
        assert_host_x86_64_object(
            &format!("{test} {opt_level:?}"),
            &result.object_code,
            &FUNCTIONS,
            &[],
        );
        objects.push((opt_level, result.object_code));
    }
    if !x86_64_link_run_or_skip(test, "x86-64 link/run leg") {
        return;
    }
    let dir = std::env::temp_dir().join(format!("trust_cg_{test}_{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let driver = dir.join("driver.c");
    fs::write(&driver, DRIVER).unwrap();
    for (opt_level, object) in objects {
        let object_path = dir.join(format!("bool_to_byte_{opt_level:?}.o"));
        fs::write(&object_path, &object).unwrap();
        let binary = dir.join(format!("bool_to_byte_{opt_level:?}"));
        let mut link = x86_64_cc();
        link.arg("-o").arg(&binary).arg(&driver).arg(&object_path);
        let linked = command_output_with_timeout(&mut link, codegen_link_timeout()).unwrap();
        assert!(
            !linked.timed_out && linked.output.status.success(),
            "{opt_level:?}: link failed: {}",
            String::from_utf8_lossy(&linked.output.stderr)
        );
        let run = run_executable_with_timeout(&binary, codegen_run_timeout()).unwrap();
        let stdout = String::from_utf8_lossy(&run.output.stdout).into_owned();
        eprintln!("[{test}] {opt_level:?}: {}", stdout.trim_end());
        assert!(
            !run.timed_out && run.output.status.success() && stdout.contains("failures=0"),
            "{opt_level:?}: a bool widened to a byte computed a wrong value (status {:?}):\n\
             {stdout}",
            run.output.status
        );
    }
    let _ = fs::remove_dir_all(&dir);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or fails by name) because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
