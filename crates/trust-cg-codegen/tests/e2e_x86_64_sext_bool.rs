// trust-cg-codegen/tests/e2e_x86_64_sext_bool.rs - `sext` of a bool on x86-64, linked and run
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! trust-ir's `SExt` of a `Bool` (LLVM's `sext i1`, the LIR `Sextend {
//! from_ty: B1, .. }`) makes `true` all ones: the reference interpreter reads
//! the bool as the 1-bit integer `InterpretInt { bits: 1, .. }` and widens
//! `as_signed()` of it, which is -1. The x86-64 selector lowered the cast as a
//! `movsx` of the bool's 0/1 byte, which is +1, and widened the `I128` low
//! half the same way (`(1, 0)` for `true`), while `Sextend B1 -> I8` was
//! refused. Nothing in Rust spells this cast; LLVM's `xor x, sext(icmp)`
//! (`x < 0 ? ~x : x`, gcc-c-torture pr68376-2) and an `i1` GEP index do.
//!
//! Nine trust-ir functions, each compiled through the AOT `Compiler` at
//! O0..O3 and checked to carry the cast in its LIR:
//!
//! * `tcg_sext_bool_{i8,i16,i32,i64,i128}(b: bool)`: the cast of a parameter
//!   into every integer width;
//! * `tcg_sext_lt_i64(a: i64, b: i64) -> i64`: of a compare, `-(a < b)`;
//! * `tcg_flip_if_negative_i32(x: i32) -> i32`: `x ^ sext(x < 0)`, the
//!   branchless `x < 0 ? !x : x` of pr68376-2;
//! * `tcg_sext_true_{i64,i128}() -> ..`: of the constant `true`, which the
//!   optimizer may fold before the selector sees it.
//!
//! The expected values are the reference interpreter's (checked here for both
//! bool values), and the native leg (an x86-64 host that links and runs
//! x86-64) runs each object from a C driver whose trampoline fills every
//! general-purpose register it does not pass with `0xA5` bytes and sets the
//! bits of each argument register that System V leaves undefined to `0xA5`
//! too: bits 8..63 of a `bool` (bit 0 is its value, bits 1..7 clear) and bits
//! 32..63 of an `i32`. The driver reads only the bits System V defines of the
//! result: AL, AX, EAX, RAX, or RAX and RDX.

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
use trust_ir::{
    BinOp, ICmpOp, InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Ty,
};
use trust_ir_build::ModuleBuilder;

const SEXT_I8: &str = "tcg_sext_bool_i8";
const SEXT_I16: &str = "tcg_sext_bool_i16";
const SEXT_I32: &str = "tcg_sext_bool_i32";
const SEXT_I64: &str = "tcg_sext_bool_i64";
const SEXT_I128: &str = "tcg_sext_bool_i128";
const SEXT_LT_I64: &str = "tcg_sext_lt_i64";
const FLIP_IF_NEGATIVE: &str = "tcg_flip_if_negative_i32";
const SEXT_TRUE_I64: &str = "tcg_sext_true_i64";
const SEXT_TRUE_I128: &str = "tcg_sext_true_i128";
const FUNCTIONS: [&str; 9] = [
    SEXT_I8,
    SEXT_I16,
    SEXT_I32,
    SEXT_I64,
    SEXT_I128,
    SEXT_LT_I64,
    FLIP_IF_NEGATIVE,
    SEXT_TRUE_I64,
    SEXT_TRUE_I128,
];

/// The destination of each parameter fixture's cast.
const PARAMETER_CASTS: [(&str, Ty, Type); 5] = [
    (SEXT_I8, Ty::I8, Type::I8),
    (SEXT_I16, Ty::I16, Type::I16),
    (SEXT_I32, Ty::I32, Type::I32),
    (SEXT_I64, Ty::I64, Type::I64),
    (SEXT_I128, Ty::I128, Type::I128),
];

const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn module() -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("e2e_x86_64_sext_bool");

    // tcg_sext_bool_iN(b) = sext(b)
    for (name, to, _) in PARAMETER_CASTS {
        let ty = builder.add_func_type(vec![Ty::Bool], vec![to.clone()]);
        let mut f = builder.function(name, ty);
        let entry = f.create_block();
        let b = f.add_block_param(entry, Ty::Bool);
        f.switch_to_block(entry);
        let wide = f.sext(Ty::Bool, to, b);
        f.ret(vec![wide]);
        f.build();
    }

    // tcg_sext_lt_i64(a, b) = sext(a < b)
    let ty = builder.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
    let mut f = builder.function(SEXT_LT_I64, ty);
    let entry = f.create_block();
    let a = f.add_block_param(entry, Ty::I64);
    let b = f.add_block_param(entry, Ty::I64);
    f.switch_to_block(entry);
    let less = f.icmp(ICmpOp::Slt, Ty::I64, a, b);
    let mask = f.sext(Ty::Bool, Ty::I64, less);
    f.ret(vec![mask]);
    f.build();

    // tcg_flip_if_negative_i32(x) = x ^ sext(x < 0)
    let ty = builder.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut f = builder.function(FLIP_IF_NEGATIVE, ty);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::I32);
    f.switch_to_block(entry);
    let zero = f.iconst(Ty::I32, 0);
    let negative = f.icmp(ICmpOp::Slt, Ty::I32, x, zero);
    let mask = f.sext(Ty::Bool, Ty::I32, negative);
    let flipped = f.binop(BinOp::Xor, Ty::I32, x, mask);
    f.ret(vec![flipped]);
    f.build();

    // tcg_sext_true_iN() = sext(true)
    for (name, to) in [(SEXT_TRUE_I64, Ty::I64), (SEXT_TRUE_I128, Ty::I128)] {
        let ty = builder.add_func_type(vec![], vec![to.clone()]);
        let mut f = builder.function(name, ty);
        let entry = f.create_block();
        f.switch_to_block(entry);
        let truth = f.bool_const(true);
        let wide = f.sext(Ty::Bool, to, truth);
        f.ret(vec![wide]);
        f.build();
    }

    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// Each fixture reaches the selector with one `Sextend` from `B1`, so the
/// native leg exercises it rather than some other spelling of the cast.
#[test]
fn every_fixture_lowers_its_cast_to_a_bool_sign_extension() {
    let module = module();
    let expected = PARAMETER_CASTS
        .iter()
        .map(|(name, _, to)| (*name, to.clone()))
        .chain([
            (SEXT_LT_I64, Type::I64),
            (FLIP_IF_NEGATIVE, Type::I32),
            (SEXT_TRUE_I64, Type::I64),
            (SEXT_TRUE_I128, Type::I128),
        ]);
    for (name, to_ty) in expected {
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
                    == Opcode::Sextend {
                        from_ty: Type::B1,
                        to_ty: to_ty.clone(),
                    }
            })
            .count();
        assert_eq!(extensions, 1, "{name}: {lir:?}");
    }
}

/// The values the native leg expects are trust-ir's: the reference
/// interpreter widens `false` to 0 and `true` to all ones at every width.
#[test]
fn the_reference_interpreter_sign_extends_true_to_all_ones() {
    let module = module();
    let run = |name: &str, args: Vec<InterpretValue>| -> i128 {
        let function = module.function_by_name(name).expect("fixture");
        let out = Interpreter::with_module(&module)
            .with_options(InterpretOptions {
                fuel: 10_000,
                max_call_depth: 4,
                panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
            })
            .execute_func(function.id, args)
            .unwrap_or_else(|error| panic!("{name}: {error:?}"));
        match &out.returns[0].kind {
            InterpretValueKind::Int(int) => int.as_signed(),
            other => panic!("{name} returned {other:?}"),
        }
    };
    for (name, _, _) in PARAMETER_CASTS {
        assert_eq!(
            run(name, vec![InterpretValue::bool(false)]),
            0,
            "{name}(false)"
        );
        assert_eq!(
            run(name, vec![InterpretValue::bool(true)]),
            -1,
            "{name}(true)"
        );
    }
    let i64v = |v: i64| InterpretValue::int(Ty::I64, i128::from(v)).expect("i64");
    let i32v = |v: i32| InterpretValue::int(Ty::I32, i128::from(v)).expect("i32");
    assert_eq!(run(SEXT_LT_I64, vec![i64v(-1), i64v(0)]), -1);
    assert_eq!(run(SEXT_LT_I64, vec![i64v(0), i64v(-1)]), 0);
    assert_eq!(run(FLIP_IF_NEGATIVE, vec![i32v(-5)]), 4);
    assert_eq!(run(FLIP_IF_NEGATIVE, vec![i32v(5)]), 5);
    assert_eq!(run(SEXT_TRUE_I64, vec![]), -1);
    assert_eq!(run(SEXT_TRUE_I128, vec![]), -1);
}

/// The codegen crate's golden-truth oracle (`trust_cg_codegen::interpreter`,
/// which differential tests compare compiled code against) agrees with the
/// reference interpreter: it returned 1 for `sext(true)`, the same wrong
/// answer the selector computed, so a differential test over it could not
/// have caught the miscompile.
#[test]
fn the_codegen_oracle_sign_extends_true_to_all_ones() {
    use trust_cg_codegen::interpreter::{InterpreterValue, interpret};
    let module = module();
    for (name, _, _) in PARAMETER_CASTS {
        for (value, want) in [(false, 0), (true, -1)] {
            let results = interpret(&module, name, &[InterpreterValue::Bool(value)])
                .unwrap_or_else(|error| panic!("{name}({value}): {error:?}"));
            assert_eq!(results.len(), 1, "{name}({value})");
            assert_eq!(results[0].as_int().ok(), Some(want), "{name}({value})");
        }
    }
    assert_eq!(
        interpret(&module, SEXT_TRUE_I64, &[]).unwrap()[0]
            .as_int()
            .ok(),
        Some(-1)
    );
}

/// `call_dirty(fn, rdi, rsi, out)` calls `fn` with exactly those two argument
/// registers and every other general-purpose register (other than RSP/RBP)
/// filled with `0xA5` bytes, then stores RAX and RDX whole into `out[0]` and
/// `out[1]`. System V: entry RSP is 8 mod 16; `push rbp`, five more pushes and
/// the 8-byte `out` slot align it for the call.
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
    "  movq %rcx, (%rsp)\n"
    "  movq %rdi, %r11\n"
    "  movq %rsi, %rdi\n  movq %rdx, %rsi\n"
    "  movabsq $0xa5a5a5a5a5a5a5a5, %rax\n"
    "  movq %rax, %rbx\n  movq %rax, %rcx\n  movq %rax, %rdx\n  movq %rax, %r8\n"
    "  movq %rax, %r9\n  movq %rax, %r10\n  movq %rax, %r12\n"
    "  movq %rax, %r13\n  movq %rax, %r14\n  movq %rax, %r15\n"
    "  callq *%r11\n"
    "  movq (%rsp), %rcx\n"
    "  movq %rax, (%rcx)\n  movq %rdx, 8(%rcx)\n"
    "  addq $8, %rsp\n"
    "  popq %r15\n  popq %r14\n  popq %r13\n  popq %r12\n  popq %rbx\n"
    "  popq %rbp\n  retq\n");

void call_dirty(void *fn, uint64_t rdi, uint64_t rsi, uint64_t out[2]);

/* Only their addresses are taken; `call_dirty` makes every call. */
extern void tcg_sext_bool_i8(void);
extern void tcg_sext_bool_i16(void);
extern void tcg_sext_bool_i32(void);
extern void tcg_sext_bool_i64(void);
extern void tcg_sext_bool_i128(void);
extern void tcg_sext_lt_i64(void);
extern void tcg_flip_if_negative_i32(void);
extern void tcg_sext_true_i64(void);
extern void tcg_sext_true_i128(void);

/* The bits of a `bool` and of an `i32` argument register that System V
   leaves undefined, which the callee must not read. */
#define ABOVE_BYTE 0xa5a5a5a5a5a5a500ull
#define ABOVE_WORD 0xa5a5a5a500000000ull

static int checks = 0, failures = 0;

static void check(const char *what, uint64_t arg0, uint64_t arg1, int ok, uint64_t rax,
                  uint64_t rdx) {
    checks++;
    if (!ok) {
        printf("%s(0x%llx, 0x%llx): rax=0x%016llx rdx=0x%016llx\n", what,
               (unsigned long long)arg0, (unsigned long long)arg1, (unsigned long long)rax,
               (unsigned long long)rdx);
        failures++;
    }
}

int main(void) {
    static const int64_t words[] = {0, 1, 2, -1, -2, 0x7fffffffffffffffll,
                                    (int64_t)0x8000000000000000ull, 0x100000000ll};
    static const int32_t ints[] = {0, 1, -1, 5, -5, 0x7fffffff, (int32_t)0x80000000u};
    const unsigned nwords = sizeof words / sizeof words[0];
    const unsigned nints = sizeof ints / sizeof ints[0];
    uint64_t out[2];
    for (uint64_t c = 0; c < 2; c++) {
        const int64_t want = c ? -1 : 0;
        const uint64_t arg = ABOVE_BYTE | c;
        call_dirty((void *)tcg_sext_bool_i8, arg, ABOVE_BYTE, out);
        check("sext_bool_i8", c, 0, (int8_t)out[0] == want, out[0], out[1]);
        call_dirty((void *)tcg_sext_bool_i16, arg, ABOVE_BYTE, out);
        check("sext_bool_i16", c, 0, (int16_t)out[0] == want, out[0], out[1]);
        call_dirty((void *)tcg_sext_bool_i32, arg, ABOVE_BYTE, out);
        check("sext_bool_i32", c, 0, (int32_t)out[0] == want, out[0], out[1]);
        call_dirty((void *)tcg_sext_bool_i64, arg, ABOVE_BYTE, out);
        check("sext_bool_i64", c, 0, (int64_t)out[0] == want, out[0], out[1]);
        call_dirty((void *)tcg_sext_bool_i128, arg, ABOVE_BYTE, out);
        check("sext_bool_i128", c, 0, (int64_t)out[0] == want && (int64_t)out[1] == want,
              out[0], out[1]);
    }
    for (unsigned i = 0; i < nwords; i++) {
        for (unsigned j = 0; j < nwords; j++) {
            const int64_t a = words[i], b = words[j];
            call_dirty((void *)tcg_sext_lt_i64, (uint64_t)a, (uint64_t)b, out);
            check("sext_lt_i64", (uint64_t)a, (uint64_t)b, (int64_t)out[0] == (a < b ? -1 : 0),
                  out[0], out[1]);
        }
    }
    for (unsigned i = 0; i < nints; i++) {
        const int32_t x = ints[i];
        call_dirty((void *)tcg_flip_if_negative_i32, ABOVE_WORD | (uint32_t)x, ABOVE_BYTE, out);
        check("flip_if_negative_i32", (uint32_t)x, 0, (int32_t)out[0] == (x < 0 ? ~x : x),
              out[0], out[1]);
    }
    call_dirty((void *)tcg_sext_true_i64, ABOVE_BYTE, ABOVE_BYTE, out);
    check("sext_true_i64", 0, 0, (int64_t)out[0] == -1, out[0], out[1]);
    call_dirty((void *)tcg_sext_true_i128, ABOVE_BYTE, ABOVE_BYTE, out);
    check("sext_true_i128", 0, 0, (int64_t)out[0] == -1 && (int64_t)out[1] == -1, out[0],
          out[1]);
    printf("checks=%d failures=%d\n", checks, failures);
    return failures == 0 ? 0 : 1;
}
"#;

#[test]
fn bool_sign_extensions_run_exactly_with_dirty_argument_registers() {
    let test = "bool_sign_extensions_run_exactly_with_dirty_argument_registers";
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
    let mut wrong = Vec::new();
    for (opt_level, object) in objects {
        let object_path = dir.join(format!("sext_bool_{opt_level:?}.o"));
        fs::write(&object_path, &object).unwrap();
        let binary = dir.join(format!("sext_bool_{opt_level:?}"));
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
        if run.timed_out || !run.output.status.success() || !stdout.contains("failures=0") {
            wrong.push(format!(
                "{opt_level:?} (status {:?}):\n{stdout}",
                run.output.status
            ));
        }
    }
    let _ = fs::remove_dir_all(&dir);
    assert!(
        wrong.is_empty(),
        "a bool's sign extension computed a wrong value at:\n{}",
        wrong.join("\n")
    );
}

/// The host JIT selects through the same x86-64 selector: each function,
/// JIT-compiled at O0..O3 into this process and called through its C ABI,
/// returns 0 for `false` and all ones for `true`.
#[cfg(all(target_arch = "x86_64", unix))]
#[test]
fn bool_sign_extensions_run_exactly_through_the_host_jit() {
    let module = module();
    let mut wrong = Vec::new();
    for opt_level in OPT_LEVELS {
        let mut config = CompilerConfig::for_host_jit_unchecked();
        config.opt_level = opt_level;
        let jit = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &std::collections::HashMap::new())
            .unwrap_or_else(|error| panic!("{opt_level:?}: JIT compile: {error}"));
        let address = |name: &str| {
            jit.buffer
                .get_fn_ptr_bound(name)
                .unwrap_or_else(|| panic!("{opt_level:?}: {name} is not published"))
                .as_ptr()
        };
        // SAFETY: each symbol is a function the module defines with exactly
        // this signature, compiled for the host's System V C ABI, and `jit`
        // outlives every call.
        unsafe {
            let i8_of: extern "C" fn(bool) -> i8 = core::mem::transmute(address(SEXT_I8));
            let i16_of: extern "C" fn(bool) -> i16 = core::mem::transmute(address(SEXT_I16));
            let i32_of: extern "C" fn(bool) -> i32 = core::mem::transmute(address(SEXT_I32));
            let i64_of: extern "C" fn(bool) -> i64 = core::mem::transmute(address(SEXT_I64));
            let i128_of: extern "C" fn(bool) -> u128 = core::mem::transmute(address(SEXT_I128));
            let lt: extern "C" fn(i64, i64) -> i64 = core::mem::transmute(address(SEXT_LT_I64));
            let flip: extern "C" fn(i32) -> i32 = core::mem::transmute(address(FLIP_IF_NEGATIVE));
            let true_i64: extern "C" fn() -> i64 = core::mem::transmute(address(SEXT_TRUE_I64));
            let true_i128: extern "C" fn() -> u128 = core::mem::transmute(address(SEXT_TRUE_I128));
            for b in [false, true] {
                let want = if b { -1 } else { 0 };
                let got = [
                    i64::from(i8_of(b)),
                    i64::from(i16_of(b)),
                    i64::from(i32_of(b)),
                    i64_of(b),
                ];
                if got != [want; 4] || i128_of(b) != if b { u128::MAX } else { 0 } {
                    wrong.push(format!(
                        "{opt_level:?} sext({b}): i8..i64 {got:?}, i128 {:#x}",
                        i128_of(b)
                    ));
                }
            }
            for (a, b) in [(-1i64, 0i64), (0, -1), (i64::MIN, i64::MAX), (5, 5)] {
                if lt(a, b) != if a < b { -1 } else { 0 } {
                    wrong.push(format!("{opt_level:?} sext_lt({a}, {b}) = {}", lt(a, b)));
                }
            }
            for x in [0i32, 1, -1, 5, -5, i32::MAX, i32::MIN] {
                if flip(x) != if x < 0 { !x } else { x } {
                    wrong.push(format!("{opt_level:?} flip({x}) = {}", flip(x)));
                }
            }
            if true_i64() != -1 || true_i128() != u128::MAX {
                wrong.push(format!(
                    "{opt_level:?} sext(true) = {} / {:#x}",
                    true_i64(),
                    true_i128()
                ));
            }
        }
    }
    assert!(
        wrong.is_empty(),
        "the host JIT computed a wrong bool sign extension:\n{}",
        wrong.join("\n")
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or fails by name) because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
