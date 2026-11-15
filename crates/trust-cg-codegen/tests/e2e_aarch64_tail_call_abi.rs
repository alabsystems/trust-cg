// Copyright 2026 Andrew Yates | Apache-2.0
//! Native sibling tail calls from Trust Codegen into clang-compiled callees.
//!
//! Sibling tail-call eligibility reads the call's classified ABI facts
//! (`MachFunction::call_abi_facts`): stack-argument bytes and stores, the
//! hidden result pointer and the callee-saved set. These controls compile Trust
//! IR callers through the production `Compiler` for the host triple
//! (DarwinPCS on macOS, AAPCS64 on Linux GNU), decode the emitted code with an
//! independent object parser, and link each object with a C driver built by
//! the host `cc -O2`:
//!
//! * `stack`: after a non-tail call that keeps nine values live in
//!   callee-saved registers, a tail call passing two stack arguments that fit
//!   the caller's own 16-byte incoming area becomes a `B` at O2/O3;
//! * `regs`: the same pressure with a register-only callee becomes a `B`;
//! * `narrow`: `i8`/`i16`/`i32` stack arguments, packed on Darwin and in
//!   eight-byte slots on Linux, are redirected store-for-store;
//! * `swap`/`dup`: the caller forwards its own two incoming stack arguments
//!   swapped or duplicated, so the redirected stores overwrite slots the
//!   arguments are read from;
//! * refusal controls: a callee needing more stack bytes than the caller
//!   received keeps its `BL`, and an indirect call keeps its `BLR`.
//!
//! O0/O1 run no tail-call pass and must keep every `BL`. Every level must
//! return the C reference value, and the driver keeps ten values live across
//! each call so a callee-saved register the tail path failed to restore
//! changes its checksum.

#[path = "common/native_host.rs"]
mod host;
#[path = "common/aarch64_native.rs"]
mod native;

use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{BinOp, Module, Ty};
use trust_ir_build::ModuleBuilder;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// Unconditional `B` / `BL` with a zero immediate: a branch to a relocated
/// external symbol (the relocation carries the target).
const EXTERNAL_B: u32 = 0x1400_0000;
const EXTERNAL_BL: u32 = 0x9400_0000;

#[derive(Debug, Default, PartialEq, Eq)]
struct Branches {
    external_b: usize,
    external_bl: usize,
    blr: usize,
}

fn branches(object: &[u8]) -> Branches {
    let mut counts = Branches::default();
    for word in host::text_words(object) {
        if word == EXTERNAL_B {
            counts.external_b += 1;
        } else if word == EXTERNAL_BL {
            counts.external_bl += 1;
        } else if word & 0xFFFF_FC1F == 0xD63F_0000 {
            counts.blr += 1;
        }
    }
    counts
}

fn tail_pass_runs(level: OptLevel) -> bool {
    matches!(level, OptLevel::O2 | OptLevel::O3)
}

/// `i64 tcg_tc_stack(a0..a7, s0, s1)`: `t = clang_tc_helper(a0)`, then
/// `return clang_tc_callee10(a0 + t, a1 + t, a2..a7, s0 ^ t, s1 - t)`.
fn stack_module() -> Module {
    let mut mb = ModuleBuilder::new("tcg_tc_stack");
    let helper_ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let ten = mb.add_func_type(vec![Ty::I64; 10], vec![Ty::I64]);
    let helper = mb.declare_function("clang_tc_helper", helper_ty);
    let callee = mb.declare_function("clang_tc_callee10", ten);
    let mut fb = mb.function("tcg_tc_stack", ten);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let params: Vec<_> = (0..10)
        .map(|_| fb.add_block_param(entry, Ty::I64))
        .collect();
    let t = fb.call(helper, vec![params[0]]);
    let a0 = fb.binop(BinOp::Add, Ty::I64, params[0], t);
    let a1 = fb.binop(BinOp::Add, Ty::I64, params[1], t);
    let s0 = fb.binop(BinOp::Xor, Ty::I64, params[8], t);
    let s1 = fb.binop(BinOp::Sub, Ty::I64, params[9], t);
    let mut args = vec![a0, a1];
    args.extend_from_slice(&params[2..8]);
    args.extend([s0, s1]);
    let result = fb.call(callee, args);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `i64 tcg_tc_regs(a0..a7)`: `t = clang_tc_helper(a0)`, then
/// `return clang_tc_callee8(a0 + t, a1..a6, a7 - t)`.
fn regs_module() -> Module {
    let mut mb = ModuleBuilder::new("tcg_tc_regs");
    let helper_ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let eight = mb.add_func_type(vec![Ty::I64; 8], vec![Ty::I64]);
    let helper = mb.declare_function("clang_tc_helper", helper_ty);
    let callee = mb.declare_function("clang_tc_callee8", eight);
    let mut fb = mb.function("tcg_tc_regs", eight);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let params: Vec<_> = (0..8).map(|_| fb.add_block_param(entry, Ty::I64)).collect();
    let t = fb.call(helper, vec![params[0]]);
    let a0 = fb.binop(BinOp::Add, Ty::I64, params[0], t);
    let a7 = fb.binop(BinOp::Sub, Ty::I64, params[7], t);
    let mut args = vec![a0];
    args.extend_from_slice(&params[1..7]);
    args.push(a7);
    let result = fb.call(callee, args);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `i64 tcg_tc_narrow(a0..a7, i8 b, i16 c, i32 d)` returning
/// `clang_tc_narrow(a0..a7, b + 1, c - 3, d * 2)`.
fn narrow_module() -> Module {
    let mut mb = ModuleBuilder::new("tcg_tc_narrow");
    let mut params = vec![Ty::I64; 8];
    params.extend([Ty::I8, Ty::I16, Ty::I32]);
    let ty = mb.add_func_type(params.clone(), vec![Ty::I64]);
    let callee = mb.declare_function("clang_tc_narrow", ty);
    let mut fb = mb.function("tcg_tc_narrow", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let values: Vec<_> = params
        .iter()
        .map(|ty| fb.add_block_param(entry, ty.clone()))
        .collect();
    let one = fb.iconst(Ty::I8, 1);
    let three = fb.iconst(Ty::I16, 3);
    let two = fb.iconst(Ty::I32, 2);
    let b = fb.binop(BinOp::Add, Ty::I8, values[8], one);
    let c = fb.binop(BinOp::Sub, Ty::I16, values[9], three);
    let d = fb.binop(BinOp::Mul, Ty::I32, values[10], two);
    let mut args = values[..8].to_vec();
    args.extend([b, c, d]);
    let result = fb.call(callee, args);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `i64 <name>(a0..a7, s0, s1)` returning
/// `clang_tc_callee10(a0..a7, s[first], s[second])`: the caller forwards its
/// own two incoming stack arguments, reordered or duplicated. The redirected
/// stores write the incoming slots those arguments are read from, so every
/// incoming load must stay ahead of every redirected store.
fn forwarded_stack_module(name: &str, first: usize, second: usize) -> Module {
    let mut mb = ModuleBuilder::new(name);
    let ten = mb.add_func_type(vec![Ty::I64; 10], vec![Ty::I64]);
    let callee = mb.declare_function("clang_tc_callee10", ten);
    let mut fb = mb.function(name, ten);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let params: Vec<_> = (0..10)
        .map(|_| fb.add_block_param(entry, Ty::I64))
        .collect();
    let mut args = params[..8].to_vec();
    args.extend([params[8 + first], params[8 + second]]);
    let result = fb.call(callee, args);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `i64 tcg_tc_overflow(a0..a7, s0)`: its 8-byte incoming area cannot hold
/// the 16 stack bytes `clang_tc_callee10(a0..a7, s0, s0 + 1)` needs.
fn overflow_module() -> Module {
    let mut mb = ModuleBuilder::new("tcg_tc_overflow");
    let nine = mb.add_func_type(vec![Ty::I64; 9], vec![Ty::I64]);
    let ten = mb.add_func_type(vec![Ty::I64; 10], vec![Ty::I64]);
    let callee = mb.declare_function("clang_tc_callee10", ten);
    let mut fb = mb.function("tcg_tc_overflow", nine);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let params: Vec<_> = (0..9).map(|_| fb.add_block_param(entry, Ty::I64)).collect();
    let one = fb.iconst(Ty::I64, 1);
    let s1 = fb.binop(BinOp::Add, Ty::I64, params[8], one);
    let mut args = params.clone();
    args.push(s1);
    let result = fb.call(callee, args);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `i64 tcg_tc_indirect(i64 (*f)(i64), i64 x)` returning `f(x)`.
fn indirect_module() -> Module {
    let mut mb = ModuleBuilder::new("tcg_tc_indirect");
    let helper_ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("tcg_tc_indirect", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let f = fb.add_block_param(entry, Ty::Ptr);
    let x = fb.add_block_param(entry, Ty::I64);
    let result = fb.call_indirect(f, helper_ty, vec![x]);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

const C_PRELUDE: &str = r#"
#include <stdint.h>
#include <stdio.h>
__attribute__((noinline)) int64_t clang_tc_helper(int64_t x) { return x * 3 - 7; }
__attribute__((noinline)) int64_t clang_tc_callee10(int64_t a0, int64_t a1, int64_t a2,
    int64_t a3, int64_t a4, int64_t a5, int64_t a6, int64_t a7, int64_t s0, int64_t s1) {
    return a0 * 1 + a1 * 3 + a2 * 5 + a3 * 7 + a4 * 11 + a5 * 13 + a6 * 17 + a7 * 19
        + s0 * 23 + s1 * 29;
}
__attribute__((noinline)) int64_t clang_tc_callee8(int64_t a0, int64_t a1, int64_t a2,
    int64_t a3, int64_t a4, int64_t a5, int64_t a6, int64_t a7) {
    return a0 * 2 - a1 * 3 + a2 * 5 - a3 * 7 + a4 * 11 - a5 * 13 + a6 * 17 - a7 * 19;
}
__attribute__((noinline)) int64_t clang_tc_narrow(int64_t a0, int64_t a1, int64_t a2,
    int64_t a3, int64_t a4, int64_t a5, int64_t a6, int64_t a7, int8_t b, int16_t c,
    int32_t d) {
    return a0 - a1 + a2 - a3 + a4 - a5 + a6 - a7 + (int64_t)b * 1000003
        + (int64_t)c * 1009 + (int64_t)d;
}
__attribute__((noinline)) int64_t opaque(int64_t x) { return x * 0x9E37 + 0x5A5A; }
static int failures;
static void check(const char *what, int64_t got, int64_t want) {
    if (got != want) {
        printf("%s: got %lld want %lld\n", what, (long long)got, (long long)want);
        failures++;
    }
}
"#;

/// A C driver that keeps ten values live across `call` (a statement that
/// sets `got`) and checks both the result and their checksum afterwards.
fn driver(declaration: &str, cases: &[(&str, &str)]) -> String {
    let mut body = String::new();
    for (index, (call, want)) in cases.iter().enumerate() {
        body.push_str(&format!(
            "    {{\n        int64_t got = {call};\n        check(\"case {index}\", got, {want});\n    }}\n"
        ));
    }
    format!(
        "{C_PRELUDE}\n{declaration}\n\
         int main(void) {{\n\
         int64_t k0 = opaque(1), k1 = opaque(2), k2 = opaque(3), k3 = opaque(4), k4 = opaque(5);\n\
         int64_t k5 = opaque(6), k6 = opaque(7), k7 = opaque(8), k8 = opaque(9), k9 = opaque(10);\n\
         int64_t before = k0 ^ (k1 << 1) ^ (k2 << 2) ^ (k3 << 3) ^ (k4 << 4) ^ (k5 << 5)\n\
             ^ (k6 << 6) ^ (k7 << 7) ^ (k8 << 8) ^ (k9 << 9);\n\
         {body}\
         int64_t after = k0 ^ (k1 << 1) ^ (k2 << 2) ^ (k3 << 3) ^ (k4 << 4) ^ (k5 << 5)\n\
             ^ (k6 << 6) ^ (k7 << 7) ^ (k8 << 8) ^ (k9 << 9);\n\
         check(\"callee-saved checksum\", after, before);\n\
         return failures != 0;\n\
         }}\n"
    )
}

fn run_scenario(
    tag: &str,
    module: &Module,
    driver_source: &str,
    expected: impl Fn(OptLevel) -> Branches,
) {
    for level in LEVELS {
        let object = native::compile(module, level);
        let counts = branches(&object);
        assert_eq!(counts, expected(level), "{tag} at {level:?}");
        native::link_run(&format!("{tag}_{level:?}"), &object, driver_source);
    }
}

#[test]
fn stack_argument_sibling_call_to_clang_becomes_a_tail_branch() {
    let driver_source = driver(
        "int64_t tcg_tc_stack(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, \
         int64_t, int64_t, int64_t, int64_t);\n\
         static int64_t ref_stack(int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4,\n\
             int64_t a5, int64_t a6, int64_t a7, int64_t s0, int64_t s1) {\n\
             int64_t t = clang_tc_helper(a0);\n\
             return clang_tc_callee10(a0 + t, a1 + t, a2, a3, a4, a5, a6, a7, s0 ^ t, s1 - t);\n\
         }",
        &[
            (
                "tcg_tc_stack(1, 2, 3, 4, 5, 6, 7, 8, 9, 10)",
                "ref_stack(1, 2, 3, 4, 5, 6, 7, 8, 9, 10)",
            ),
            (
                "tcg_tc_stack(-5, 1LL << 40, -3, 99, -1000, 7, 123456789, -8, 0x7fff0000, -77)",
                "ref_stack(-5, 1LL << 40, -3, 99, -1000, 7, 123456789, -8, 0x7fff0000, -77)",
            ),
        ],
    );
    run_scenario("tc_stack", &stack_module(), &driver_source, |level| {
        if tail_pass_runs(level) {
            Branches {
                external_b: 1,
                external_bl: 1,
                blr: 0,
            }
        } else {
            Branches {
                external_b: 0,
                external_bl: 2,
                blr: 0,
            }
        }
    });
}

#[test]
fn register_only_sibling_call_after_callee_saved_pressure_becomes_a_tail_branch() {
    let driver_source = driver(
        "int64_t tcg_tc_regs(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, \
         int64_t, int64_t);\n\
         static int64_t ref_regs(int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4,\n\
             int64_t a5, int64_t a6, int64_t a7) {\n\
             int64_t t = clang_tc_helper(a0);\n\
             return clang_tc_callee8(a0 + t, a1, a2, a3, a4, a5, a6, a7 - t);\n\
         }",
        &[
            (
                "tcg_tc_regs(11, -12, 13, -14, 15, -16, 17, -18)",
                "ref_regs(11, -12, 13, -14, 15, -16, 17, -18)",
            ),
            (
                "tcg_tc_regs(1LL << 50, 3, 1LL << 33, 5, -6, 7, 8, 1LL << 61)",
                "ref_regs(1LL << 50, 3, 1LL << 33, 5, -6, 7, 8, 1LL << 61)",
            ),
        ],
    );
    run_scenario("tc_regs", &regs_module(), &driver_source, |level| {
        if tail_pass_runs(level) {
            Branches {
                external_b: 1,
                external_bl: 1,
                blr: 0,
            }
        } else {
            Branches {
                external_b: 0,
                external_bl: 2,
                blr: 0,
            }
        }
    });
}

#[test]
fn narrow_stack_arguments_are_redirected_store_for_store() {
    let driver_source = driver(
        "int64_t tcg_tc_narrow(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, \
         int64_t, int64_t, int8_t, int16_t, int32_t);\n\
         static int64_t ref_narrow(int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4,\n\
             int64_t a5, int64_t a6, int64_t a7, int8_t b, int16_t c, int32_t d) {\n\
             return clang_tc_narrow(a0, a1, a2, a3, a4, a5, a6, a7, (int8_t)(b + 1),\n\
                 (int16_t)(c - 3), (int32_t)((uint32_t)d * 2u));\n\
         }",
        &[
            (
                "tcg_tc_narrow(1, 2, 3, 4, 5, 6, 7, 8, -5, 300, -70000)",
                "ref_narrow(1, 2, 3, 4, 5, 6, 7, 8, -5, 300, -70000)",
            ),
            (
                "tcg_tc_narrow(-1, -2, -3, -4, -5, -6, -7, -8, 127, -32768, 0x7fffffff)",
                "ref_narrow(-1, -2, -3, -4, -5, -6, -7, -8, 127, -32768, 0x7fffffff)",
            ),
        ],
    );
    run_scenario("tc_narrow", &narrow_module(), &driver_source, |level| {
        if tail_pass_runs(level) {
            Branches {
                external_b: 1,
                external_bl: 0,
                blr: 0,
            }
        } else {
            Branches {
                external_b: 0,
                external_bl: 1,
                blr: 0,
            }
        }
    });
}

/// Adversarial control for the incoming-area redirect: swapping the two
/// forwarded stack arguments makes each redirected store overwrite the slot
/// the other argument is loaded from, and duplicating one stores a single
/// register to two incoming slots (identical operands once register
/// allocation blinds `IncomingArg`). A load sunk below a redirected store, or
/// a redirected store re-associated with the other slot, returns a wrong sum.
#[test]
fn forwarded_stack_arguments_are_read_before_their_slots_are_overwritten() {
    let declare = |name: &str| {
        format!(
            "int64_t {name}(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, \
             int64_t, int64_t, int64_t);"
        )
    };
    let expected = |level| {
        if tail_pass_runs(level) {
            Branches {
                external_b: 1,
                external_bl: 0,
                blr: 0,
            }
        } else {
            Branches {
                external_b: 0,
                external_bl: 1,
                blr: 0,
            }
        }
    };
    let swap_driver = driver(
        &declare("tcg_tc_swap"),
        &[
            (
                "tcg_tc_swap(1, 2, 3, 4, 5, 6, 7, 8, 9, 10)",
                "clang_tc_callee10(1, 2, 3, 4, 5, 6, 7, 8, 10, 9)",
            ),
            (
                "tcg_tc_swap(-5, 1LL << 40, -3, 99, -1000, 7, 123456789, -8, 0x7fff0000, -77)",
                "clang_tc_callee10(-5, 1LL << 40, -3, 99, -1000, 7, 123456789, -8, -77, 0x7fff0000)",
            ),
        ],
    );
    run_scenario(
        "tc_swap",
        &forwarded_stack_module("tcg_tc_swap", 1, 0),
        &swap_driver,
        expected,
    );
    let dup_driver = driver(
        &declare("tcg_tc_dup"),
        &[
            (
                "tcg_tc_dup(1, 2, 3, 4, 5, 6, 7, 8, 9, 10)",
                "clang_tc_callee10(1, 2, 3, 4, 5, 6, 7, 8, 10, 10)",
            ),
            (
                "tcg_tc_dup(11, -12, 13, -14, 15, -16, 17, -18, 1LL << 45, -(1LL << 37))",
                "clang_tc_callee10(11, -12, 13, -14, 15, -16, 17, -18, -(1LL << 37), -(1LL << 37))",
            ),
        ],
    );
    run_scenario(
        "tc_dup",
        &forwarded_stack_module("tcg_tc_dup", 1, 1),
        &dup_driver,
        expected,
    );
}

#[test]
fn stack_arguments_beyond_the_incoming_area_keep_the_call() {
    let driver_source = driver(
        "int64_t tcg_tc_overflow(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, \
         int64_t, int64_t, int64_t);",
        &[(
            "tcg_tc_overflow(1, 2, 3, 4, 5, 6, 7, 8, 9)",
            "clang_tc_callee10(1, 2, 3, 4, 5, 6, 7, 8, 9, 10)",
        )],
    );
    run_scenario("tc_overflow", &overflow_module(), &driver_source, |_| {
        Branches {
            external_b: 0,
            external_bl: 1,
            blr: 0,
        }
    });
}

#[test]
fn indirect_call_in_tail_position_keeps_its_blr() {
    let driver_source = driver(
        "int64_t tcg_tc_indirect(int64_t (*)(int64_t), int64_t);",
        &[(
            "tcg_tc_indirect(clang_tc_helper, 41)",
            "clang_tc_helper(41)",
        )],
    );
    run_scenario("tc_indirect", &indirect_module(), &driver_source, |_| {
        Branches {
            external_b: 0,
            external_bl: 0,
            blr: 1,
        }
    });
}
