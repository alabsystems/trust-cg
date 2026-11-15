// trust-cg-codegen - an entry block that is also a loop header reads its
// formal arguments once
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! trust-ir admits a branch to the entry block, so the entry block can head a
//! loop:
//!
//! ```text
//! entry(a, b, n): condbr n != 0 -> body, exit
//! body:           br entry(a * 3 + b, a, n - 1)
//! exit:           ret a ^ b
//! ```
//!
//! The formal argument materializations (`mov x20, x0`, an incoming-argument
//! load, the saved X8 result pointer) must run once per call. Placed at the
//! top of the re-entered entry block they ran on every back edge, overwrote
//! the block arguments that edge had just written with the stale incoming
//! registers, and the function above never returned for `n = 1` (O2:
//! `0xc: mov x20, x0 ... 0x38: ... b 0xc`). The formal argument copy guard and
//! the register-allocation validator both accepted it. Instruction selection
//! now emits the formals into a dedicated block ahead of a re-entered entry
//! block.
//!
//! Every function runs at O0-O3 under both AArch64 allocator profiles against
//! a plain Rust model. A call that does not return within the timeout is a
//! failure, not a hang of the test.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Module, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

const ENTRY: &str = "entry_loop";
const SCRAMBLE: &str = "entry_loop_scramble";
const SEEDS: [u64; 3] = [5, 0x1111_2222_3333_4444, u64::MAX - 6];

/// `scramble(x, y)`, which also overwrites every caller-saved integer
/// register (X0-X17, X8 included) before it returns.
extern "C" fn scramble(x: u64, y: u64) -> u64 {
    let result = x.rotate_left(13).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ y;
    // SAFETY: writes only registers declared as clobbered outputs.
    unsafe {
        core::arch::asm!(
            "mov x0, #0x0c0b", "mov x1, #0x1c0b", "mov x2, #0x2c0b", "mov x3, #0x3c0b",
            "mov x4, #0x4c0b", "mov x5, #0x5c0b", "mov x6, #0x6c0b", "mov x7, #0x7c0b",
            "mov x8, #0x8c0b", "mov x9, #0x9c0b", "mov x10, #0xac0b", "mov x11, #0xbc0b",
            "mov x12, #0xcc0b", "mov x13, #0xdc0b", "mov x14, #0xec0b", "mov x15, #0xfc0b",
            "mov x16, #0x1d0b", "mov x17, #0x1e0b",
            out("x0") _, out("x1") _, out("x2") _, out("x3") _, out("x4") _,
            out("x5") _, out("x6") _, out("x7") _, out("x8") _, out("x9") _,
            out("x10") _, out("x11") _, out("x12") _, out("x13") _, out("x14") _,
            out("x15") _, out("x16") _, out("x17") _,
            options(nostack, nomem),
        );
    }
    result
}

/// `(a, b) -> (a * 3 + b, a)`, or `(scramble(b, a), a)` with a call.
fn step(a: u64, b: u64, call: bool) -> (u64, u64) {
    if call {
        (scramble(b, a), a)
    } else {
        (a.wrapping_mul(3).wrapping_add(b), a)
    }
}

/// Emit `step` on the block parameters `a`, `b`.
fn build_step(
    fb: &mut FunctionBuilder<'_>,
    scramble: Option<trust_ir::FuncId>,
    a: ValueId,
    b: ValueId,
) -> ValueId {
    match scramble {
        Some(callee) => fb.call(callee, vec![b, a]),
        None => {
            let three = fb.iconst(Ty::U64, 3);
            let scaled = fb.binop(BinOp::Mul, Ty::U64, a, three);
            fb.binop(BinOp::Add, Ty::U64, scaled, b)
        }
    }
}

/// `f(a, b, n)`: `n` trips of `(a, b) = step(a, b)` through a back edge into
/// the entry block, then `a ^ b`. With `sret` the result is the three-word
/// tuple `(a, b, a ^ b)`, returned through the X8 result pointer.
fn build_registers(call: bool, sret: bool) -> Module {
    let mut mb = ModuleBuilder::new("entry_loop_registers");
    let scramble_ty = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let callee = call.then(|| mb.declare_function(SCRAMBLE, scramble_ty));
    let triple = Ty::Tuple(vec![Ty::U64; 3]);
    let returns = if sret { triple.clone() } else { Ty::U64 };
    let ty = mb.add_func_type(vec![Ty::U64; 3], vec![returns]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    let a = fb.add_block_param(entry, Ty::U64);
    let b = fb.add_block_param(entry, Ty::U64);
    let n = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    let more = fb.icmp(ICmpOp::Ne, Ty::U64, n, zero);
    fb.condbr(more, body, vec![], exit, vec![]);
    fb.switch_to_block(body);
    let next = build_step(&mut fb, callee, a, b);
    let one = fb.iconst(Ty::U64, 1);
    let n1 = fb.binop(BinOp::Sub, Ty::U64, n, one);
    fb.br(entry, vec![next, a, n1]);
    fb.switch_to_block(exit);
    let x = fb.binop(BinOp::Xor, Ty::U64, a, b);
    let result = if sret {
        fb.make_aggregate(triple, vec![a, b, x])
    } else {
        x
    };
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn registers_reference(mut a: u64, mut b: u64, n: u64, call: bool) -> (u64, u64) {
    for _ in 0..n {
        (a, b) = step(a, b, call);
    }
    (a, b)
}

/// `f(p0..p9)`, `p8` and `p9` stack-passed: while `p9 != 0`, shift
/// `p0..p8` one place up with `p0 = p0 * 3 + p1` (or `scramble(p1, p0)`),
/// decrement `p9`, and branch back into the entry block; then return
/// `sum_k rotl(p_k, 7k)` over `p0..p8`.
fn build_stack(call: bool) -> Module {
    let mut mb = ModuleBuilder::new("entry_loop_stack");
    let scramble_ty = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let callee = call.then(|| mb.declare_function(SCRAMBLE, scramble_ty));
    let ty = mb.add_func_type(vec![Ty::U64; 10], vec![Ty::U64]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    let p: Vec<_> = (0..10)
        .map(|_| fb.add_block_param(entry, Ty::U64))
        .collect();
    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    let more = fb.icmp(ICmpOp::Ne, Ty::U64, p[9], zero);
    fb.condbr(more, body, vec![], exit, vec![]);
    fb.switch_to_block(body);
    let mut next = vec![build_step(&mut fb, callee, p[0], p[1])];
    next.extend_from_slice(&p[..8]);
    let one = fb.iconst(Ty::U64, 1);
    next.push(fb.binop(BinOp::Sub, Ty::U64, p[9], one));
    fb.br(entry, next);
    fb.switch_to_block(exit);
    let mut acc = p[0];
    for (k, &x) in p.iter().enumerate().take(9).skip(1) {
        let left_by = fb.iconst(Ty::U64, (k * 7) as i128);
        let right_by = fb.iconst(Ty::U64, (64 - k * 7) as i128);
        let high = fb.binop(BinOp::Shl, Ty::U64, x, left_by);
        let low = fb.binop(BinOp::LShr, Ty::U64, x, right_by);
        let rotated = fb.binop(BinOp::Or, Ty::U64, high, low);
        acc = fb.binop(BinOp::Add, Ty::U64, acc, rotated);
    }
    fb.ret(vec![acc]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn stack_reference(mut p: [u64; 10], call: bool) -> u64 {
    while p[9] != 0 {
        let (head, _) = step(p[0], p[1], call);
        p.copy_within(0..8, 1);
        p[0] = head;
        p[9] -= 1;
    }
    (0..9).fold(0u64, |acc, k| {
        acc.wrapping_add(p[k].rotate_left(7 * k as u32))
    })
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq)]
struct Triple(u64, u64, u64);

type Registers = extern "C" fn(u64, u64, u64) -> u64;
type RegistersSret = extern "C" fn(u64, u64, u64) -> Triple;
type Stack = extern "C" fn(u64, u64, u64, u64, u64, u64, u64, u64, u64, u64) -> u64;

/// Run `call` on its own thread; `None` when it has not returned in time.
fn call_with_timeout<T: Send + 'static>(call: impl FnOnce() -> T + Send + 'static) -> Option<T> {
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(call());
    });
    rx.recv_timeout(Duration::from_secs(5)).ok()
}

/// Compile `module` under every opt level and allocator profile and check
/// each `(arguments, expected)` case through `invoke(entry address, args)`.
fn check<R>(module: &Module, cases: &[(Vec<u64>, R)], invoke: fn(usize, &[u64]) -> R)
where
    R: PartialEq + std::fmt::Debug + Send + Clone + 'static,
{
    let symbols = HashMap::from([(SCRAMBLE.to_string(), scramble as *const u8)]);
    let mut failures = Vec::new();
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        for fast in [false, true] {
            let mut config = CompilerConfig::jit_fast(Target::Aarch64);
            config.opt_level = opt_level;
            config.enable_jit_fast_regalloc = fast;
            let label = format!("{opt_level:?} fast_regalloc={fast}");
            let result = match Compiler::new(config)
                .with_codegen_license(permit_unlicensed())
                .compile_module_to_jit(module, &symbols)
            {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{label}: refused: {error}"));
                    continue;
                }
            };
            let entry = result
                .buffer
                .get_fn_ptr_bound(ENTRY)
                .expect("entry symbol")
                .as_ptr() as usize;
            for (args, expected) in cases {
                let owned = args.clone();
                match call_with_timeout(move || invoke(entry, &owned)) {
                    Some(got) if got == *expected => {}
                    Some(got) => failures.push(format!(
                        "{label}: args={args:x?} got {got:x?} expected {expected:x?}"
                    )),
                    None => {
                        failures.push(format!(
                            "{label}: args={args:x?} did not return (expected {expected:x?})"
                        ));
                        // The looping thread still runs the JIT code.
                        std::mem::forget(result);
                        break;
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

fn registers_cases(call: bool) -> Vec<(Vec<u64>, (u64, u64))> {
    let mut cases = Vec::new();
    for n in 0..4 {
        for (i, &a) in SEEDS.iter().enumerate() {
            let b = SEEDS[(i + 1) % SEEDS.len()] ^ 7;
            cases.push((vec![a, b, n], registers_reference(a, b, n, call)));
        }
    }
    cases
}

fn run_registers(call: bool) {
    let cases: Vec<_> = registers_cases(call)
        .into_iter()
        .map(|(args, (a, b))| (args, a ^ b))
        .collect();
    check(&build_registers(call, false), &cases, |entry, args| {
        // SAFETY: the entry takes three u64 parameters and returns u64; the
        // JIT buffer outlives the call.
        let f: Registers = unsafe { std::mem::transmute(entry) };
        f(args[0], args[1], args[2])
    });
}

#[test]
fn register_formals_re_entered_without_a_call() {
    run_registers(false);
}

#[test]
fn register_formals_re_entered_across_a_clobbering_call() {
    run_registers(true);
}

#[test]
fn indirect_result_pointer_re_entered_across_a_clobbering_call() {
    let cases: Vec<_> = registers_cases(true)
        .into_iter()
        .map(|(args, (a, b))| (args, Triple(a, b, a ^ b)))
        .collect();
    check(&build_registers(true, true), &cases, |entry, args| {
        // SAFETY: the entry takes three u64 parameters and returns a
        // three-word aggregate through X8; the JIT buffer outlives the call.
        let f: RegistersSret = unsafe { std::mem::transmute(entry) };
        f(args[0], args[1], args[2])
    });
}

fn run_stack(call: bool) {
    let mut cases = Vec::new();
    for n in 0..4u64 {
        for s in 0..2u64 {
            let mut p = [0u64; 10];
            for (k, slot) in p.iter_mut().enumerate().take(9) {
                *slot = (k as u64 + 1)
                    .wrapping_mul(0x1234_5678_9ABC_DEF1)
                    .rotate_left((s * 13 + k as u64) as u32);
            }
            p[9] = n;
            cases.push((p.to_vec(), stack_reference(p, call)));
        }
    }
    check(&build_stack(call), &cases, |entry, a| {
        // SAFETY: the entry takes ten u64 parameters and returns u64; the JIT
        // buffer outlives the call.
        let f: Stack = unsafe { std::mem::transmute(entry) };
        f(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9])
    });
}

#[test]
fn stack_formals_re_entered_without_a_call() {
    run_stack(false);
}

#[test]
fn stack_formals_re_entered_across_a_clobbering_call() {
    run_stack(true);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
