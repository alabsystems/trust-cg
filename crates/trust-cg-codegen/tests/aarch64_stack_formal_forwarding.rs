// trust-cg-codegen - stack-passed parameters forwarded through dead incoming
// argument registers compile
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The allocator may load a stack-passed parameter straight into an incoming
//! argument register whose own parameter is dead, and the body may then copy
//! it out of that register. `f(a, p1..p5, get, p7, i, tbl)` passes `tbl` and
//! `i` as the first call's X0/X1 while `p1` is unused, so the call's argument
//! setups become identity copies over the two loads:
//!
//! ```text
//! mov  x19, x0              ; formal copy of `a`
//! ldr  x1, [x29, #in+0]     ; i
//! ldr  x0, [x29, #in+8]     ; tbl
//! Copy x0 <- x0             ; call-argument setup (identity)
//! Copy x1 <- x1             ; call-argument setup (identity)
//! blr/bl ...
//! ```
//!
//! Block arguments do the same: a loop header seeded from a stack parameter
//! that was loaded into a dead incoming X3 gets `ldr x3, [..]; mov x9, x3`.
//!
//! After allocation such a copy has the shape of a formal read of the incoming
//! register behind the load that wrote it, so
//! `verify_aarch64_formal_entry_copy_hazards` takes its formal reads from the
//! function before allocation. Reading them off the allocated function refused
//! these valid functions ("AArch64 formal argument copy hazard ... LdrRI
//! dst=x1 aliases unread ABI source x1"). Every function here must compile at
//! O2 and O3 under both AArch64 allocator profiles and return the value plain
//! Rust arithmetic computes. The call variants cover a target dying at its
//! `BLR`, a target live after the call, a direct `BL`, and a direct `BL` with
//! no `BLR` at all.
#![cfg(target_arch = "aarch64")]

#[path = "common/pinned_target.rs"]
mod pinned_target;

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, CastOp, ICmpOp, Module, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "stack_params_as_call_args";

/// `get(tbl, i) -> tbl[i & 3]`.
extern "C" fn get_entry(tbl: *const u64, i: u64) -> u64 {
    // SAFETY: every caller passes a live 4-entry table.
    unsafe { *tbl.add((i & 3) as usize) }
}

extern "C" fn k0(a: u64) -> u64 {
    a.wrapping_mul(3).wrapping_add(1)
}
extern "C" fn k1(a: u64) -> u64 {
    a ^ 0x5555
}
extern "C" fn k2(a: u64) -> u64 {
    a.rotate_left(9)
}
extern "C" fn k3(a: u64) -> u64 {
    a.wrapping_sub(77)
}

fn reference(i: u64, a: u64) -> u64 {
    match i & 3 {
        0 => a.wrapping_mul(3).wrapping_add(1),
        1 => a ^ 0x5555,
        2 => a.rotate_left(9),
        _ => a.wrapping_sub(77),
    }
}

/// `f(a, p1..p5, get, p7, i, tbl) = get(tbl, i)(a)` (see [`Getter`]).
///
/// Parameters 0-7 arrive in X0-X7 (`get` in X6); `i` and `tbl` are the two
/// stack-passed parameters.
#[derive(Clone, Copy, PartialEq)]
enum Getter {
    /// `get(tbl, i)` through the X6 parameter, which dies at that `BLR`.
    DyingTarget,
    /// The same, and `get` is read again after the second call.
    LiveTarget,
    /// A direct `BL ext_get(tbl, i)`, then the indirect call.
    Direct,
    /// A direct `BL ext_get(tbl, i)` whose result is returned as an integer
    /// plus `a`: no `BLR` in the function.
    DirectOnly,
}

fn build(mode: Getter) -> Module {
    let mut mb = ModuleBuilder::new("blr_stack_param_refusal");
    let getter = mb.add_func_type(vec![Ty::Ptr, Ty::U64], vec![Ty::Ptr]);
    let ext_get = mb.declare_function("ext_get", getter);
    let unary = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut params = vec![Ty::U64; 6];
    params.extend([Ty::Ptr, Ty::U64, Ty::U64, Ty::Ptr]);
    let ty = mb.add_func_type(params, vec![Ty::U64]);
    let mut fb = mb.function(ENTRY, ty);
    let b = fb.create_block();
    let a = fb.add_block_param(b, Ty::U64);
    for _ in 1..6 {
        fb.add_block_param(b, Ty::U64);
    }
    let get = fb.add_block_param(b, Ty::Ptr);
    fb.add_block_param(b, Ty::U64);
    let i = fb.add_block_param(b, Ty::U64);
    let tbl = fb.add_block_param(b, Ty::Ptr);
    fb.switch_to_block(b);
    let target = if matches!(mode, Getter::Direct | Getter::DirectOnly) {
        fb.call(ext_get, vec![tbl, i])
    } else {
        fb.call_indirect(get, getter, vec![tbl, i])
    };
    let mut r = if mode == Getter::DirectOnly {
        let t = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, target);
        fb.binop(BinOp::Add, Ty::U64, t, a)
    } else {
        fb.call_indirect(target, unary, vec![a])
    };
    if mode == Getter::LiveTarget {
        let get_int = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, get);
        r = fb.binop(BinOp::Add, Ty::U64, r, get_int);
    }
    fb.ret(vec![r]);
    fb.build();
    // `ext_get` is an FFI boundary: trust-ir requires the pinned target
    // (`TargetInfoRequired`), and every ingestion entry refuses what the
    // validator refuses (WS7.3). The JIT runs on the host.
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    pinned_target::pin(&mut module, pinned_target::host_triple());
    module
}

fn run(mode: Getter) {
    let module = build(mode);
    let symbols = HashMap::from([("ext_get".to_string(), get_entry as *const u8)]);
    let table: Box<[u64; 4]> = Box::new([
        k0 as *const () as usize as u64,
        k1 as *const () as usize as u64,
        k2 as *const () as usize as u64,
        k3 as *const () as usize as u64,
    ]);
    let get = get_entry as *const () as usize as u64;
    type Entry = extern "C" fn(u64, u64, u64, u64, u64, u64, u64, u64, u64, u64) -> u64;
    let mut failures = Vec::new();
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        for fast in [false, true] {
            let mut config = CompilerConfig::jit_fast(Target::Aarch64);
            config.opt_level = opt_level;
            config.enable_jit_fast_regalloc = fast;
            let label = format!("{opt_level:?} fast_regalloc={fast}");
            let result = match Compiler::new(config)
                .with_codegen_license(permit_unlicensed())
                .compile_module_to_jit(&module, &symbols)
            {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{label}: valid input refused: {error}"));
                    continue;
                }
            };
            let ptr = result
                .buffer
                .get_fn_ptr_bound(ENTRY)
                .expect("entry symbol")
                .as_ptr();
            // SAFETY: the entry's trust-ir signature is ten pointer-sized
            // integer-class parameters returning u64; `result` outlives it.
            let entry: Entry = unsafe { std::mem::transmute(ptr) };
            for i in 0..4u64 {
                for a in [0u64, 9, u64::MAX] {
                    let got = entry(a, 11, 12, 13, 14, 15, get, 17, i, table.as_ptr() as u64);
                    let mut expected = if mode == Getter::DirectOnly {
                        table[(i & 3) as usize].wrapping_add(a)
                    } else {
                        reference(i, a)
                    };
                    if mode == Getter::LiveTarget {
                        expected = expected.wrapping_add(get);
                    }
                    if got != expected {
                        failures.push(format!(
                            "{label}: i={i} a={a:#x} got {got:#x} expected {expected:#x}"
                        ));
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn indirect_call_on_stack_parameters_through_a_target_that_dies_at_its_blr() {
    run(Getter::DyingTarget);
}

#[test]
fn indirect_call_on_stack_parameters_through_a_target_live_after_the_call() {
    run(Getter::LiveTarget);
}

#[test]
fn direct_call_on_stack_parameters() {
    run(Getter::Direct);
}

#[test]
fn direct_call_on_stack_parameters_without_any_blr() {
    run(Getter::DirectOnly);
}

// ---------------------------------------------------------------------------
// Block arguments
// ---------------------------------------------------------------------------

/// `f(p0..)` enters a loop whose header arguments are parameters: the trip
/// count is `p[counter] & 7` and the carried values start at `p[seeds[j]]`.
/// Each trip sets `v[j] = ops[j](v[(j + 1) % m], v[j])`; the exit returns
/// `sum_k rotl(v[k], 7k)` xor every `p[post[_]]`. With a stack parameter
/// loaded into a dead incoming register, its block-argument copy reads that
/// register after the load wrote it.
struct LoopShape {
    params: usize,
    counter: usize,
    seeds: &'static [usize],
    ops: &'static [BinOp],
    post: &'static [usize],
}

const LOOP_SHAPES: [LoopShape; 6] = [
    LoopShape {
        params: 10,
        counter: 3,
        seeds: &[8, 8, 8, 9],
        ops: &[BinOp::Sub, BinOp::Add, BinOp::Sub, BinOp::Add],
        post: &[5],
    },
    LoopShape {
        params: 10,
        counter: 9,
        seeds: &[8, 8, 9, 9],
        ops: &[BinOp::Add, BinOp::Xor, BinOp::Xor, BinOp::Xor],
        post: &[9],
    },
    LoopShape {
        params: 11,
        counter: 10,
        seeds: &[8, 10],
        ops: &[BinOp::Xor, BinOp::Add],
        post: &[8, 9],
    },
    LoopShape {
        params: 9,
        counter: 8,
        seeds: &[8, 8, 2],
        ops: &[BinOp::Sub, BinOp::Xor, BinOp::Add],
        post: &[],
    },
    LoopShape {
        params: 10,
        counter: 7,
        seeds: &[9, 9, 9, 9],
        ops: &[BinOp::Sub, BinOp::Add, BinOp::Xor, BinOp::Add],
        post: &[],
    },
    LoopShape {
        params: 10,
        counter: 5,
        seeds: &[8, 8],
        ops: &[BinOp::Add, BinOp::Xor],
        post: &[0],
    },
];

const LOOP_ENTRY: &str = "stack_params_as_block_args";

fn loop_reference(shape: &LoopShape, args: &[u64]) -> u64 {
    let mut v: Vec<u64> = shape.seeds.iter().map(|&p| args[p]).collect();
    let m = v.len();
    for _ in 0..args[shape.counter] & 7 {
        let old = v.clone();
        for j in 0..m {
            let (a, b) = (old[(j + 1) % m], old[j]);
            v[j] = match shape.ops[j] {
                BinOp::Add => a.wrapping_add(b),
                BinOp::Xor => a ^ b,
                BinOp::Sub => a.wrapping_sub(b),
                op => unreachable!("{op:?}"),
            };
        }
    }
    let mut acc = 0u64;
    for (k, x) in v.iter().enumerate() {
        acc = acc.wrapping_add(x.rotate_left(k as u32 * 7));
    }
    shape.post.iter().fold(acc, |acc, &p| acc ^ args[p])
}

fn build_loop(shape: &LoopShape) -> Module {
    let mut mb = ModuleBuilder::new("stack_param_block_args");
    let ty = mb.add_func_type(vec![Ty::U64; shape.params], vec![Ty::U64]);
    let mut fb = mb.function(LOOP_ENTRY, ty);
    let entry = fb.create_block();
    let header = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    let params: Vec<_> = (0..shape.params)
        .map(|_| fb.add_block_param(entry, Ty::U64))
        .collect();
    let m = shape.seeds.len();
    let h_i = fb.add_block_param(header, Ty::U64);
    let h_v: Vec<_> = (0..m)
        .map(|_| fb.add_block_param(header, Ty::U64))
        .collect();
    let b_i = fb.add_block_param(body, Ty::U64);
    let b_v: Vec<_> = (0..m).map(|_| fb.add_block_param(body, Ty::U64)).collect();
    let e_v: Vec<_> = (0..m).map(|_| fb.add_block_param(exit, Ty::U64)).collect();

    fb.switch_to_block(entry);
    let mut seeds = vec![params[shape.counter]];
    seeds.extend(shape.seeds.iter().map(|&p| params[p]));
    fb.br(header, seeds);

    fb.switch_to_block(header);
    let seven = fb.iconst(Ty::U64, 7);
    let left = fb.binop(BinOp::And, Ty::U64, h_i, seven);
    let zero = fb.iconst(Ty::U64, 0);
    let more = fb.icmp(ICmpOp::Ne, Ty::U64, left, zero);
    let mut body_args = vec![left];
    body_args.extend(h_v.iter().copied());
    fb.condbr(more, body, body_args, exit, h_v.clone());

    fb.switch_to_block(body);
    let mut next = Vec::new();
    for j in 0..m {
        next.push(fb.binop(shape.ops[j], Ty::U64, b_v[(j + 1) % m], b_v[j]));
    }
    let one = fb.iconst(Ty::U64, 1);
    let mut header_args = vec![fb.binop(BinOp::Sub, Ty::U64, b_i, one)];
    header_args.extend(next);
    fb.br(header, header_args);

    fb.switch_to_block(exit);
    let mut acc = fb.iconst(Ty::U64, 0);
    for (k, &x) in e_v.iter().enumerate() {
        let rotated = if k == 0 {
            x
        } else {
            let left_by = fb.iconst(Ty::U64, (k * 7) as i128);
            let right_by = fb.iconst(Ty::U64, (64 - k * 7) as i128);
            let high = fb.binop(BinOp::Shl, Ty::U64, x, left_by);
            let low = fb.binop(BinOp::LShr, Ty::U64, x, right_by);
            fb.binop(BinOp::Or, Ty::U64, high, low)
        };
        acc = fb.binop(BinOp::Add, Ty::U64, acc, rotated);
    }
    for &p in shape.post {
        acc = fb.binop(BinOp::Xor, Ty::U64, acc, params[p]);
    }
    fb.ret(vec![acc]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Call a JIT entry taking `args.len()` (9 to 11) u64 parameters.
///
/// # Safety
/// `ptr` must be such an entry returning u64.
unsafe fn call_loop_entry(ptr: *const u8, a: &[u64]) -> u64 {
    type F9 = extern "C" fn(u64, u64, u64, u64, u64, u64, u64, u64, u64) -> u64;
    type F10 = extern "C" fn(u64, u64, u64, u64, u64, u64, u64, u64, u64, u64) -> u64;
    type F11 = extern "C" fn(u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64) -> u64;
    // SAFETY: the caller guarantees the entry's arity and return type.
    unsafe {
        match a.len() {
            9 => std::mem::transmute::<*const u8, F9>(ptr)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8],
            ),
            10 => std::mem::transmute::<*const u8, F10>(ptr)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9],
            ),
            11 => std::mem::transmute::<*const u8, F11>(ptr)(
                a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10],
            ),
            n => panic!("no {n}-argument entry trampoline"),
        }
    }
}

#[test]
fn stack_parameters_forwarded_as_loop_block_arguments() {
    let mut failures = Vec::new();
    for (index, shape) in LOOP_SHAPES.iter().enumerate() {
        let module = build_loop(shape);
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            for fast in [false, true] {
                let mut config = CompilerConfig::jit_fast(Target::Aarch64);
                config.opt_level = opt_level;
                config.enable_jit_fast_regalloc = fast;
                let label = format!("shape {index} {opt_level:?} fast_regalloc={fast}");
                let result = match Compiler::new(config)
                    .with_codegen_license(permit_unlicensed())
                    .compile_module_to_jit(&module, &HashMap::new())
                {
                    Ok(result) => result,
                    Err(error) => {
                        failures.push(format!("{label}: valid input refused: {error}"));
                        continue;
                    }
                };
                let ptr = result
                    .buffer
                    .get_fn_ptr_bound(LOOP_ENTRY)
                    .expect("entry symbol")
                    .as_ptr();
                for s in 0..8u64 {
                    let args: Vec<u64> = (0..shape.params as u64)
                        .map(|k| {
                            (k + 1)
                                .wrapping_mul(0x1234_5678_9ABC_DEF1)
                                .rotate_left((s * 13 + k) as u32)
                                ^ s
                        })
                        .collect();
                    // SAFETY: the entry takes `shape.params` u64 parameters
                    // and returns u64; `result` outlives the call.
                    let got = unsafe { call_loop_entry(ptr, &args) };
                    let expected = loop_reference(shape, &args);
                    if got != expected {
                        failures.push(format!(
                            "{label}: args={args:x?} got {got:#x} expected {expected:#x}"
                        ));
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
