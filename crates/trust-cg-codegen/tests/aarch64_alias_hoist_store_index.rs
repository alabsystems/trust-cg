// trust-cg-codegen - alias-versioned load hoisting over a 32-bit store index
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `i = 0; loop { a[i] = 7; *out = *p; i += 1; if i >= n { break } }` with a
//! 32-bit index `i` and bound `n` (a parameter or the constant 4), run through
//! the JIT at every optimization level.
//!
//! The `i32`/`u32` index reaches the store as a W register read through
//! `sxtw`/`uxtw` (ext-addr), and `n` is a Gpr32 register: the parameter, or a
//! `movz #4` the selector hoists ahead of the loop. The alias-versioned load
//! hoist (O2/O3) guarded such a register bound with `cmp (8n >> 3), n` against
//! a 64-bit shift result, which the encoder refuses for a W-register `n`, so
//! the whole function failed to compile. These are executions on this host:
//! tested, not proved.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const ENTRY: &str = "store_then_copy_32";

/// The do-while above with the index and bound of type `ty` (`I32` or `U32`),
/// exiting on `icmp <exit> i + 1, n`, where `n` is the constant `bound` when
/// given and the fourth parameter otherwise.
fn do_while_module(ty: Ty, exit: ICmpOp, bound: Option<i128>) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_alias_hoist_store_index");
    let sig = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, ty.clone()], vec![]);
    let mut fb = mb.function(ENTRY, sig);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let p = fb.add_block_param(entry, Ty::Ptr);
    let out = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, ty.clone());
    let header = fb.create_block();
    let i = fb.add_block_param(header, ty.clone());
    let done = fb.create_block();

    fb.switch_to_block(entry);
    let zero = fb.iconst(ty.clone(), 0);
    fb.br(header, vec![zero]);

    fb.switch_to_block(header);
    let slot = fb.gep(Ty::U64, a, vec![i]);
    let seven = fb.iconst(Ty::U64, 7);
    fb.store(Ty::U64, slot, seven);
    let value = fb.load(Ty::U64, p);
    fb.store(Ty::U64, out, value);
    let one = fb.iconst(ty.clone(), 1);
    let step = fb.binop(BinOp::Add, ty.clone(), i, one);
    let n = match bound {
        Some(k) => fb.iconst(ty.clone(), k),
        None => n,
    };
    let stop = fb.icmp(exit, ty, step, n);
    fb.condbr(stop, done, vec![], header, vec![step]);

    fb.switch_to_block(done);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn jit(module: &trust_ir::Module, opt_level: OptLevel) -> JitCompilationResult {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
}

/// Compile `module` at every level and run `call(entry, a, p, out)` on a
/// zeroed 8-element `a` with `p = a + p_index` for each `(p_index, n, want)`,
/// checking `*out == want` and that iteration 0 stored `a[0]`.
fn check<K: Copy>(
    module: &trust_ir::Module,
    cases: &[(usize, i64, u64)],
    call: impl Fn(K, *mut u64, *const u64, *mut u64, i64),
) {
    for opt_level in LEVELS {
        let result = jit(module, opt_level);
        // SAFETY: each caller's `K` is `extern "C" fn(*mut u64, *const u64,
        // *mut u64, i32|u32)`, matching the trust-ir signature, and `result`
        // outlives every call.
        let entry = unsafe { result.buffer.get_fn_bound::<K>(ENTRY) }.expect("entry symbol");
        for &(p_index, n, want) in cases {
            let mut a = [0u64; 8];
            let mut out = u64::MAX;
            let base = a.as_mut_ptr();
            // SAFETY: every kernel stores at most `a[0..max(n, 1)]` with
            // `max(n, 1) <= 8` (a non-positive `n` runs the body once; the
            // constant-bound kernel stores `a[0..4]`), and `p_index < 8`, so
            // every access stays inside `a` and `out`.
            call(
                *entry.as_ref(),
                base,
                unsafe { base.add(p_index) },
                &mut out,
                n,
            );
            assert_eq!(out, want, "{opt_level:?}: p = a + {p_index}, n = {n}");
            assert_eq!(a[0], 7, "{opt_level:?}: iteration 0 always stores a[0]");
        }
    }
}

type SignedKernel = extern "C" fn(*mut u64, *const u64, *mut u64, i32);
type UnsignedKernel = extern "C" fn(*mut u64, *const u64, *mut u64, u32);

#[test]
fn an_i32_indexed_do_while_with_a_register_bound_compiles_and_loads_its_stores() {
    let module = do_while_module(Ty::I32, ICmpOp::Sge, None);
    check(
        &module,
        &[
            (0, -1, 7),
            (0, 0, 7),
            (0, 1, 7),
            (3, 4, 7),
            (4, 4, 0),
            (7, 8, 7),
        ],
        |kernel: SignedKernel, a, p, out, n| kernel(a, p, out, n as i32),
    );
}

#[test]
fn a_u32_indexed_do_while_with_a_register_bound_compiles_and_loads_its_stores() {
    let module = do_while_module(Ty::U32, ICmpOp::Uge, None);
    check(
        &module,
        &[(0, 0, 7), (0, 1, 7), (3, 4, 7), (4, 4, 0), (7, 8, 7)],
        |kernel: UnsignedKernel, a, p, out, n| kernel(a, p, out, n as u32),
    );
}

/// The constant bound 4 ignores the `n` argument: the loop stores `a[0..4]`.
#[test]
fn an_i32_indexed_do_while_with_a_constant_bound_compiles_and_loads_its_stores() {
    let module = do_while_module(Ty::I32, ICmpOp::Sge, Some(4));
    check(
        &module,
        &[(0, 0, 7), (3, 0, 7), (4, 0, 0), (7, 0, 0)],
        |kernel: SignedKernel, a, p, out, n| kernel(a, p, out, n as i32),
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
