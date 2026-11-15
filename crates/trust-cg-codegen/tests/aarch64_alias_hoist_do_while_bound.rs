// trust-cg-codegen - alias-versioned load hoisting: the do-while's first store
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `i = 0; loop { a[i] = 7; *out = *p; i += 1; if i >= n { break } }`, run
//! through the JIT at every optimization level.
//!
//! The body runs once whatever `n` is, so with `p == a` iteration 0 stores
//! `a[0] = 7` before it loads `*p` and `*out` must be 7. The alias-versioned
//! load hoist (O2/O3) sizes the store range as `[a, a + 8n)`, which is empty for
//! `n == 0` and wraps below `a` for a negative signed `n`; both cleared the
//! disjointness check, and the fast clone loaded `*p` ahead of the store.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const ENTRY: &str = "store_then_copy";

type Kernel = extern "C" fn(*mut u64, *const u64, *mut u64, u64);

/// The do-while above with the index and bound of type `ty`, exiting on
/// `icmp <exit> step, n`.
fn do_while_module(ty: Ty, exit: ICmpOp) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_alias_hoist_do_while_bound");
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

/// Run the kernel on a zeroed 8-element `a` with `p = a + p_index` and return
/// `(*out, a)`.
fn run(kernel: Kernel, p_index: usize, n: u64) -> (u64, [u64; 8]) {
    let mut a = [0u64; 8];
    let mut out = u64::MAX;
    let base = a.as_mut_ptr();
    // SAFETY: every `n` passed below stores at most `a[0..max(n, 1)]` with
    // `max(n, 1) <= 8` (a non-positive signed `n` runs the body once), and
    // `p_index < 8`, so every access stays inside `a` and `out`.
    kernel(base, unsafe { base.add(p_index) }, &mut out, n);
    (out, a)
}

/// `(p_index, n, expected *out)` for the unsigned and signed kernels.
fn check(module: &trust_ir::Module, cases: &[(usize, u64, u64)]) {
    for opt_level in LEVELS {
        let result = jit(module, opt_level);
        // SAFETY: the trust-ir signature is (ptr, ptr, ptr, i64/u64) -> (),
        // matching `Kernel`, and `result` outlives every call.
        let entry = unsafe { result.buffer.get_fn_bound::<Kernel>(ENTRY) }.expect("entry symbol");
        for &(p_index, n, want) in cases {
            let (out, a) = run(*entry.as_ref(), p_index, n);
            assert_eq!(
                out, want,
                "{opt_level:?}: p = a + {p_index}, n = {}",
                n as i64
            );
            assert_eq!(a[0], 7, "{opt_level:?}: iteration 0 always stores a[0]");
        }
    }
}

#[test]
fn an_unsigned_do_while_with_a_zero_bound_loads_its_own_first_store() {
    let module = do_while_module(Ty::U64, ICmpOp::Uge);
    check(
        &module,
        &[
            // n == 0: the body still runs once, so *p == a[0] == 7.
            (0, 0, 7),
            // Sized bounds: inside the stored range on the last trip, and past it.
            (3, 4, 7),
            (4, 4, 0),
            (0, 1, 7),
        ],
    );
}

#[test]
fn a_signed_do_while_with_a_negative_bound_loads_its_own_first_store() {
    let module = do_while_module(Ty::I64, ICmpOp::Sge);
    check(
        &module,
        &[
            (0, (-1i64) as u64, 7),
            (0, (-4i64) as u64, 7),
            (0, 0, 7),
            (3, 4, 7),
            (4, 4, 0),
        ],
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
