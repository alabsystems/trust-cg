// trust-cg-codegen - alias-versioned load hoisting under a bound or start that
// two definitions reach
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `loop { a[i] = 7; *out = *p; i += c; if <exit>(i, n) { break } }` where the
//! bound `n` or the start `i` is a value two definitions reach, run through
//! the JIT at every optimization level against a model of the loop:
//!
//!  * `n = flag ? 100 : 4` and `i = flag ? 5 : 0`, each through a diamond
//!    whose arms store to `out` (so it stays a branch, not a `csel`): after
//!    phi lowering the register is written once in each arm;
//!  * `n` a loop-carried value, 100 on entry and 1 on the back edge, with a
//!    stride of 50: written in the preheader and in the latch.
//!
//! The alias-versioned load hoist (O2/O3) sized the store range from whichever
//! definition came last in the layout -- `n = 4`, `n = 1`, or `i = 0` -- so the
//! version check sent a `p` the loop really stores to (a[4], a[50], a[5]) to
//! the clone, which reads `*p` once, before the store. These are executions on
//! this host: tested, not proved.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const ENTRY: &str = "store_then_copy";
/// Elements of `a`: the widest loop stores `a[0..100]`.
const LEN: usize = 128;
/// Where `p` points, as an index into `a`.
const P_INDICES: [usize; 8] = [0, 3, 4, 5, 49, 50, 99, 100];

/// Which value two definitions reach.
#[derive(Clone, Copy, Debug)]
enum Shape {
    /// `n = flag ? 100 : 4`, `i = 0`, stride 1.
    PhiBound,
    /// `n = 4`, `i = flag ? 5 : 0`, stride 1.
    PhiStart,
    /// `n` = 100 on entry and 1 on the back edge, `i = 0`, stride 50.
    CarriedBound,
}

/// The loop's exit test on `step = i + c`.
#[derive(Clone, Copy, Debug)]
enum Exit {
    /// `step >= n` (signed or unsigned, with the index type).
    AtLeast,
    /// `step == n`.
    Equal,
}

/// The index types: `i`, `n` and the step share one.
fn index_types() -> [(Ty, ICmpOp); 4] {
    [
        (Ty::I32, ICmpOp::Sge),
        (Ty::U32, ICmpOp::Uge),
        (Ty::I64, ICmpOp::Sge),
        (Ty::U64, ICmpOp::Uge),
    ]
}

/// `extern "C" fn(a, p, out, flag)`.
type Kernel = extern "C" fn(*mut u64, *const u64, *mut u64, u64);

fn module(shape: Shape, ty: &Ty, exit: ICmpOp) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_alias_hoist_reaching_bound");
    let sig = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::U64], vec![]);
    let mut fb = mb.function(ENTRY, sig);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let p = fb.add_block_param(entry, Ty::Ptr);
    let out = fb.add_block_param(entry, Ty::Ptr);
    let flag = fb.add_block_param(entry, Ty::U64);
    let header = fb.create_block();
    let i = fb.add_block_param(header, ty.clone());
    let carried_n =
        matches!(shape, Shape::CarriedBound).then(|| fb.add_block_param(header, ty.clone()));
    let done = fb.create_block();

    fb.switch_to_block(entry);
    let (start, phi_n) = match shape {
        Shape::PhiBound => {
            let n = branch_pick(&mut fb, ty, flag, out, 100, 4);
            (fb.iconst(ty.clone(), 0), Some(n))
        }
        Shape::PhiStart => (branch_pick(&mut fb, ty, flag, out, 5, 0), None),
        Shape::CarriedBound => (fb.iconst(ty.clone(), 0), None),
    };
    let mut args = vec![start];
    if carried_n.is_some() {
        args.push(fb.iconst(ty.clone(), 100));
    }
    fb.br(header, args);

    fb.switch_to_block(header);
    let slot = fb.gep(Ty::U64, a, vec![i]);
    let seven = fb.iconst(Ty::U64, 7);
    fb.store(Ty::U64, slot, seven);
    let value = fb.load(Ty::U64, p);
    fb.store(Ty::U64, out, value);
    let stride = fb.iconst(ty.clone(), i128::from(stride(shape)));
    let step = fb.binop(BinOp::Add, ty.clone(), i, stride);
    let n = match (phi_n, carried_n) {
        (Some(n), _) | (None, Some(n)) => n,
        (None, None) => fb.iconst(ty.clone(), 4),
    };
    let stop = fb.icmp(exit, ty.clone(), step, n);
    let mut args = vec![step];
    if carried_n.is_some() {
        args.push(fb.iconst(ty.clone(), 1));
    }
    fb.condbr(stop, done, vec![], header, args);

    fb.switch_to_block(done);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `flag != 0 ? when_set : when_clear`, as a diamond whose arms store 1 or 2
/// to `out` (so it stays a branch) and pass their constant to the join, where
/// the builder is left.
fn branch_pick(
    fb: &mut FunctionBuilder<'_>,
    ty: &Ty,
    flag: ValueId,
    out: ValueId,
    when_set: i128,
    when_clear: i128,
) -> ValueId {
    let set = fb.create_block();
    let clear = fb.create_block();
    let join = fb.create_block();
    let picked = fb.add_block_param(join, ty.clone());
    let zero = fb.iconst(Ty::U64, 0);
    let is_set = fb.icmp(ICmpOp::Ne, Ty::U64, flag, zero);
    fb.condbr(is_set, set, vec![], clear, vec![]);
    for (arm, mark, k) in [(set, 1, when_set), (clear, 2, when_clear)] {
        fb.switch_to_block(arm);
        let mark = fb.iconst(Ty::U64, mark);
        fb.store(Ty::U64, out, mark);
        let k = fb.iconst(ty.clone(), k);
        fb.br(join, vec![k]);
    }
    fb.switch_to_block(join);
    picked
}

fn stride(shape: Shape) -> u64 {
    match shape {
        Shape::CarriedBound => 50,
        Shape::PhiBound | Shape::PhiStart => 1,
    }
}

/// What the loop leaves in `a` and `*out` with `p = a + p_index`.
fn model(shape: Shape, exit: Exit, flag: bool, p_index: usize) -> (Vec<u64>, u64) {
    let mut a = vec![0u64; LEN];
    let (mut i, mut n) = match shape {
        Shape::PhiBound => (0, if flag { 100 } else { 4 }),
        Shape::PhiStart => (if flag { 5 } else { 0 }, 4),
        Shape::CarriedBound => (0, 100),
    };
    loop {
        a[i as usize] = 7;
        let out = a[p_index];
        let step = i + stride(shape);
        let stop = match exit {
            Exit::AtLeast => step >= n,
            Exit::Equal => step == n,
        };
        if stop {
            return (a, out);
        }
        i = step;
        if let Shape::CarriedBound = shape {
            n = 1;
        }
    }
}

fn jit(module: &trust_ir::Module, opt_level: OptLevel) -> JitCompilationResult {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
}

/// Run `shape` at every level and index type, compare `a` and `*out` with
/// [`model`] for both `flag` values and every `p` in [`P_INDICES`], and
/// describe the first mismatch of each index type and level.
fn mismatches(shape: Shape, exit: Exit) -> Vec<String> {
    let mut found = Vec::new();
    for (ty, at_least) in index_types() {
        let op = match exit {
            Exit::AtLeast => at_least,
            Exit::Equal => ICmpOp::Eq,
        };
        let module = module(shape, &ty, op);
        for opt_level in LEVELS {
            let result = jit(&module, opt_level);
            // SAFETY: `Kernel` matches the trust-ir signature (three pointers
            // and a u64), and `result` outlives every call.
            let entry = unsafe { result.buffer.get_fn_bound::<Kernel>(ENTRY) }.expect("entry");
            let first = [false, true].into_iter().find_map(|flag| {
                P_INDICES.into_iter().find_map(|p_index| {
                    let (want_a, want_out) = model(shape, exit, flag, p_index);
                    let mut a = vec![0u64; LEN];
                    let mut out = u64::MAX;
                    let base = a.as_mut_ptr();
                    // SAFETY: the loop stores below index 100 < LEN (the
                    // model's walk), and `p_index < LEN`.
                    let p = unsafe { base.add(p_index) };
                    entry.as_ref()(base, p, &mut out, u64::from(flag));
                    (out != want_out || a != want_a).then(|| {
                        format!(
                            "{ty:?} {opt_level:?} flag={} p=a+{p_index}: *out {out}, want {want_out}{}",
                            u8::from(flag),
                            if a == want_a { "" } else { "; a[] differs" },
                        )
                    })
                })
            });
            found.extend(first);
        }
    }
    found
}

/// `n = flag ? 100 : 4`: with `flag = 1` the loop stores `a[0..100]`, so a
/// `p` of `a + 4` reads 7. Sized from the `n = 4` laid out last, the store
/// range `[a, a + 32)` cleared `p` and the clone read 0.
#[test]
fn a_bound_chosen_by_a_branch_sizes_the_store_range_it_takes() {
    assert_eq!(
        mismatches(Shape::PhiBound, Exit::AtLeast),
        Vec::<String>::new()
    );
    assert_eq!(
        mismatches(Shape::PhiBound, Exit::Equal),
        Vec::<String>::new()
    );
}

/// `i = flag ? 5 : 0`, `n = 4`: with `flag = 1` iteration 0 stores `a[5]`
/// and then reads it through `p = a + 5`. Counted from the `i = 0` laid out
/// last, the store range `[a, a + 32)` cleared `p` and the clone read 0.
#[test]
fn a_start_chosen_by_a_branch_is_not_counted_from_zero() {
    assert_eq!(
        mismatches(Shape::PhiStart, Exit::AtLeast),
        Vec::<String>::new()
    );
}

/// `n` 100 on entry and 1 on the back edge, stride 50: the loop stores `a[0]`
/// and `a[50]`, then reads `a[50]` through `p = a + 50`. Sized from the
/// `n = 1` laid out last, the store range `[a, a + 8)` cleared `p` and the
/// clone read 0.
#[test]
fn a_bound_redefined_on_the_back_edge_is_not_sized_from_either_value() {
    assert_eq!(
        mismatches(Shape::CarriedBound, Exit::AtLeast),
        Vec::<String>::new()
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
