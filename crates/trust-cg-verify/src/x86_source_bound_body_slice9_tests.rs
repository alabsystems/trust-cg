// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 9 of the x86-64 source-bound body theorem: acyclic control flow
//! past the slice-6 bounds, stated over the DAG. A several-path source of
//! more than sixteen blocks, more than sixteen entry-to-end paths or a path
//! of more than 256 instructions is admitted block by block and its theorem
//! states each block's observed items under the block's reachability guard
//! and each edge's machine `jcc` literals under the edge's guard, values at
//! a join chosen by the incoming edges' guards (`build_theorem`).
//!
//! Fixtures are real: LIR from the trust-ir adapter, the machine stream from
//! the real x86-64 instruction selector (`super::select`). Every test here
//! runs without a solver (the `x86_source_bound_body::tests::slice9::`
//! library gate); the replay on AY and Clean is in `slice9_qualification`.
//!
//! The central control is the equivalence: on every slice-6 fixture,
//! refutation and variant, and on every slice-9 fixture (whose paths can
//! still be enumerated in a test), the DAG theorem and the slice-6 per-path
//! theorem of the same pair agree at every sampled assignment of their free
//! inputs, matched by what each input stands for
//! (`theorem_with_input_keys`), so the DAG theorem is never weaker.

use super::slice5::describe;
use super::slice6::{
    all_slice_six_shapes, describe_lir, slice_six_refutations, slice_six_variants, slice6_pair,
};
use super::*;
use trust_ir::{BinOp, Constant, ICmpOp, SwitchCase};

/// Slice-9 fixture shapes: each is a several-path source past the slice-6
/// bounds (except [`DagShape::LongChain`], one path past 256 instructions).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DagShape {
    /// Five diamonds in sequence on `x < b`, each arm updating `x`
    /// (`x + i` or `x ^ i`) into its join's parameter: 16 blocks, 32 paths.
    Diamonds5,
    /// Six such diamonds: 19 blocks, 64 paths.
    Diamonds6,
    /// Nine bounds checks `if i + k >= n { panic_at(i + k, n) }` (a call,
    /// then a trap), then `i + 9`: 19 blocks, ten paths.
    GuardChain9,
    /// Three switches in sequence, `match x_s { c_k => acc + 3k + 1, _ =>
    /// acc ^ 5 }` on arguments `x_0`, `x_1`, `x_2` for the four sparse cases
    /// `c_k` of [`SWITCH_CASES`], `acc` from the fourth argument, each
    /// into a join parameter `acc` (four sparse cases: the selector's compare
    /// chain, neither its search tree nor a jump table): 19 blocks, 125 paths.
    SwitchChain,
    /// `match x { c_k => match y { c_j => 4k + j } }` over [`SWITCH_CASES`],
    /// each default returning a constant: 26 blocks, 21 returns.
    SwitchTree,
    /// `if c { x + 1 + 2 + ... + 140 } else { x }`: two paths, one of 281
    /// instructions.
    LongArm,
    /// `x + 1 + 2 + ... + 140`: one path of 282 instructions (the slice 1-5
    /// chain past the old bound).
    LongChain,
    /// An `Option`-like slot pair built on two arms (`(1, x)` or `(0, _)`,
    /// the payload unwritten on one), four diamonds on `b`, then the tag
    /// and the payload plus the diamonds' value returned: 32 paths, merged
    /// slot bytes and an initial frame byte.
    SlotJoin,
    /// Five diamonds whose `then` arm calls `g1(x)` and whose `else` arm
    /// adds `y`: 32 paths, calls on some paths only.
    CallJoin,
    /// Five conditional incoming stores `if x & 2^i != 0 { *p = x + i }`
    /// (void): 32 paths, accesses on some paths only.
    StoreJoin,
    /// Five diamonds on `d` toggling a `bool` accumulator (`acc ^ d` or
    /// `acc`), `bool`s in and out (the clean-bool walk): 32 paths.
    BoolDag,
    /// A loaded value compared against `x` in five diamonds, a second load
    /// on one arm of each: 32 paths with incoming loads on some.
    LoadDag,
    /// Nested ifs five deep on independent argument bits, each leaf
    /// returning its own constant: 63 blocks, 32 returns.
    NestedTree,
    /// `if c_i { tick() }` for five `bool` parameters, a void function: 16
    /// blocks, 32 paths, observed only through which calls run.
    CallChain5,
    /// Five diamonds on `bool` parameters, `acc ^ k_i` or `acc`, `acc` from
    /// a `u64`: 16 blocks, 32 paths of cheap arithmetic.
    XorChain5,
}

/// The sparse case values of the switch fixtures (contiguous ones make a
/// jump table, which no slice admits).
const SWITCH_CASES: [i128; 4] = [1, 9, 33, 70];

/// Every slice-9 fixture shape.
pub(crate) const SLICE_NINE: [DagShape; 15] = [
    DagShape::Diamonds5,
    DagShape::Diamonds6,
    DagShape::GuardChain9,
    DagShape::SwitchChain,
    DagShape::SwitchTree,
    DagShape::LongArm,
    DagShape::LongChain,
    DagShape::SlotJoin,
    DagShape::CallJoin,
    DagShape::StoreJoin,
    DagShape::BoolDag,
    DagShape::LoadDag,
    DagShape::NestedTree,
    DagShape::CallChain5,
    DagShape::XorChain5,
];

impl DagShape {
    fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s9_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }
}

/// The LIR the trust-ir adapter produces for a slice-9 shape.
pub(crate) fn slice9_lir(shape: DagShape) -> Function {
    use DagShape::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice9");
    let mut declare = |name: &str, params: Vec<Ty>, results: Vec<Ty>| {
        let ty = builder.add_func_type(params, results);
        builder.declare_function(name, ty)
    };
    let g1 = declare("g1", vec![Ty::U64], vec![Ty::U64]);
    let tick = declare("tick", vec![], vec![]);
    let panic = declare("panic_at", vec![Ty::U64, Ty::U64], vec![]);
    let ptr = Ty::PtrMut(Box::new(Ty::U64));
    let (params, results): (Vec<Ty>, Vec<Ty>) = match shape {
        Diamonds5 | Diamonds6 | GuardChain9 | CallJoin => (vec![Ty::U64, Ty::U64], vec![Ty::U64]),
        LongChain => (vec![Ty::U64], vec![Ty::U64]),
        SwitchChain => (vec![Ty::U64, Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]),
        SwitchTree => (vec![Ty::U64, Ty::U64], vec![Ty::U64]),
        LongArm => (vec![Ty::U64, Ty::Bool], vec![Ty::U64]),
        SlotJoin => (vec![Ty::U64, Ty::Bool, Ty::U64], vec![Ty::U64, Ty::U64]),
        StoreJoin => (vec![ptr.clone(), Ty::U64], vec![]),
        BoolDag => (vec![Ty::Bool, Ty::Bool], vec![Ty::Bool]),
        LoadDag => (vec![ptr.clone(), Ty::U64], vec![Ty::U64]),
        NestedTree => (vec![Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]),
        CallChain5 => (vec![Ty::Bool; 5], vec![]),
        XorChain5 => (
            vec![Ty::U64, Ty::Bool, Ty::Bool, Ty::Bool, Ty::Bool, Ty::Bool],
            vec![Ty::U64],
        ),
    };
    let signature = builder.add_func_type(params.clone(), results.clone());
    let mut f = builder.function(shape.name(), signature);
    let entry = f.create_block();
    let args: Vec<_> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    // A diamond on `test` from the current block: `then` computes one value
    // and `else` another into the join's parameter; returns the parameter,
    // with the join current.
    fn diamond(
        f: &mut trust_ir_build::FunctionBuilder<'_>,
        test: trust_ir::value::ValueId,
        ty: Ty,
        then_value: &mut dyn FnMut(
            &mut trust_ir_build::FunctionBuilder<'_>,
        ) -> trust_ir::value::ValueId,
        else_value: &mut dyn FnMut(
            &mut trust_ir_build::FunctionBuilder<'_>,
        ) -> trust_ir::value::ValueId,
    ) -> trust_ir::value::ValueId {
        let (then, other, join) = (f.create_block(), f.create_block(), f.create_block());
        let result = f.add_block_param(join, ty);
        f.condbr(test, then, vec![], other, vec![]);
        f.switch_to_block(then);
        let value = then_value(f);
        f.br(join, vec![value]);
        f.switch_to_block(other);
        let value = else_value(f);
        f.br(join, vec![value]);
        f.switch_to_block(join);
        result
    }
    match shape {
        Diamonds5 | Diamonds6 => {
            let count = if shape == Diamonds5 { 5 } else { 6 };
            let mut x = args[0];
            for i in 1..=count {
                let test = f.icmp(ICmpOp::Ult, Ty::U64, x, args[1]);
                let current = x;
                x = diamond(
                    &mut f,
                    test,
                    Ty::U64,
                    &mut |f| {
                        let k = f.iconst(Ty::U64, i);
                        f.add(Ty::U64, current, k)
                    },
                    &mut |f| {
                        let k = f.iconst(Ty::U64, i);
                        f.binop(BinOp::Xor, Ty::U64, current, k)
                    },
                );
            }
            f.ret(vec![x]);
        }
        GuardChain9 => {
            for k in 0..9 {
                let (fail, ok) = (f.create_block(), f.create_block());
                let offset = f.iconst(Ty::U64, k);
                let index = f.add(Ty::U64, args[0], offset);
                let test = f.icmp(ICmpOp::Uge, Ty::U64, index, args[1]);
                f.condbr(test, fail, vec![], ok, vec![]);
                f.switch_to_block(fail);
                f.call_void(panic, vec![index, args[1]]);
                f.unreachable();
                f.switch_to_block(ok);
            }
            let nine = f.iconst(Ty::U64, 9);
            let last = f.add(Ty::U64, args[0], nine);
            f.ret(vec![last]);
        }
        SwitchChain => {
            let mut acc = args[3];
            for &selector in args.iter().take(3) {
                let targets: Vec<_> = (0..4).map(|_| f.create_block()).collect();
                let (default, join) = (f.create_block(), f.create_block());
                let result = f.add_block_param(join, Ty::U64);
                f.switch(
                    selector,
                    targets
                        .iter()
                        .enumerate()
                        .map(|(k, target)| SwitchCase {
                            value: Constant::Int(SWITCH_CASES[k]),
                            target: *target,
                            args: vec![],
                        })
                        .collect(),
                    default,
                    vec![],
                );
                for (k, target) in targets.iter().enumerate() {
                    f.switch_to_block(*target);
                    let constant = f.iconst(Ty::U64, 3 * k as i128 + 1);
                    let value = f.add(Ty::U64, acc, constant);
                    f.br(join, vec![value]);
                }
                f.switch_to_block(default);
                let five = f.iconst(Ty::U64, 5);
                let value = f.binop(BinOp::Xor, Ty::U64, acc, five);
                f.br(join, vec![value]);
                f.switch_to_block(join);
                acc = result;
            }
            f.ret(vec![acc]);
        }
        SwitchTree => {
            let outer: Vec<_> = (0..4).map(|_| f.create_block()).collect();
            let outer_default = f.create_block();
            let cases = |targets: &[trust_ir::value::BlockId]| -> Vec<SwitchCase> {
                targets
                    .iter()
                    .enumerate()
                    .map(|(k, target)| SwitchCase {
                        value: Constant::Int(SWITCH_CASES[k]),
                        target: *target,
                        args: vec![],
                    })
                    .collect()
            };
            f.switch(args[0], cases(&outer), outer_default, vec![]);
            for (k, block) in outer.iter().enumerate() {
                f.switch_to_block(*block);
                let inner: Vec<_> = (0..4).map(|_| f.create_block()).collect();
                let inner_default = f.create_block();
                f.switch(args[1], cases(&inner), inner_default, vec![]);
                for (j, leaf) in inner.iter().enumerate() {
                    f.switch_to_block(*leaf);
                    let value = f.iconst(Ty::U64, 4 * k as i128 + j as i128);
                    f.ret(vec![value]);
                }
                f.switch_to_block(inner_default);
                let value = f.iconst(Ty::U64, 100 + k as i128);
                f.ret(vec![value]);
            }
            f.switch_to_block(outer_default);
            let value = f.iconst(Ty::U64, 200);
            f.ret(vec![value]);
        }
        LongArm => {
            let x = args[0];
            let result = diamond(
                &mut f,
                args[1],
                Ty::U64,
                &mut |f| {
                    let mut value = x;
                    for k in 1..=140 {
                        let constant = f.iconst(Ty::U64, k);
                        value = f.add(Ty::U64, value, constant);
                    }
                    value
                },
                &mut |_| x,
            );
            f.ret(vec![result]);
        }
        LongChain => {
            let mut value = args[0];
            for k in 1..=140 {
                let constant = f.iconst(Ty::U64, k);
                value = f.add(Ty::U64, value, constant);
            }
            f.ret(vec![value]);
        }
        SlotJoin => {
            let (some, none, built) = (f.create_block(), f.create_block(), f.create_block());
            let tag = f.alloca(Ty::U64);
            let payload = f.alloca(Ty::U64);
            f.condbr(args[1], some, vec![], none, vec![]);
            f.switch_to_block(some);
            let one = f.iconst(Ty::U64, 1);
            f.store(Ty::U64, tag, one);
            f.store(Ty::U64, payload, args[0]);
            f.br(built, vec![]);
            f.switch_to_block(none);
            let zero = f.iconst(Ty::U64, 0);
            f.store(Ty::U64, tag, zero);
            f.br(built, vec![]);
            f.switch_to_block(built);
            let mut acc = args[2];
            for i in 1..=4 {
                let k = f.iconst(Ty::U64, 1 << i);
                let bit = f.binop(BinOp::And, Ty::U64, args[2], k);
                let zero = f.iconst(Ty::U64, 0);
                let test = f.icmp(ICmpOp::Ne, Ty::U64, bit, zero);
                let current = acc;
                acc = diamond(
                    &mut f,
                    test,
                    Ty::U64,
                    &mut |f| {
                        let k = f.iconst(Ty::U64, i);
                        f.add(Ty::U64, current, k)
                    },
                    &mut |_| current,
                );
            }
            let tag = f.load(Ty::U64, tag);
            let payload = f.load(Ty::U64, payload);
            let total = f.add(Ty::U64, payload, acc);
            f.ret(vec![tag, total]);
        }
        CallJoin => {
            let mut x = args[0];
            for i in 1..=5 {
                let k = f.iconst(Ty::U64, i * 10);
                let test = f.icmp(ICmpOp::Ult, Ty::U64, x, k);
                let current = x;
                x = diamond(
                    &mut f,
                    test,
                    Ty::U64,
                    &mut |f| f.call(g1, vec![current]),
                    &mut |f| f.add(Ty::U64, current, args[1]),
                );
            }
            f.ret(vec![x]);
        }
        StoreJoin => {
            for i in 0..5 {
                let (store, done) = (f.create_block(), f.create_block());
                let k = f.iconst(Ty::U64, 1 << i);
                let bit = f.binop(BinOp::And, Ty::U64, args[1], k);
                let zero = f.iconst(Ty::U64, 0);
                let test = f.icmp(ICmpOp::Ne, Ty::U64, bit, zero);
                f.condbr(test, store, vec![], done, vec![]);
                f.switch_to_block(store);
                let offset = f.iconst(Ty::U64, i);
                let value = f.add(Ty::U64, args[1], offset);
                f.store(Ty::U64, args[0], value);
                f.br(done, vec![]);
                f.switch_to_block(done);
            }
            f.ret(vec![]);
        }
        BoolDag => {
            let mut acc = args[0];
            for _ in 0..5 {
                let current = acc;
                let d = args[1];
                acc = diamond(
                    &mut f,
                    d,
                    Ty::Bool,
                    &mut |f| f.binop(BinOp::Xor, Ty::Bool, current, d),
                    &mut |_| current,
                );
                // Flip the next diamond's input through the accumulator.
                let flipped = f.binop(BinOp::Xor, Ty::Bool, acc, d);
                acc = flipped;
            }
            f.ret(vec![acc]);
        }
        LoadDag => {
            let loaded = f.load(Ty::U64, args[0]);
            let mut acc = loaded;
            for i in 1..=5 {
                let k = f.iconst(Ty::U64, i);
                let shifted = f.add(Ty::U64, args[1], k);
                let test = f.icmp(ICmpOp::Ult, Ty::U64, acc, shifted);
                let current = acc;
                let pointer = args[0];
                acc = diamond(
                    &mut f,
                    test,
                    Ty::U64,
                    &mut |f| {
                        let again = f.load(Ty::U64, pointer);
                        f.add(Ty::U64, current, again)
                    },
                    &mut |f| {
                        let k = f.iconst(Ty::U64, i);
                        f.sub(Ty::U64, current, k)
                    },
                );
            }
            f.ret(vec![acc]);
        }
        NestedTree => {
            // A complete binary tree of tests five deep: the test at depth
            // `d` is bit `d` of argument `d % 3` (independent bits: every
            // path is feasible); the leaves return their own index.
            fn tree(
                f: &mut trust_ir_build::FunctionBuilder<'_>,
                args: &[trust_ir::value::ValueId],
                depth: i128,
                index: i128,
            ) {
                if depth == 5 {
                    let value = f.iconst(Ty::U64, index);
                    f.ret(vec![value]);
                    return;
                }
                let (then, other) = (f.create_block(), f.create_block());
                let mask = f.iconst(Ty::U64, 1 << depth);
                let bit = f.binop(BinOp::And, Ty::U64, args[(depth % 3) as usize], mask);
                let zero = f.iconst(Ty::U64, 0);
                let test = f.icmp(ICmpOp::Ne, Ty::U64, bit, zero);
                f.condbr(test, then, vec![], other, vec![]);
                f.switch_to_block(then);
                tree(f, args, depth + 1, 2 * index);
                f.switch_to_block(other);
                tree(f, args, depth + 1, 2 * index + 1);
            }
            tree(&mut f, &args, 0, 0);
        }
        CallChain5 => {
            for c in args.iter().copied() {
                let (call, done) = (f.create_block(), f.create_block());
                f.condbr(c, call, vec![], done, vec![]);
                f.switch_to_block(call);
                f.call_void(tick, vec![]);
                f.br(done, vec![]);
                f.switch_to_block(done);
            }
            f.ret(vec![]);
        }
        XorChain5 => {
            let mut acc = args[0];
            for (i, c) in args[1..].iter().copied().enumerate() {
                let current = acc;
                acc = diamond(
                    &mut f,
                    c,
                    Ty::U64,
                    &mut |f| {
                        let k = f.iconst(Ty::U64, 1 << (8 * i));
                        f.binop(BinOp::Xor, Ty::U64, current, k)
                    },
                    &mut |_| current,
                );
            }
            f.ret(vec![acc]);
        }
    }
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{shape:?}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == shape.name())
    .unwrap_or_else(|| panic!("{shape:?}: no translated function"))
}

pub(crate) fn slice9_pair(shape: DagShape) -> (Function, X86ISelFunction) {
    let source = slice9_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

// ---------------------------------------------------------------------------
// The solver-free sampler
// ---------------------------------------------------------------------------

/// Random samples before the constant-driven ones.
const RANDOM_SAMPLES: u64 = 384;

/// Every bitvector constant the obligation mentions, and 0.
fn constants_of(obligation: &ProofObligation) -> Vec<u64> {
    fn walk(expr: &E, constants: &mut Vec<u64>) {
        if let E::BvConst { value, .. } = expr
            && !constants.contains(value)
        {
            constants.push(*value);
        }
        expr.for_each_child(&mut |child| walk(child, constants));
    }
    let mut constants = vec![0];
    for expr in [&obligation.trust_ir_expr, &obligation.aarch64_expr]
        .into_iter()
        .chain(&obligation.preconditions)
    {
        walk(expr, &mut constants);
    }
    constants
}

/// Whether sample `seed` zeroes byte `byte` of every input: the samples at
/// `6k + 3` zero the bytes on one side of a boundary that steps through
/// every byte of a word (structured partial zeroing: a zero tag beside a
/// nonzero payload, a value whose low or high bytes are zero), never all at
/// once.
fn zeroed_byte(seed: u64, byte: u32) -> bool {
    if seed % 6 != 3 {
        return false;
    }
    let k = seed / 6;
    let boundary = (k % 9) as u32;
    if (k / 9).is_multiple_of(2) {
        byte < boundary
    } else {
        byte >= boundary
    }
}

fn splitmix(mut z: u64) -> u64 {
    z = z.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn key_hash(key: &str) -> u64 {
    key.bytes().fold(0xcbf2_9ce4_8422_2325, |h, b| {
        (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3)
    })
}

/// The rank of an input in the constant phase of the sampler: the argument
/// registers in System V order (0 to 5), every other input 6. A function of
/// the key alone.
fn constant_rank(key: &str) -> usize {
    ["e_rdi", "e_rsi", "e_rdx", "e_rcx", "e_r8", "e_r9"]
        .iter()
        .position(|name| *name == key)
        .unwrap_or(6)
}

/// The least stride from `start` on that is coprime with `n`: `n`
/// consecutive multiples of it visit every residue modulo `n` once.
fn coprime_stride(start: usize, n: usize) -> usize {
    fn gcd(a: usize, b: usize) -> usize {
        if b == 0 { a } else { gcd(b, a % b) }
    }
    (start..)
        .find(|stride| gcd(*stride, n) == 1)
        .expect("a stride coprime with n")
}

/// The value sample `seed` gives the input `key` of `width` bits: random
/// words, small values, zero, one input nonzero, structured partial zeroing
/// ([`zeroed_byte`]), and past [`RANDOM_SAMPLES`] the theorem's constants
/// and their neighbours (a switch case, a compared constant): first every
/// input takes every constant and neighbour (`3n` samples, each input at its
/// own stride coprime with `n`), then every pair of them for the first two
/// argument registers and a cycling choice for every other input. A function
/// of the key, so two encodings' inputs that stand for the same thing get
/// the same value.
fn sample_value(seed: u64, key: &str, width: u32, constants: &[u64]) -> u64 {
    let state = splitmix(seed ^ splitmix(key_hash(key)));
    let mut value = match seed.checked_sub(RANDOM_SAMPLES) {
        Some(k) => {
            let (k, n) = (k as usize, constants.len());
            let rank = constant_rank(key);
            let offset = if rank == 0 {
                0
            } else {
                key_hash(key) as usize % n
            };
            // A stride a multiple of `n` shares a factor with would visit
            // only some constants (a third switch's case missed when five
            // divides `n`): every stride is coprime with `n`.
            let stride = coprime_stride(2 * rank + 1, n);
            let (index, neighbour) = match k.checked_sub(3 * n) {
                None => ((k * stride + offset) % n, k / n),
                Some(k) => match rank {
                    0 => (k % n, (k / (n * n)) % 3),
                    1 => ((k / n) % n, (k / (n * n)) % 3),
                    _ => ((k * stride + offset) % n, (k / n) % 3),
                },
            };
            let constant = constants[index];
            match neighbour {
                0 => constant,
                1 => constant.wrapping_add(1),
                _ => constant.wrapping_sub(1),
            }
        }
        None => match seed % 6 {
            0 => 0,
            1 => (state >> 29) % 12,
            2 => (state >> 17) & 0xff,
            4 if key_hash(key) % 5 != seed % 5 => 0,
            _ => state,
        },
    };
    // Structured partial zeroing in the random phase only: the constant phase
    // must keep each constant whole.
    for byte in 0..width.div_ceil(8) {
        if seed < RANDOM_SAMPLES && zeroed_byte(seed, byte) {
            value &= !(0xffu64 << (8 * byte));
        }
    }
    crate::smt::mask(value, width)
}

/// The number of samples a theorem is judged at: the random ones, then the
/// constant phase (every constant and neighbour at every input, then every
/// pair of them for the first two argument registers, at most
/// [`CONSTANT_SAMPLES`]).
fn samples(obligation: &ProofObligation) -> u64 {
    samples_for(constants_of(obligation).len())
}

const CONSTANT_SAMPLES: u64 = 3000;

fn samples_for(constants: usize) -> u64 {
    let n = constants as u64;
    RANDOM_SAMPLES + 3 * n + (3 * n * n).clamp(18 * n, CONSTANT_SAMPLES.max(18 * n))
}

/// Evaluate a theorem at sample `seed`, its free inputs keyed by `key` (the
/// premises are definitional): whether its two sides agree.
fn evaluate_keyed(
    obligation: &ProofObligation,
    key: &dyn Fn(&str) -> String,
    seed: u64,
    constants: &[u64],
) -> bool {
    use crate::smt::{EvalEnv, EvalResult};
    let mut env = EvalEnv::default();
    for (name, width) in free_inputs_of(obligation) {
        let value = sample_value(seed, &key(&name), width, constants);
        env.insert(name, value);
    }
    for premise in obligation.preconditions.iter().rev() {
        let E::Eq { lhs, rhs } = premise else {
            panic!("premise {premise} is not an equation")
        };
        let E::Var { name, .. } = lhs.as_ref() else {
            panic!("premise {premise} defines no name")
        };
        let EvalResult::Bv(value) = rhs.eval(&env) else {
            panic!("definition of {name} is not a bitvector")
        };
        env.insert(name.clone(), value);
    }
    obligation.trust_ir_expr.eval(&env) == obligation.aarch64_expr.eval(&env)
}

/// Whether a theorem holds at every sample (inputs keyed by name).
pub(crate) fn dag_holds_on_samples(obligation: &ProofObligation) -> bool {
    let constants = constants_of(obligation);
    (0..samples(obligation))
        .all(|seed| evaluate_keyed(obligation, &|name| name.to_owned(), seed, &constants))
}

/// Whether some sample refutes a theorem (inputs keyed by name).
pub(crate) fn dag_refuted_on_samples(obligation: &ProofObligation) -> bool {
    let constants = constants_of(obligation);
    (0..samples(obligation))
        .any(|seed| !evaluate_keyed(obligation, &|name| name.to_owned(), seed, &constants))
}

/// The DAG encoding and the slice-6 path encoding of one pair, by name.
const DAG: PathEncoding = PathEncoding {
    dag: Some(true),
    ..PathEncoding::CANONICAL
};
const PATHS: PathEncoding = PathEncoding {
    dag: Some(false),
    ..PathEncoding::CANONICAL
};

/// The DAG theorem and the path theorem of one pair agree at every sample,
/// their inputs matched by what each stands for. Returns how many samples
/// refuted both (a wrong lowering refuted alike), for the caller's check.
#[track_caller]
fn assert_encodings_agree(source: &Function, machine: &X86ISelFunction, what: &str) -> usize {
    let (paths, path_keys) = theorem_with_input_keys(source, machine, SYSV, PATHS)
        .unwrap_or_else(|refusal| panic!("{what}: paths: {refusal}\n{}", describe(machine)));
    let (dag, dag_keys) = theorem_with_input_keys(source, machine, SYSV, DAG)
        .unwrap_or_else(|refusal| panic!("{what}: DAG: {refusal}\n{}", describe(machine)));
    let mut constants = constants_of(&paths);
    for constant in constants_of(&dag) {
        if !constants.contains(&constant) {
            constants.push(constant);
        }
    }
    let path_key = |name: &str| path_keys[name].clone();
    let dag_key = |name: &str| dag_keys[name].clone();
    let mut refuted = 0;
    for seed in 0..samples_for(constants.len()) {
        let by_paths = evaluate_keyed(&paths, &path_key, seed, &constants);
        let by_dag = evaluate_keyed(&dag, &dag_key, seed, &constants);
        assert_eq!(
            by_paths,
            by_dag,
            "{what}: the DAG and path theorems disagree at sample {seed}\n{}{}",
            describe_lir(source),
            describe(machine)
        );
        refuted += usize::from(!by_paths);
    }
    refuted
}

#[track_caller]
fn owner(source: &Function, machine: &X86ISelFunction, what: &str) -> ProofObligation {
    source_bound_x86_body(source, machine, SYSV)
        .unwrap_or_else(|refusal| {
            panic!(
                "{what}: {refusal}\n{}{}",
                describe_lir(source),
                describe(machine)
            )
        })
        .obligation()
        .clone()
}

/// Every slice-9 fixture's theorem is stated inlined, never in its fallback
/// spelling: a claim equation that substitution makes an identity is
/// dropped, not kept (kept, it fails the structural check and the theorem
/// falls back to the uninlined spelling, which on the qualification host
/// certified none of the 62 uncertified bodies the census newly bound). No
/// claim of it, nor of a guarded claim's conjuncts, is an identity.
#[test]
fn every_slice_nine_theorem_is_inlined_without_identities() {
    const PLAIN: PathEncoding = PathEncoding {
        inline_single_use: false,
        value_number: ValueNumbering::Off,
        ..PathEncoding::CANONICAL
    };
    let identity = |term: &E| matches!(term, E::Eq { lhs, rhs } if lhs == rhs);
    for shape in SLICE_NINE {
        let what = format!("{shape:?}");
        let (source, machine) = slice9_pair(shape);
        let canonical = owner(&source, &machine, &what);
        let plain = theorem_with_path_encoding(&source, &machine, SYSV, PLAIN)
            .unwrap_or_else(|refusal| panic!("{what}: {refusal}"));
        if canonical.trust_ir_expr != E::bool_const(true) {
            // One equation (the long chain's returned sum): substitution
            // makes its two sides one term, which the structural check
            // refuses, so it keeps the uninlined spelling.
            assert_eq!(shape, DagShape::LongChain, "{what}: one equation");
            assert_eq!(canonical, plain, "{what}: the fallback spelling");
            continue;
        }
        assert!(
            canonical.preconditions.len() < plain.preconditions.len(),
            "{what}: the theorem is not inlined ({} definitions, {} uninlined)",
            canonical.preconditions.len(),
            plain.preconditions.len()
        );
        for claim in conjuncts(&canonical.aarch64_expr) {
            let terms = match claim {
                E::Or { rhs, .. } => conjuncts(rhs),
                other => vec![other],
            };
            assert!(
                !terms.into_iter().any(identity),
                "{what}: an identity claim in {claim}"
            );
        }
    }
}

/// The constant phase gives every input every constant and neighbour,
/// whatever the number of constants. With a fixed stride of `2 rank + 1`,
/// the third argument register (stride five) visited only a fifth of the
/// constants of a theorem with a multiple of five of them, and the sampler
/// missed a third switch's case compared against the wrong constant (the
/// slice-9 mutation probe); every stride is now coprime with the count.
#[test]
fn the_sampler_gives_every_input_every_constant() {
    for n in 1..=64usize {
        let constants: Vec<u64> = (0..n as u64).map(|c| 1000 * c + 500).collect();
        for key in [
            "e_rdi", "e_rsi", "e_rdx", "e_rcx", "e_r8", "e_r9", "c3", "m0_k1",
        ] {
            let seen: std::collections::HashSet<u64> = (RANDOM_SAMPLES..samples_for(n))
                .map(|seed| sample_value(seed, key, 64, &constants))
                .collect();
            for constant in &constants {
                for value in [*constant, constant + 1, constant - 1] {
                    assert!(
                        seen.contains(&value),
                        "{n} constants, input {key}: {value} never sampled"
                    );
                }
            }
        }
    }
}

/// A wrong lowering is never credited: the owner names a mismatch, makes no
/// claim, or builds a theorem the sampler refutes.
#[track_caller]
fn never_credited(source: &Function, machine: &X86ISelFunction, what: &str) -> &'static str {
    let verdict = source_bound_x86_body(source, machine, SYSV);
    if let Err(refusal) = &verdict {
        eprintln!("{what}: {refusal}");
    }
    match verdict {
        Ok(owner) => {
            assert!(
                dag_refuted_on_samples(owner.obligation()),
                "{what}: a wrong lowering's theorem holds on samples\n{}",
                describe(machine)
            );
            "refuted"
        }
        Err(X86BodyRefusal::Mismatch(_)) => "mismatch",
        Err(X86BodyRefusal::Unsupported(_)) => "no claim",
    }
}

// ---------------------------------------------------------------------------
// Construction (no solver)
// ---------------------------------------------------------------------------

/// Every slice-9 fixture is stated over its DAG (except the one-path chain),
/// the owner builds its theorem and covers every value row, and the
/// theorem's size is linear in the blocks: one guarded claim per block with
/// items and one per conditional edge, never one per path.
#[test]
fn owner_builds_every_slice_nine_shape_over_its_dag() {
    for shape in SLICE_NINE {
        let (source, machine) = slice9_pair(shape);
        let text = format!("{shape:?}\n{}{}", describe_lir(&source), describe(&machine));
        let body = admitted_body(&source).unwrap_or_else(|refusal| panic!("{text}{refusal}"));
        let cfg = source_cfg(&source).unwrap();
        assert!(!cfg.per_path() || shape == DagShape::LongChain, "{text}");
        assert_eq!(body.dag.is_some(), shape != DagShape::LongChain, "{text}");
        let owner = source_bound_x86_body(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{text}{refusal}"));
        let entries = free_inputs_of(owner.obligation());
        assert_eq!(
            owner_check(&source, &machine, owner.obligation(), &entries),
            Ok(()),
            "{text}"
        );
        assert!(owner.obligation().is_genuinely_proven(), "{text}");
        // Every value row is covered (every row but control, calls and
        // `nop`s).
        let covered: HashSet<usize> = owner.bound_rows().iter().copied().collect();
        for (ordinal, _, _) in rows(&machine) {
            let row = inst(&machine, ordinal);
            if matches!(
                row.opcode,
                X86Opcode::Jmp | X86Opcode::Ret | X86Opcode::Ud2 | X86Opcode::Call | X86Opcode::Nop
            ) {
                continue;
            }
            assert!(covered.contains(&ordinal), "{text}row {ordinal} uncovered");
        }
        if let Some(dag) = &body.dag {
            let conditional = dag
                .order
                .iter()
                .map(|block| dag.blocks[block].branches.len())
                .sum::<usize>();
            // Guarded claims: one per block with items and one per edge of a
            // conditional block (the entry block's items are unguarded
            // equations).
            let claims = conjuncts(&owner.obligation().aarch64_expr)
                .into_iter()
                .filter(|claim| matches!(claim, E::Or { .. }))
                .count();
            assert!(
                claims <= dag.order.len() + conditional,
                "{shape:?}: {claims} claims for {} blocks and {conditional} conditional edges",
                dag.order.len()
            );
        }
    }
}

/// The top-level conjuncts of a right-nested conjunction.
fn conjuncts(expr: &E) -> Vec<&E> {
    let mut terms = Vec::new();
    let mut rest = expr;
    loop {
        match rest {
            E::And { lhs, rhs } => {
                terms.push(lhs.as_ref());
                rest = rhs.as_ref();
            }
            last => {
                terms.push(last);
                return terms;
            }
        }
    }
}

#[test]
fn slice_nine_theorems_hold_on_samples() {
    for shape in SLICE_NINE {
        let (source, machine) = slice9_pair(shape);
        let obligation = owner(&source, &machine, &format!("{shape:?}"));
        assert!(
            dag_holds_on_samples(&obligation),
            "{shape:?}\n{}{}",
            describe_lir(&source),
            describe(&machine)
        );
    }
}

/// Every guard of a DAG theorem holds at some sample: the samples reach
/// every block and take every edge, so a claim is never judged vacuously.
#[test]
fn the_samples_reach_every_block_and_edge() {
    use crate::smt::{EvalEnv, EvalResult};
    for shape in SLICE_NINE {
        if shape == DagShape::LongChain {
            continue;
        }
        let (source, machine) = slice9_pair(shape);
        let obligation = owner(&source, &machine, &format!("{shape:?}"));
        let constants = constants_of(&obligation);
        let guards: Vec<&E> = conjuncts(&obligation.aarch64_expr)
            .into_iter()
            .filter_map(|claim| match claim {
                E::Or { lhs, .. } => match lhs.as_ref() {
                    E::Not { operand } => Some(operand.as_ref()),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        let mut reached = vec![false; guards.len()];
        for seed in 0..samples(&obligation) {
            let mut env = EvalEnv::default();
            for (name, width) in free_inputs_of(&obligation) {
                env.insert(name.clone(), sample_value(seed, &name, width, &constants));
            }
            for premise in obligation.preconditions.iter().rev() {
                let E::Eq { lhs, rhs } = premise else {
                    unreachable!()
                };
                let E::Var { name, .. } = lhs.as_ref() else {
                    unreachable!()
                };
                let EvalResult::Bv(value) = rhs.eval(&env) else {
                    unreachable!()
                };
                env.insert(name.clone(), value);
            }
            for (seen, guard) in reached.iter_mut().zip(&guards) {
                *seen |= matches!(guard.eval(&env), EvalResult::Bool(true));
            }
        }
        let unreached: Vec<String> = reached
            .iter()
            .zip(&guards)
            .filter(|(seen, _)| !**seen)
            .map(|(_, guard)| guard.to_string().chars().take(300).collect())
            .collect();
        assert!(
            unreached.is_empty(),
            "{shape:?}: some guard never holds ({} of {}): {unreached:#?}",
            reached.iter().filter(|seen| **seen).count(),
            reached.len()
        );
    }
}

/// THE equivalence: on every slice-6 fixture, every slice-6 refutation and
/// variant, and every slice-9 fixture, the DAG theorem and the per-path
/// theorem of the same pair agree at every sample, so the DAG theorem
/// states exactly the per-path conjunction; and each slice-6 refutation is
/// refuted by both.
#[test]
fn the_dag_theorem_is_equivalent_to_the_path_claims() {
    for shape in all_slice_six_shapes() {
        let (source, machine) = slice6_pair(shape);
        if source_cfg(&source).unwrap().paths == 1 {
            continue;
        }
        assert_eq!(
            assert_encodings_agree(&source, &machine, &format!("{shape:?}")),
            0,
            "{shape:?}: a correct lowering is refuted"
        );
    }
    for (label, source, machine) in slice_six_variants() {
        if source_cfg(&source).unwrap().paths == 1 {
            continue;
        }
        assert_encodings_agree(&source, &machine, &label);
    }
    for (label, source, machine) in slice_six_refutations() {
        if source_cfg(&source).unwrap().paths == 1 {
            continue;
        }
        assert!(
            assert_encodings_agree(&source, &machine, label) > 0,
            "{label}: the wrong lowering is refuted by neither encoding"
        );
    }
    for shape in SLICE_NINE {
        if shape == DagShape::LongChain {
            continue;
        }
        let (source, machine) = slice9_pair(shape);
        assert_eq!(
            assert_encodings_agree(&source, &machine, &format!("{shape:?}")),
            0,
            "{shape:?}: a correct lowering is refuted"
        );
    }
    for (label, source, machine) in slice_nine_refutations() {
        assert_encodings_agree(&source, &machine, label);
    }
}

// ---------------------------------------------------------------------------
// Negative controls
// ---------------------------------------------------------------------------

fn set_condition(machine: &mut X86ISelFunction, ordinal: usize, cc: trust_cg_ir::X86CondCode) {
    let row = inst_mut(machine, ordinal);
    let index = usize::from(row.opcode == X86Opcode::Setcc);
    row.operands[index] = O::CondCode(cc);
}

fn condition(machine: &X86ISelFunction, ordinal: usize) -> trust_cg_ir::X86CondCode {
    let O::CondCode(cc) = inst(machine, ordinal).operands[0] else {
        panic!("row {ordinal} is no Jcc")
    };
    cc
}

/// The opposite x86 condition code.
fn inverse(cc: trust_cg_ir::X86CondCode) -> trust_cg_ir::X86CondCode {
    use trust_cg_ir::X86CondCode as C;
    match cc {
        C::E => C::NE,
        C::NE => C::E,
        C::B => C::AE,
        C::AE => C::B,
        C::BE => C::A,
        C::A => C::BE,
        C::L => C::GE,
        C::GE => C::L,
        C::LE => C::G,
        C::G => C::LE,
        C::S => C::NS,
        C::NS => C::S,
        C::O => C::NO,
        C::NO => C::O,
        C::P => C::NP,
        C::NP => C::P,
    }
}

/// The block holding walk ordinal `ordinal`.
fn block_of(machine: &X86ISelFunction, ordinal: usize) -> Block {
    rows(machine)[ordinal].1
}

/// The walk ordinal of the `n`-th row with `opcode`.
fn nth(machine: &X86ISelFunction, opcode: X86Opcode, n: usize) -> usize {
    find(machine, opcode)
        .get(n)
        .copied()
        .unwrap_or_else(|| panic!("no {opcode:?} #{n}\n{}", describe(machine)))
}

/// The arms' copies into join parameters (a `MovRR`/`MovRR32` that is the
/// row before its block's final `Jmp`), in walk order.
fn join_copies(machine: &X86ISelFunction) -> Vec<usize> {
    rows(machine)
        .into_iter()
        .filter(|(_, block, index)| {
            let body = &machine.blocks[block].insts;
            index + 2 == body.len()
                && matches!(body[*index].opcode, X86Opcode::MovRR | X86Opcode::MovRR32)
                && body[index + 1].opcode == X86Opcode::Jmp
        })
        .map(|(ordinal, _, _)| ordinal)
        .collect()
}

/// Wrong lowerings of slice-9 shapes, each never credited: an inverted
/// branch in the middle of the DAG, swapped successors, a join taking
/// another arm's value, an arm's value one off, a call argument wrong on
/// one arm, a store of the wrong value on one arm, a return of the wrong
/// constant deep in a tree, a switch case against the wrong constant, a
/// guard that traps on the wrong condition, a slot written with the wrong
/// tag on one arm, and a `bool` join taking the other arm.
pub(crate) fn slice_nine_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    let mut cases = Vec::new();
    // An inverted branch condition in the third diamond.
    let (source, mut machine) = slice9_pair(DagShape::Diamonds5);
    let jcc = nth(&machine, X86Opcode::Jcc, 2);
    let cc = condition(&machine, jcc);
    set_condition(&mut machine, jcc, inverse(cc));
    cases.push(("inverted branch in a middle diamond", source, machine));
    // Swapped successors of the fourth diamond, its recorded edges swapped
    // with them.
    let (source, mut machine) = slice9_pair(DagShape::Diamonds5);
    let jcc = nth(&machine, X86Opcode::Jcc, 3);
    let jmp = jcc + 1;
    assert_eq!(inst(&machine, jmp).opcode, X86Opcode::Jmp);
    let (taken, other) = (
        inst(&machine, jcc).operands[1].clone(),
        inst(&machine, jmp).operands[0].clone(),
    );
    inst_mut(&mut machine, jcc).operands[1] = other;
    inst_mut(&mut machine, jmp).operands[0] = taken;
    let block = block_of(&machine, jcc);
    machine.blocks.get_mut(&block).unwrap().successors.reverse();
    cases.push(("swapped successors in a middle diamond", source, machine));
    // A join taking another arm's value: the second diamond's `else` copy
    // reads the `then` arm's value.
    let (source, mut machine) = slice9_pair(DagShape::Diamonds5);
    let copies = join_copies(&machine);
    let input = inst(&machine, nth(&machine, X86Opcode::XorRR, 1)).operands[1].clone();
    inst_mut(&mut machine, copies[3]).operands[1] = input;
    cases.push((
        "join takes the diamond's input, not its arm's value",
        source,
        machine,
    ));
    // An arm's constant one off, in the last diamond.
    let (source, mut machine) = slice9_pair(DagShape::Diamonds6);
    let five = find(&machine, X86Opcode::MovRI)
        .into_iter()
        .rev()
        .find(|row| inst(&machine, *row).operands[1] == O::Imm(6))
        .expect("the last diamond's constant");
    inst_mut(&mut machine, five).operands[1] = O::Imm(7);
    cases.push(("an arm's constant one off", source, machine));
    // A call argument wrong on one arm: the third call passes `y`.
    let (source, mut machine) = slice9_pair(DagShape::CallJoin);
    let call = nth(&machine, X86Opcode::Call, 2);
    let setup = (0..call)
        .rev()
        .find(|ordinal| {
            inst(&machine, *ordinal)
                .operands
                .first()
                .and_then(gpr)
                .is_some_and(|reg| reg.root == Root::Physical(RDI))
        })
        .expect("the argument setup");
    let y = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| inst(&machine, ordinal))
        .find(|row| {
            row.opcode == X86Opcode::MovRR
                && row.operands.get(1).and_then(gpr).map(|reg| reg.root)
                    == Some(Root::Physical(RSI))
        })
        .map(|row| row.operands[0].clone())
        .expect("the entry copy of y");
    inst_mut(&mut machine, setup).operands[1] = y;
    cases.push(("a call argument wrong on one arm", source, machine));
    // A store of the wrong value on one arm: the fourth store stores `x`.
    let (source, mut machine) = slice9_pair(DagShape::StoreJoin);
    let store = nth(&machine, X86Opcode::MovMR, 3);
    let x = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| inst(&machine, ordinal))
        .find(|row| {
            row.opcode == X86Opcode::MovRR
                && row.operands.get(1).and_then(gpr).map(|reg| reg.root)
                    == Some(Root::Physical(RSI))
        })
        .map(|row| row.operands[0].clone())
        .expect("the entry copy of x");
    inst_mut(&mut machine, store).operands[1] = x;
    cases.push(("a store of the wrong value on one arm", source, machine));
    // A leaf deep in the tree returns another leaf's constant.
    let (source, mut machine) = slice9_pair(DagShape::NestedTree);
    let leaf = find(&machine, X86Opcode::MovRI)
        .into_iter()
        .find(|row| inst(&machine, *row).operands[1] == O::Imm(21))
        .expect("leaf 21's constant");
    inst_mut(&mut machine, leaf).operands[1] = O::Imm(22);
    cases.push(("a leaf returns another leaf's constant", source, machine));
    // A switch case against the wrong constant (case 33 of the second
    // switch tested against 34).
    let (source, mut machine) = slice9_pair(DagShape::SwitchChain);
    let cmp = find(&machine, X86Opcode::CmpRI)
        .into_iter()
        .filter(|row| inst(&machine, *row).operands[1] == O::Imm(33))
        .nth(1)
        .expect("the second switch's case-33 compare");
    inst_mut(&mut machine, cmp).operands[1] = O::Imm(34);
    cases.push(("a switch case against the wrong constant", source, machine));
    // The same in the third switch, whose selector is the third argument
    // register (found by the slice-9 mutation probe: the sampler's constant
    // phase once missed it).
    let (source, mut machine) = slice9_pair(DagShape::SwitchChain);
    let cmp = find(&machine, X86Opcode::CmpRI)
        .into_iter()
        .filter(|row| inst(&machine, *row).operands[1] == O::Imm(33))
        .nth(2)
        .expect("the third switch's case-33 compare");
    inst_mut(&mut machine, cmp).operands[1] = O::Imm(34);
    cases.push((
        "a third switch's case against the wrong constant",
        source,
        machine,
    ));
    // An inner switch's case swapped with its default.
    let (source, mut machine) = slice9_pair(DagShape::SwitchTree);
    let leaf = find(&machine, X86Opcode::MovRI)
        .into_iter()
        .find(|row| inst(&machine, *row).operands[1] == O::Imm(100))
        .expect("the first inner default's constant");
    inst_mut(&mut machine, leaf).operands[1] = O::Imm(101);
    cases.push((
        "an inner switch's default returns another constant",
        source,
        machine,
    ));
    // A bounds check that traps on the wrong condition.
    let (source, mut machine) = slice9_pair(DagShape::GuardChain9);
    let jcc = nth(&machine, X86Opcode::Jcc, 6);
    let cc = condition(&machine, jcc);
    set_condition(&mut machine, jcc, inverse(cc));
    cases.push((
        "a bounds check traps on the wrong condition",
        source,
        machine,
    ));
    // The `None` arm stores tag 1.
    let (source, mut machine) = slice9_pair(DagShape::SlotJoin);
    let zero_tag = find(&machine, X86Opcode::MovRI)
        .into_iter()
        .find(|row| inst(&machine, *row).operands[1] == O::Imm(0))
        .expect("the None arm's tag");
    inst_mut(&mut machine, zero_tag).operands[1] = O::Imm(1);
    cases.push((
        "a slot written with the wrong tag on one arm",
        source,
        machine,
    ));
    // A `bool` join taking the other arm's value.
    let (source, mut machine) = slice9_pair(DagShape::BoolDag);
    let copies = join_copies(&machine);
    let d = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| inst(&machine, ordinal))
        .find(|row| {
            // (slice 15: a `bool` parameter is the `movzx` of its register)
            matches!(
                row.opcode,
                X86Opcode::MovRR | X86Opcode::MovRR32 | X86Opcode::Movzx
            ) && row.operands.get(1).and_then(gpr).map(|reg| reg.root) == Some(Root::Physical(RSI))
        })
        .map(|row| row.operands[0].clone())
        .expect("the entry copy of d");
    let width = gpr(&inst(&machine, copies[5]).operands[1]).unwrap().bits;
    assert_eq!(gpr(&d).unwrap().bits, width, "{}", describe(&machine));
    inst_mut(&mut machine, copies[5]).operands[1] = d;
    cases.push(("a bool join takes d, not its arm's value", source, machine));
    cases
}

#[test]
fn every_slice_nine_refutation_is_never_credited() {
    let mut outcomes: Vec<(&str, &str)> = Vec::new();
    for (label, source, machine) in slice_nine_refutations() {
        outcomes.push((label, never_credited(&source, &machine, label)));
    }
    // The theorem judges the value and condition mutants (several paths get
    // no exact affine refusal).
    for (label, outcome) in &outcomes {
        assert_eq!(*outcome, "refuted", "{label}");
    }
}

/// Wrong control past the slice-6 bounds: a branch retargeted to a block
/// that is not its LIR successor, an extra edge, a missing edge (both of a
/// diamond's edges to one arm), a return where the source traps and a trap
/// where it returns: each a named mismatch or no claim, never credit (flags
/// across a block boundary: [`flags_never_cross_a_dag_block_boundary`]).
#[test]
fn wrong_dag_control_is_named_or_refused() {
    // A branch retargeted to another diamond's arm.
    let (source, mut machine) = slice9_pair(DagShape::Diamonds5);
    let jcc = nth(&machine, X86Opcode::Jcc, 1);
    let other = inst(&machine, nth(&machine, X86Opcode::Jcc, 3)).operands[1].clone();
    let O::Block(target) = other else {
        unreachable!()
    };
    inst_mut(&mut machine, jcc).operands[1] = O::Block(target);
    let block = block_of(&machine, jcc);
    let successors = &mut machine.blocks.get_mut(&block).unwrap().successors;
    successors[0] = target;
    assert_ne!(
        never_credited(&source, &machine, "retargeted branch"),
        "refuted"
    );
    // An extra edge: a second `jcc` from a diamond's head to the next join.
    let (source, mut machine) = slice9_pair(DagShape::Diamonds5);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    let later = inst(&machine, nth(&machine, X86Opcode::Jcc, 1)).operands[1].clone();
    let O::Block(target) = later else {
        unreachable!()
    };
    let block = block_of(&machine, jcc);
    let row = X86ISelInst::new(
        X86Opcode::Jcc,
        vec![O::CondCode(trust_cg_ir::X86CondCode::O), O::Block(target)],
    );
    insert_at(&mut machine, jcc, row);
    machine
        .blocks
        .get_mut(&block)
        .unwrap()
        .successors
        .insert(0, target);
    assert_ne!(never_credited(&source, &machine, "extra edge"), "refuted");
    // A missing edge: both edges of the first diamond to its `then` arm.
    let (source, mut machine) = slice9_pair(DagShape::Diamonds5);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    let taken = inst(&machine, jcc).operands[1].clone();
    inst_mut(&mut machine, jcc + 1).operands[0] = taken.clone();
    let O::Block(target) = taken else {
        unreachable!()
    };
    let block = block_of(&machine, jcc);
    machine.blocks.get_mut(&block).unwrap().successors = vec![target];
    assert_ne!(never_credited(&source, &machine, "missing edge"), "refuted");
    // A return where a bounds check traps.
    let (source, mut machine) = slice9_pair(DagShape::GuardChain9);
    let ud2 = nth(&machine, X86Opcode::Ud2, 4);
    let row = inst_mut(&mut machine, ud2);
    row.opcode = X86Opcode::Ret;
    row.flags = row.opcode.default_flags();
    assert_eq!(
        never_credited(&source, &machine, "return for trap"),
        "mismatch"
    );
    // A trap where a switch arm returns.
    let (source, mut machine) = slice9_pair(DagShape::SwitchTree);
    let ret = nth(&machine, X86Opcode::Ret, 7);
    let row = inst_mut(&mut machine, ret);
    row.opcode = X86Opcode::Ud2;
    row.flags = row.opcode.default_flags();
    assert_ne!(
        never_credited(&source, &machine, "trap for return"),
        "refuted"
    );
}

// ---------------------------------------------------------------------------
// Rules of the DAG admission and walk
// ---------------------------------------------------------------------------

/// Loops stay outside, by name, whatever their size; the block and
/// instruction bounds are named refusals.
#[test]
fn loops_and_the_size_bounds_are_named_refusals() {
    // Slice 12 admits natural loops; an irreducible cycle stays outside.
    let looped = super::slice12::irreducible_loop();
    match admitted_body(&looped) {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::SourceShape(detail))) => {
            assert!(detail.contains("an irreducible loop"), "{detail}")
        }
        other => panic!("an irreducible loop: {:?}", other.err()),
    }
    // A chain of more blocks than the lane admits.
    let blocks = MAX_BODY_BLOCKS + 2;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice9");
    let signature = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("s9_many_blocks", signature);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let mut value = x;
    for _ in 1..blocks {
        let next = f.create_block();
        let one = f.iconst(Ty::U64, 1);
        value = f.add(Ty::U64, value, one);
        f.br(next, vec![]);
        f.switch_to_block(next);
    }
    f.ret(vec![value]);
    f.build();
    let many = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &builder.build().expect("ModuleBuilder::build: test fixture"),
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .remove(0)
    .0;
    match admitted_body(&many) {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::SourceShape(detail))) => {
            assert!(detail.contains("blocks (the lane admits"), "{detail}")
        }
        other => panic!("too many blocks: {:?}", other.err()),
    }
    // A chain of more instructions than the lane admits.
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice9");
    let signature = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("s9_many_instructions", signature);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let mut value = x;
    for k in 0..(MAX_BODY_INSTRUCTIONS / 2 + 1) {
        let constant = f.iconst(Ty::U64, k as i128);
        value = f.add(Ty::U64, value, constant);
    }
    f.ret(vec![value]);
    f.build();
    let long = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &builder.build().expect("ModuleBuilder::build: test fixture"),
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .remove(0)
    .0;
    match admitted_body(&long) {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::SourceShape(detail))) => {
            assert!(detail.contains("instructions (the lane admits"), "{detail}")
        }
        other => panic!("too many instructions: {:?}", other.err()),
    }
}

/// A `Switch` whose two cases denote one bit pattern would give two edges
/// one test, and the edge guards would not partition the runs: it is
/// outside the domain.
#[test]
fn a_switch_with_two_cases_of_one_value_is_refused() {
    let (mut source, _) = slice9_pair(DagShape::SwitchChain);
    for block in source.blocks.values_mut() {
        if let Some(last) = block.instructions.last_mut()
            && let L::Switch { cases, .. } = &mut last.opcode
        {
            cases[2].0 = cases[1].0;
        }
    }
    match admitted_body(&source) {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::SourceDomain(detail))) => {
            assert!(detail.contains("two cases of one value"), "{detail}")
        }
        other => panic!("duplicate cases: {:?}", other.err()),
    }
}

/// A join's merged private bytes: the `None` arm's payload is the slot's
/// initial byte, the `Some` arm's the stored `x`; the theorem reads both
/// through one merged definition per byte, and a machine that reads the
/// payload from the tag slot is refuted.
#[test]
fn merged_slot_bytes_are_joined_by_the_edges_guards() {
    let (source, machine) = slice9_pair(DagShape::SlotJoin);
    let body = admitted_body(&source).unwrap();
    let dag = body.dag.as_ref().expect("a DAG");
    // Both slots' bytes are merged at the first join (tag 1 or 0; payload
    // `x` or unwritten).
    let first_join = dag
        .order
        .iter()
        .find(|block| dag.predecessors[block].len() > 1)
        .copied()
        .unwrap();
    let merged: Vec<&SlotMerge> = dag
        .merges
        .iter()
        .filter(|merge| merge.join == first_join)
        .collect();
    assert_eq!(merged.len(), 16, "two 8-byte slots merged");
    assert!(
        merged
            .iter()
            .any(|merge| merge.incoming.iter().any(|(_, byte)| byte.is_none())),
        "the unwritten payload is an incoming initial byte"
    );
    let obligation = owner(&source, &machine, "SlotJoin");
    // The merged bytes are definitions (one use each is inlined in the
    // canonical spelling; stated plainly without inlining here).
    let uninlined = theorem_with_path_encoding(
        &source,
        &machine,
        SYSV,
        PathEncoding {
            inline_single_use: false,
            value_number: ValueNumbering::Off,
            ..PathEncoding::CANONICAL
        },
    )
    .unwrap();
    let text = uninlined
        .preconditions
        .iter()
        .map(|premise| premise.to_string())
        .collect::<Vec<_>>()
        .join("\n");
    assert!(text.contains("y0 "), "a merged byte is defined\n{text}");
    assert!(dag_holds_on_samples(&obligation));
    // The payload read from the tag slot.
    let (source, mut machine) = slice9_pair(DagShape::SlotJoin);
    let loads = find(&machine, X86Opcode::MovRM);
    let tag_base = inst(&machine, loads[loads.len() - 2]).operands[1].clone();
    let payload_load = loads[loads.len() - 1];
    inst_mut(&mut machine, payload_load).operands[1] = tag_base;
    assert_eq!(
        never_credited(&source, &machine, "payload from the tag"),
        "refuted"
    );
}

/// A join of paths on which different private slots escaped takes their
/// union (slice 13): the slot is treated as escaped on every path through
/// the join, so a later call reads and redefines it on each, and the DAG
/// theorem holds. (Until slice 13 this was outside the domain.)
#[test]
fn a_join_of_different_escapes_takes_their_union() {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice9");
    let sink_ty = builder.add_func_type(vec![Ty::PtrMut(Box::new(Ty::U64))], vec![]);
    let sink = builder.declare_function("sink", sink_ty);
    let later_ty = builder.add_func_type(vec![], vec![]);
    let later = builder.declare_function("later", later_ty);
    let signature = builder.add_func_type(vec![Ty::Bool, Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("s9_escape_join", signature);
    let entry = f.create_block();
    let c = f.add_block_param(entry, Ty::Bool);
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let slot = f.alloca(Ty::U64);
    f.store(Ty::U64, slot, x);
    let (escape, keep, join) = (f.create_block(), f.create_block(), f.create_block());
    f.condbr(c, escape, vec![], keep, vec![]);
    f.switch_to_block(escape);
    f.call_void(sink, vec![slot]);
    f.br(join, vec![]);
    f.switch_to_block(keep);
    f.br(join, vec![]);
    f.switch_to_block(join);
    let before = f.load(Ty::U64, slot);
    f.call_void(later, vec![]);
    let after = f.load(Ty::U64, slot);
    let value = f.add(Ty::U64, before, after);
    f.ret(vec![value]);
    f.build();
    let source = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &builder.build().expect("ModuleBuilder::build: test fixture"),
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == "s9_escape_join")
    .unwrap();
    let body = admitted_body_as(&source, Some(true))
        .unwrap_or_else(|refusal| panic!("a join of different escapes: {refusal}"));
    let dag = body.dag.as_ref().expect("stated over its DAG");
    let last = *dag.order.last().expect("a block");
    let call = &dag.blocks[&last].calls[0];
    assert_eq!(
        call.slot_reads
            .iter()
            .map(|(slot, _)| *slot)
            .collect::<Vec<_>>(),
        vec![0],
        "the later call reads the slot on every path"
    );
    let machine = select(&source, X86CallAbi::SystemV);
    let theorem = theorem_with_path_encoding(
        &source,
        &machine,
        SYSV,
        PathEncoding {
            dag: Some(true),
            ..PathEncoding::CANONICAL
        },
    )
    .unwrap_or_else(|refusal| panic!("a join of different escapes: {refusal}"));
    assert!(dag_holds_on_samples(&theorem));
}

/// A machine root the paths into a join leave holding a private address on
/// one and bits on another is [`RegValue::Mixed`]: reading it makes no
/// claim.
#[test]
fn a_root_of_different_kinds_at_a_join_makes_no_claim() {
    let (source, mut machine) = slice9_pair(DagShape::Diamonds5);
    // The first diamond's `else` arm copies a frame address into the join's
    // value register instead of its value.
    let copies = join_copies(&machine);
    let ordinal = copies[1];
    let destination = inst(&machine, ordinal).operands[0].clone();
    let provenance = inst(&machine, ordinal).lowering_provenance;
    let row = inst_mut(&mut machine, ordinal);
    *row = X86ISelInst::new(
        X86Opcode::Lea,
        vec![
            destination,
            O::MemAddr {
                base: Box::new(O::StackSlot(0)),
                disp: 0,
            },
        ],
    );
    row.lowering_provenance = provenance;
    machine.stack_slots = vec![trust_cg_lower::function::StackSlotInfo::new(8, 8)];
    let mut source = source;
    source.stack_slots = machine.stack_slots.clone();
    match source_bound_x86_body(&source, &machine, SYSV) {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::MachineRow { detail, .. })) => {
            assert!(detail.contains("different kinds of value"), "{detail}")
        }
        Ok(_) => panic!("a mixed root at a join was read as a value"),
        Err(other) => panic!("a mixed root: {other}"),
    }
}

/// A block that redefines a value some path into it already defined (on
/// that path an SSA redefinition, which a chain refuses) is outside the
/// domain, also when the join no longer keeps the value (only one incoming
/// edge defines it).
#[test]
fn a_value_redefined_after_a_join_is_refused() {
    let mut source = slice9_lir(DagShape::Diamonds5);
    let cfg = source_cfg(&source).unwrap();
    let join = cfg
        .order
        .iter()
        .copied()
        .find(|block| cfg.predecessors[block].len() > 1)
        .unwrap();
    let arm = cfg.predecessors[&join][0];
    let value = source.blocks[&arm]
        .instructions
        .iter()
        .find(|inst| matches!(inst.opcode, L::Iconst { .. }))
        .and_then(|inst| inst.results.first().copied())
        .expect("an arm's constant");
    source.blocks.get_mut(&join).unwrap().instructions.insert(
        0,
        trust_cg_lower::instructions::Instruction {
            opcode: L::Iconst {
                ty: Type::I64,
                imm: 0,
            },
            args: vec![],
            results: vec![value],
        },
    );
    match admitted_body(&source) {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::SourceDomain(detail))) => {
            assert!(detail.contains("redefines"), "{detail}")
        }
        other => panic!("a redefinition after a join: {:?}", other.err()),
    }
}

/// `fn(c: bool, d: bool) -> bool` with a `bool` slot written with `d` on the
/// `then` arm of `c` (and, `both`, with `false` on the other), read after
/// the join.
fn bool_slot_join(both: bool) -> Function {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice9");
    let signature = builder.add_func_type(vec![Ty::Bool, Ty::Bool], vec![Ty::Bool]);
    let mut f = builder.function("s9_bool_slot_join", signature);
    let entry = f.create_block();
    let c = f.add_block_param(entry, Ty::Bool);
    let d = f.add_block_param(entry, Ty::Bool);
    f.switch_to_block(entry);
    let flag = f.alloca(Ty::Bool);
    let (set, other, join) = (f.create_block(), f.create_block(), f.create_block());
    f.condbr(c, set, vec![], other, vec![]);
    f.switch_to_block(set);
    f.store(Ty::Bool, flag, d);
    f.br(join, vec![]);
    f.switch_to_block(other);
    if both {
        let no = f.bool_const(false);
        f.store(Ty::Bool, flag, no);
    }
    f.br(join, vec![]);
    f.switch_to_block(join);
    let value = f.load(Ty::Bool, flag);
    f.ret(vec![value]);
    f.build();
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &builder.build().expect("ModuleBuilder::build: test fixture"),
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == "s9_bool_slot_join")
    .unwrap()
}

/// A `bool` read of a merged private byte is admitted only when every
/// incoming edge brings a byte a `bool` read may read (here a `bool`
/// store's on both arms); a byte one path left unwritten is refused there,
/// as a chain refuses it on that path.
#[test]
fn a_bool_read_of_a_merged_byte_needs_a_bool_byte_on_every_edge() {
    let both = bool_slot_join(true);
    let machine = select(&both, X86CallAbi::SystemV);
    let body = admitted_body_as(&both, Some(true)).unwrap();
    assert!(body.dag.is_some());
    let theorem = theorem_with_path_encoding(&both, &machine, SYSV, DAG).unwrap();
    assert!(dag_holds_on_samples(&theorem), "{}", describe(&machine));
    assert_encodings_agree(&both, &machine, "bool slot written on both arms");
    let one = bool_slot_join(false);
    for dag in [Some(true), Some(false)] {
        match admitted_body_as(&one, dag) {
            Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::SourceDomain(detail))) => {
                assert!(detail.contains("no bool store"), "{detail}")
            }
            other => panic!(
                "a bool read of a byte one path left unwritten ({dag:?}): {:?}",
                other.err()
            ),
        }
    }
}

/// `fn(a: u64, b: u64) -> u64 { let t = a < b; if t { if t { 1 } else { 2 }
/// } else { 3 } }`: the inner branch tests the outer branch's value again.
fn retested_branch() -> Function {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice9");
    let signature = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("s9_retested_branch", signature);
    let entry = f.create_block();
    let a = f.add_block_param(entry, Ty::U64);
    let b = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let (inner, one, two, three) = (
        f.create_block(),
        f.create_block(),
        f.create_block(),
        f.create_block(),
    );
    let test = f.icmp(ICmpOp::Ult, Ty::U64, a, b);
    f.condbr(test, inner, vec![], three, vec![]);
    f.switch_to_block(inner);
    f.condbr(test, one, vec![], two, vec![]);
    for (block, value) in [(one, 1), (two, 2), (three, 3)] {
        f.switch_to_block(block);
        let constant = f.iconst(Ty::U64, value);
        f.ret(vec![constant]);
    }
    f.build();
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &builder.build().expect("ModuleBuilder::build: test fixture"),
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == "s9_retested_branch")
    .unwrap()
}

/// Flags never cross a block boundary over the DAG either: with the rows
/// that compute the inner branch's test removed, its `jcc` reads the flags
/// the outer block's compare wrote (here of the same test, and the hardware
/// would keep them), which makes no claim, as on a path.
#[test]
fn flags_never_cross_a_dag_block_boundary() {
    let source = retested_branch();
    let machine = select(&source, X86CallAbi::SystemV);
    let theorem = theorem_with_path_encoding(&source, &machine, SYSV, DAG)
        .unwrap_or_else(|refusal| panic!("{refusal}\n{}", describe(&machine)));
    assert!(dag_holds_on_samples(&theorem), "{}", describe(&machine));
    let mut machine = machine;
    let jcc = nth(&machine, X86Opcode::Jcc, 1);
    let block = block_of(&machine, jcc);
    let first = (0..jcc)
        .find(|ordinal| block_of(&machine, *ordinal) == block)
        .unwrap();
    for ordinal in (first..jcc).rev() {
        remove_at(&mut machine, ordinal);
    }
    assert_flags_do_not_cross(&source, &machine, "a compare's flags");
    // The same with flags a slice-10 ALU row wrote: a `sub` of the two
    // arguments (whose flags the walk models) just before the outer `jcc`,
    // so both outer edges leave its flags.
    let mut machine = select(&source, X86CallAbi::SystemV);
    let argument = |machine: &X86ISelFunction, root: u16| {
        rows(machine)
            .into_iter()
            .map(|(ordinal, _, _)| inst(machine, ordinal))
            .find(|row| {
                row.opcode == X86Opcode::MovRR
                    && row.operands.get(1).and_then(gpr).map(|reg| reg.root)
                        == Some(Root::Physical(root))
            })
            .map(|row| row.operands[0].clone())
            .expect("an argument's entry copy")
    };
    let (a, b) = (argument(&machine, RDI), argument(&machine, RSI));
    let fresh = vreg(machine.next_vreg);
    machine.next_vreg += 1;
    let outer = nth(&machine, X86Opcode::Jcc, 0);
    insert_at(
        &mut machine,
        outer,
        X86ISelInst::new(X86Opcode::SubRR, vec![fresh, a, b]),
    );
    // The `sub` is walked, and the outer `jcc` reads its flags in its block.
    if let Err(refusal) = theorem_with_path_encoding(&source, &machine, SYSV, DAG) {
        panic!(
            "the sub variant before its inner rows are removed: {refusal}\n{}",
            describe(&machine)
        );
    }
    let jcc = nth(&machine, X86Opcode::Jcc, 1);
    let block = block_of(&machine, jcc);
    let first = (0..jcc)
        .find(|ordinal| block_of(&machine, *ordinal) == block)
        .unwrap();
    for ordinal in (first..jcc).rev() {
        remove_at(&mut machine, ordinal);
    }
    assert_flags_do_not_cross(&source, &machine, "a sub's flags");
}

/// The inner branch's `jcc`, with no flag writer in its block, makes no
/// claim under both encodings.
#[track_caller]
fn assert_flags_do_not_cross(source: &Function, machine: &X86ISelFunction, what: &str) {
    for dag in [DAG, PATHS] {
        match theorem_with_path_encoding(source, machine, SYSV, dag) {
            Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::MachineRow { detail, .. })) => {
                assert!(
                    detail.contains("no compare or test row of its block"),
                    "{what}: {detail}"
                )
            }
            other => panic!(
                "{what} across a block boundary ({:?}): {:?}\n{}",
                dag.dag,
                other.map(|_| "a theorem"),
                describe(machine)
            ),
        }
    }
}

/// `fn(x: u64, c: bool, y: u64) -> u64 { if x == 0 { (if c { y } else { y +
/// 1 }) + x } else { 9 } }`: an inner join reached only when `x == 0`.
fn path_join() -> Function {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice9");
    let signature = builder.add_func_type(vec![Ty::U64, Ty::Bool, Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("s9_path_join", signature);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    let c = f.add_block_param(entry, Ty::Bool);
    let y = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let (zero, other, then, otherwise, join) = (
        f.create_block(),
        f.create_block(),
        f.create_block(),
        f.create_block(),
        f.create_block(),
    );
    let joined = f.add_block_param(join, Ty::U64);
    let nought = f.iconst(Ty::U64, 0);
    let test = f.icmp(ICmpOp::Eq, Ty::U64, x, nought);
    f.condbr(test, zero, vec![], other, vec![]);
    f.switch_to_block(zero);
    f.condbr(c, then, vec![], otherwise, vec![]);
    f.switch_to_block(then);
    f.br(join, vec![y]);
    f.switch_to_block(otherwise);
    let one = f.iconst(Ty::U64, 1);
    let next = f.add(Ty::U64, y, one);
    f.br(join, vec![next]);
    f.switch_to_block(join);
    let sum = f.add(Ty::U64, joined, x);
    f.ret(vec![sum]);
    f.switch_to_block(other);
    let nine = f.iconst(Ty::U64, 9);
    f.ret(vec![nine]);
    f.build();
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &builder.build().expect("ModuleBuilder::build: test fixture"),
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == "s9_path_join")
    .unwrap()
}

/// A join's items are judged under the join's guard: a machine that adds
/// nothing where the source adds `x` in a join reached only when `x == 0` is
/// correct, and its DAG theorem holds (as the per-path theorem does), while
/// stating the join's items on every input would refute it.
#[test]
fn a_join_reached_on_some_paths_is_judged_under_its_guard() {
    let source = path_join();
    let mut machine = select(&source, X86CallAbi::SystemV);
    let x = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| inst(&machine, ordinal))
        .find(|row| {
            row.opcode == X86Opcode::MovRR
                && row.operands.get(1).and_then(gpr).map(|reg| reg.root)
                    == Some(Root::Physical(RDI))
        })
        .map(|row| row.operands[0].clone())
        .expect("the entry copy of x");
    let add = find(&machine, X86Opcode::AddRR)
        .into_iter()
        .find(|row| inst(&machine, *row).operands[2] == x)
        .expect("the join's add of x");
    let (destination, joined) = (
        inst(&machine, add).operands[0].clone(),
        inst(&machine, add).operands[1].clone(),
    );
    let provenance = inst(&machine, add).lowering_provenance;
    let row = inst_mut(&mut machine, add);
    *row = X86ISelInst::new(X86Opcode::MovRR, vec![destination, joined]);
    row.lowering_provenance = provenance;
    let theorem = theorem_with_path_encoding(&source, &machine, SYSV, DAG)
        .unwrap_or_else(|refusal| panic!("{refusal}\n{}", describe(&machine)));
    assert!(dag_holds_on_samples(&theorem), "{}", describe(&machine));
    assert_eq!(
        assert_encodings_agree(&source, &machine, "x + 0 under x == 0"),
        0
    );
}

/// The real x86 optimizer's output at O1, O2 and O3 for every slice-9
/// fixture: the owner never names a mismatch for a correct lowering, and
/// every theorem it builds holds.
#[test]
fn optimized_slice_nine_fixtures_are_judged_without_false_mismatches() {
    use trust_cg_codegen::x86_64::pipeline::{X86Pipeline, X86PipelineConfig};
    let mut built = 0;
    for opt_level in [
        trust_cg_opt::OptLevel::O1,
        trust_cg_opt::OptLevel::O2,
        trust_cg_opt::OptLevel::O3,
    ] {
        let pipeline = X86Pipeline::new(X86PipelineConfig {
            opt_level,
            call_abi: X86CallAbi::SystemV,
            ..X86PipelineConfig::default()
        });
        for shape in SLICE_NINE {
            let (source, mut machine) = slice9_pair(shape);
            pipeline.run_x86_optimization_passes(&mut machine);
            match source_bound_x86_body(&source, &machine, SYSV) {
                Ok(owner) => {
                    built += 1;
                    assert!(
                        dag_holds_on_samples(owner.obligation()),
                        "{shape:?} at {opt_level:?}\n{}",
                        describe(&machine)
                    );
                    eprintln!("{opt_level:?} {shape:?}: theorem holds on samples");
                }
                Err(X86BodyRefusal::Unsupported(refusal)) => {
                    eprintln!("{opt_level:?} {shape:?}: no claim ({refusal})");
                }
                Err(other) => panic!(
                    "{shape:?} at {opt_level:?}: {other}\n{}",
                    describe(&machine)
                ),
            }
        }
    }
    assert!(built > 0, "no optimized fixture built a theorem");
}

const SLICE_NINE_SNAPSHOT_SHA256: &str =
    "9ad06e11b73f578abcf611f69d5372baa0bcd8b11ae78c149e77f3af294a65e3";

/// The rendered theorem of every slice-9 fixture, pinned by digest (a
/// change of encoding is a reviewed change), and independent of the
/// function's name.
#[test]
fn slice_nine_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str =
        include_str!("../tests/fixtures/x86_source_bound_body/slice9_snapshots.smt2");
    let mut rendered = String::new();
    for shape in SLICE_NINE {
        let (source, machine) = slice9_pair(shape);
        let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        let smt2 = generate_smt2_query_raw(owner.obligation(), &replay_config());
        rendered.push_str(&format!(";;;; {shape:?}\n{smt2}\n"));
        let (mut source, mut machine) = (source.clone(), machine.clone());
        source.name = "renamed_function".into();
        machine.name = "renamed_function".into();
        let renamed = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        assert_eq!(
            generate_smt2_query_raw(renamed.obligation(), &replay_config()),
            smt2
        );
    }
    if std::env::var_os("TCG_X86_BODY_SNAPSHOT_WRITE").is_some() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/x86_source_bound_body/slice9_snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_NINE_SNAPSHOT_SHA256 to {:x} and re-run \
             without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        SLICE_NINE_SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    assert_eq!(rendered, GOLDEN, "slice-9 snapshots drifted");
}

/// Building the same pair twice gives the same theorem (no hash-map order
/// reaches a name or a claim).
#[test]
fn dag_theorems_are_deterministic() {
    for shape in SLICE_NINE {
        let (source, machine) = slice9_pair(shape);
        let first = owner(&source, &machine, "first");
        for _ in 0..3 {
            assert_eq!(owner(&source, &machine, "again"), first, "{shape:?}");
        }
    }
}
