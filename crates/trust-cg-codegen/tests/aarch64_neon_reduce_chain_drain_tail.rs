// trust-cg-codegen - the bitwise-chain drain's dead-tail skip
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `neon-reduce`'s forward-chain path (`BitChainRecognized`) splices a vector
//! main loop in front of a `while i <u N { acc OP= a[i] }` chain loop. Its
//! vector drain branches straight to the loop exit when the induction's entry
//! value `iv0` is one constant on every path with `N - iv0` a multiple of the
//! vector width, and otherwise continues into the scalar tail. These tests
//! JIT-run chain loops at O2 and O3 and compare against a plain Rust model of
//! the same loop.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, ProofAnnotation, Ty};
use trust_ir_build::ModuleBuilder;

const TRAP: u64 = 0xDEAD_BEEF;

/// Where the loop's induction starts.
#[derive(Clone, Copy, Debug)]
enum Start {
    /// A compile-time constant.
    Const(u64),
    /// `sel != 0 ? then_start : else_start`, merged into one block parameter
    /// before the loop preheader.
    Diamond { then_start: u64, else_start: u64 },
    /// The run-time `start` argument.
    Param,
    /// Where an earlier early-exit search stopped: `j` runs 1..=limit and
    /// stops early when `j == sel`. A small constant `limit` lets O2/O3 fully
    /// unroll that search, which rewrites its induction into per-iteration
    /// constants, so the chain loop's start register has several constant
    /// definitions, one per exit edge.
    SearchStop { limit: u64 },
}

#[derive(Clone, Copy, Debug)]
enum Bound {
    /// `i <u N` with a constant N.
    ConstUlt(u64),
    /// `i <s N` with a constant N.
    ConstSlt(u64),
    /// `i <u n` with the run-time `n` argument.
    ParamUlt,
}

#[derive(Clone, Debug)]
struct Shape {
    name: &'static str,
    /// Element (and accumulator) type: U32 or U64 (U8/U16 for width probes).
    elem: Ty,
    /// One accumulator per op, each seeded with the matching seed.
    ops: &'static [BinOp],
    seeds: &'static [u64],
    start: Start,
    bound: Bound,
    /// Split the body into a pass-through block (first reduction) and a
    /// separate latch (other reductions + the step), the >= 3-block chain shape.
    middle_guard: bool,
    /// The exit folds the induction into the returned value.
    exit_reads_iv: bool,
    /// The exit re-tests `i <u N` and selects on it.
    exit_retests_bound: bool,
    /// Wrap the chain loop in an outer loop of `trips` iterations; `reset`
    /// re-enters the chain at the constant start each time, otherwise the
    /// chain resumes from the induction value the previous run left.
    /// Requires `Start::Const`.
    outer: Option<(u64, bool)>,
    /// The entry branches straight to the chain loop's exit when
    /// `sel == SHARED_SEL`, with the induction `SHARED_IV` and the seeds.
    /// Requires `Start::Const`.
    shared_exit: bool,
}

const SHARED_SEL: u64 = 7777;
const SHARED_IV: u64 = 12345;

fn elem_bits(ty: &Ty) -> u32 {
    match ty {
        Ty::U8 => 8,
        Ty::U16 => 16,
        Ty::U32 => 32,
        Ty::U64 => 64,
        other => panic!("unsupported element type {other:?}"),
    }
}

fn header_bound(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    bound: Bound,
    n_rt: trust_ir::ValueId,
) -> (ICmpOp, trust_ir::ValueId) {
    match bound {
        Bound::ConstUlt(n) => (ICmpOp::Ult, fb.iconst(Ty::U64, i128::from(n))),
        Bound::ConstSlt(n) => (ICmpOp::Slt, fb.iconst(Ty::U64, i128::from(n))),
        Bound::ParamUlt => (ICmpOp::Ult, n_rt),
    }
}

/// `fn(p: *const T, sel: u64, start: u64, n: u64) -> u64`.
fn build_module(shape: &Shape) -> trust_ir::Module {
    assert_eq!(shape.ops.len(), shape.seeds.len());
    let elem = shape.elem.clone();
    let mut mb = ModuleBuilder::new(shape.name);
    let fty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(shape.name, fty);
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, Ty::Ptr);
    let sel = fb.add_block_param(entry, Ty::U64);
    let start_rt = fb.add_block_param(entry, Ty::U64);
    let n_rt = fb.add_block_param(entry, Ty::U64);

    let pre = fb.create_block();
    let pre_start = fb.add_block_param(pre, Ty::U64);
    let header = fb.create_block();
    let iv = fb.add_block_param(header, Ty::U64);
    let accs: Vec<_> = shape
        .ops
        .iter()
        .map(|_| fb.add_block_param(header, elem.clone()))
        .collect();
    // `mid` holds the first reduction and falls through to `latch`, which is
    // created after `exit` so the two are not layout-adjacent and
    // cfg-simplify keeps them apart (the chain path needs a >= 3-block body).
    let body = fb.create_block();
    let exit = fb.create_block();
    let exit_iv = fb.add_block_param(exit, Ty::U64);
    let exit_accs: Vec<_> = shape
        .ops
        .iter()
        .map(|_| fb.add_block_param(exit, elem.clone()))
        .collect();
    let trap = fb.create_block();
    let latch = shape.middle_guard.then(|| fb.create_block());
    // Outer loop header `oh(j, total, ivc)` and its exit `done(t)`.
    let outer = shape.outer.map(|(trips, reset)| {
        let oh = fb.create_block();
        let j = fb.add_block_param(oh, Ty::U64);
        let total = fb.add_block_param(oh, Ty::U64);
        let ivc = fb.add_block_param(oh, Ty::U64);
        let done = fb.create_block();
        let t = fb.add_block_param(done, Ty::U64);
        (trips, reset, oh, j, total, ivc, done, t)
    });
    let const_start = match shape.start {
        Start::Const(k) => Some(k),
        _ => None,
    };
    let bits = elem_bits(&elem);
    let mask = if bits == 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    };

    // entry
    fb.switch_to_block(entry);
    if let Some((trips, reset, oh, j, total, ivc, done, t)) = outer {
        let k = const_start.expect("an outer loop needs a constant start");
        let zero = fb.iconst(Ty::U64, 0);
        let s = fb.iconst(Ty::U64, i128::from(k));
        fb.br(oh, vec![zero, zero, s]);
        fb.switch_to_block(oh);
        let lim = fb.iconst(Ty::U64, i128::from(trips));
        let more = fb.icmp(ICmpOp::Ult, Ty::U64, j, lim);
        let enter = if reset {
            fb.iconst(Ty::U64, i128::from(k))
        } else {
            ivc
        };
        fb.condbr(more, pre, vec![enter], done, vec![total]);
        fb.switch_to_block(done);
        fb.ret(vec![t]);
    } else if shape.shared_exit {
        let k = const_start.expect("a shared exit needs a constant start");
        let want = fb.iconst(Ty::U64, i128::from(SHARED_SEL));
        let c = fb.icmp(ICmpOp::Eq, Ty::U64, sel, want);
        let mut skip = vec![fb.iconst(Ty::U64, i128::from(SHARED_IV))];
        for seed in shape.seeds {
            skip.push(fb.iconst(elem.clone(), i128::from(*seed & mask)));
        }
        let s = fb.iconst(Ty::U64, i128::from(k));
        fb.condbr(c, exit, skip, pre, vec![s]);
    } else {
        match shape.start {
            Start::Const(k) => {
                let s = fb.iconst(Ty::U64, i128::from(k));
                fb.br(pre, vec![s]);
            }
            Start::Param => fb.br(pre, vec![start_rt]),
            Start::SearchStop { limit } => {
                let search = fb.create_block();
                let j = fb.add_block_param(search, Ty::U64);
                let search_test = fb.create_block();
                let zero = fb.iconst(Ty::U64, 0);
                fb.br(search, vec![zero]);
                fb.switch_to_block(search);
                let one = fb.iconst(Ty::U64, 1);
                let next = fb.add(Ty::U64, j, one);
                fb.br(search_test, vec![]);
                fb.switch_to_block(search_test);
                let lim = fb.iconst(Ty::U64, i128::from(limit));
                let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, lim);
                let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, sel);
                let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
                fb.condbr(more, search, vec![next], pre, vec![next]);
            }
            Start::Diamond {
                then_start,
                else_start,
            } => {
                let then_b = fb.create_block();
                let else_b = fb.create_block();
                let zero = fb.iconst(Ty::U64, 0);
                let c = fb.icmp(ICmpOp::Ne, Ty::U64, sel, zero);
                fb.condbr(c, then_b, vec![], else_b, vec![]);
                fb.switch_to_block(then_b);
                let s = fb.iconst(Ty::U64, i128::from(then_start));
                fb.br(pre, vec![s]);
                fb.switch_to_block(else_b);
                let s = fb.iconst(Ty::U64, i128::from(else_start));
                fb.br(pre, vec![s]);
            }
        }
    }

    // preheader: seed the accumulators and enter the loop.
    fb.switch_to_block(pre);
    let mut args = vec![pre_start];
    for seed in shape.seeds {
        args.push(fb.iconst(elem.clone(), i128::from(*seed & mask)));
    }
    fb.br(header, args);

    // header: `i < N` continue test.
    fb.switch_to_block(header);
    let (cc, n) = header_bound(&mut fb, shape.bound, n_rt);
    let go = fb.icmp(cc, Ty::U64, iv, n);
    let mut exit_args = vec![iv];
    exit_args.extend(accs.iter().copied());
    fb.condbr(go, body, vec![], exit, exit_args);

    // body: acc_j = acc_j OP a[i]; i += 1. With `middle_guard`, the first
    // reduction is in `body` and the rest (plus the step) in `latch`.
    fb.switch_to_block(body);
    if latch.is_some() {
        // The bridge's `a[i]` bounds probe: an `InBounds`-annotated `i <u N`
        // whose result is unused lowers to a proof-only
        // `TrapBoundsCheckExact` carrier. The carrier is a branch-class
        // instruction, so cfg-simplify keeps `body` and `latch` apart until
        // bounds-check elimination deletes it (the header dominates it).
        if let Bound::ConstUlt(n) | Bound::ConstSlt(n) = shape.bound {
            let bound = fb.iconst(Ty::U64, i128::from(n));
            let _probe = fb.icmp(ICmpOp::Ult, Ty::U64, iv, bound);
            fb.annotate_last(ProofAnnotation::InBounds)
                .expect("annotate probe");
        }
    }
    let addr = fb.gep(elem.clone(), p, vec![iv]);
    let v = fb.load(elem.clone(), addr);
    let mut next = Vec::new();
    let in_body = if latch.is_some() { 1 } else { shape.ops.len() };
    for (op, acc) in shape.ops.iter().zip(&accs).take(in_body) {
        next.push(fb.binop(*op, elem.clone(), *acc, v));
    }
    if let Some(latch) = latch {
        fb.br(latch, vec![]);
        fb.switch_to_block(latch);
        let addr2 = fb.gep(elem.clone(), p, vec![iv]);
        let v2 = fb.load(elem.clone(), addr2);
        for (op, acc) in shape.ops.iter().zip(&accs).skip(next.len()) {
            next.push(fb.binop(*op, elem.clone(), *acc, v2));
        }
    }
    let one = fb.iconst(Ty::U64, 1);
    let iv_next = fb.add(Ty::U64, iv, one);
    let mut back = vec![iv_next];
    back.extend(next);
    fb.br(header, back);

    // exit: combine the accumulators (and maybe the induction).
    fb.switch_to_block(exit);
    let mut result = fb.iconst(Ty::U64, 0);
    for (j, acc) in exit_accs.iter().enumerate() {
        let wide = if elem_bits(&elem) == 64 {
            *acc
        } else {
            fb.zext(elem.clone(), Ty::U64, *acc)
        };
        let k = fb.iconst(Ty::U64, i128::from(0x9E37_79B9_u64 + j as u64));
        let mixed = fb.mul(Ty::U64, result, k);
        result = fb.binop(BinOp::Xor, Ty::U64, mixed, wide);
    }
    if shape.exit_reads_iv {
        let k = fb.iconst(Ty::U64, 1_000_003);
        let scaled = fb.mul(Ty::U64, exit_iv, k);
        result = fb.add(Ty::U64, result, scaled);
    }
    if shape.exit_retests_bound {
        let (cc, n3) = header_bound(&mut fb, shape.bound, n_rt);
        let still = fb.icmp(cc, Ty::U64, exit_iv, n3);
        let bad = fb.iconst(Ty::U64, 0x0BAD);
        result = fb.select(Ty::U64, still, bad, result);
    }
    if let Some((_, _, oh, j, total, _, _, _)) = outer {
        let k31 = fb.iconst(Ty::U64, 31);
        let scaled = fb.mul(Ty::U64, total, k31);
        let total2 = fb.add(Ty::U64, scaled, result);
        let one = fb.iconst(Ty::U64, 1);
        let j2 = fb.add(Ty::U64, j, one);
        fb.br(oh, vec![j2, total2, exit_iv]);
    } else {
        fb.ret(vec![result]);
    }

    fb.switch_to_block(trap);
    let t = fb.iconst(Ty::U64, i128::from(TRAP));
    fb.ret(vec![t]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Plain-Rust model of the same loop over `data` (elements as u64, masked to
/// the element width).
fn model(shape: &Shape, data: &[u64], sel: u64, start_rt: u64, n_rt: u64) -> u64 {
    let bits = elem_bits(&shape.elem);
    let mask = if bits == 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    };
    let i = match shape.start {
        Start::Const(k) => k,
        Start::Param => start_rt,
        Start::SearchStop { limit } => {
            let mut j = 0u64;
            loop {
                j += 1;
                if j == limit || j == sel {
                    break j;
                }
            }
        }
        Start::Diamond {
            then_start,
            else_start,
        } => {
            if sel != 0 {
                then_start
            } else {
                else_start
            }
        }
    };
    let cont = |i: u64| match shape.bound {
        Bound::ConstUlt(n) => i < n,
        Bound::ConstSlt(n) => (i as i64) < (n as i64),
        Bound::ParamUlt => i < n_rt,
    };
    let seeds: Vec<u64> = shape.seeds.iter().map(|s| s & mask).collect();
    if let Some((trips, reset)) = shape.outer {
        let k = i;
        let mut total = 0u64;
        let mut ivc = k;
        for _ in 0..trips {
            let (i_end, r) = inner(shape, data, if reset { k } else { ivc }, &cont, mask);
            total = total.wrapping_mul(31).wrapping_add(r);
            ivc = i_end;
        }
        return total;
    }
    if shape.shared_exit && sel == SHARED_SEL {
        return finish(shape, SHARED_IV, &seeds, &cont);
    }
    inner(shape, data, i, &cont, mask).1
}

/// One run of the chain loop from `i`: the induction it exits with and the
/// exit block's result.
fn inner(
    shape: &Shape,
    data: &[u64],
    mut i: u64,
    cont: &dyn Fn(u64) -> bool,
    mask: u64,
) -> (u64, u64) {
    let mut accs: Vec<u64> = shape.seeds.iter().map(|s| s & mask).collect();
    while cont(i) {
        let v = data[i as usize] & mask;
        for (op, acc) in shape.ops.iter().zip(accs.iter_mut()) {
            *acc = match op {
                BinOp::And => *acc & v,
                BinOp::Or => *acc | v,
                BinOp::Xor => *acc ^ v,
                other => panic!("unsupported op {other:?}"),
            };
        }
        i += 1;
    }
    (i, finish(shape, i, &accs, cont))
}

/// The exit block's result for induction `i` and accumulators `accs`.
fn finish(shape: &Shape, i: u64, accs: &[u64], cont: &dyn Fn(u64) -> bool) -> u64 {
    let mut result = 0u64;
    for (j, acc) in accs.iter().enumerate() {
        result = result.wrapping_mul(0x9E37_79B9 + j as u64) ^ acc;
    }
    if shape.exit_reads_iv {
        result = result.wrapping_add(i.wrapping_mul(1_000_003));
    }
    if shape.exit_retests_bound && cont(i) {
        result = 0x0BAD;
    }
    result
}

/// Deterministic element data with every byte varied and the AND-chain not
/// collapsing to zero immediately.
fn data_for(len: usize) -> Vec<u64> {
    let mut x = 0x1234_5678_9ABC_DEF1_u64;
    (0..len)
        .map(|k| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            // Mostly-ones words so an AND chain stays informative.
            x | (0xF7FF_FFFF_FF7F_FFFF_u64.rotate_left(k as u32 % 64)) ^ ((k as u64) << (k % 61))
        })
        .collect()
}

/// Run `shape` at O2 and O3 on every `(sel, start, n)` row and compare with
/// the model. Returns the failures as text.
fn probe(shape: &Shape, rows: &[(u64, u64, u64)]) -> Vec<String> {
    let module = build_module(shape);
    let max_len = 4096 + 64;
    let data64 = data_for(max_len);
    let mut failures = Vec::new();
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = opt_level;
        let result = match Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &HashMap::new())
        {
            Ok(result) => result,
            Err(error) => {
                failures.push(format!(
                    "{} {opt_level:?}: compile refused: {error}",
                    shape.name
                ));
                continue;
            }
        };
        // SAFETY: the entry's trust-ir signature is (ptr, u64, u64, u64) ->
        // u64, and `result` outlives every call through `entry`.
        let entry = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*const u8, u64, u64, u64) -> u64>(shape.name)
        }
        .expect("entry symbol");
        for &(sel, start, n) in rows {
            let expected = model(shape, &data64, sel, start, n);
            let got = match elem_bits(&shape.elem) {
                8 => {
                    let d: Vec<u8> = data64.iter().map(|x| *x as u8).collect();
                    entry.as_ref()(d.as_ptr(), sel, start, n)
                }
                16 => {
                    let d: Vec<u16> = data64.iter().map(|x| *x as u16).collect();
                    entry.as_ref()(d.as_ptr().cast(), sel, start, n)
                }
                32 => {
                    let d: Vec<u32> = data64.iter().map(|x| *x as u32).collect();
                    entry.as_ref()(d.as_ptr().cast(), sel, start, n)
                }
                _ => entry.as_ref()(data64.as_ptr().cast(), sel, start, n),
            };
            if got != expected {
                failures.push(format!(
                    "{} {opt_level:?} sel={sel} start={start} n={n}: got {got:#x}, expected {expected:#x}",
                    shape.name
                ));
            }
        }
    }
    failures
}

const ROW0: &[(u64, u64, u64)] = &[(0, 0, 0), (1, 0, 0)];

fn base(name: &'static str, elem: Ty, n: u64) -> Shape {
    Shape {
        name,
        elem,
        ops: &[BinOp::Xor],
        seeds: &[0],
        start: Start::Const(0),
        bound: Bound::ConstUlt(n),
        middle_guard: true,
        exit_reads_iv: false,
        exit_retests_bound: false,
        outer: None,
        shared_exit: false,
    }
}

// --- Trip counts around the vector width (i32: 16, i64: 8) ------------------

#[test]
fn i32_xor_trip_counts_around_the_width() {
    let mut failures = Vec::new();
    for (name, n) in [
        ("x32_n1", 1u64),
        ("x32_n15", 15),
        ("x32_n16", 16),
        ("x32_n17", 17),
        ("x32_n31", 31),
        ("x32_n32", 32),
        ("x32_n33", 33),
        ("x32_n64", 64),
        ("x32_n2048", 2048),
        ("x32_n2047", 2047),
        ("x32_n4080", 4080),
    ] {
        failures.extend(probe(&base(name, Ty::U32, n), ROW0));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn i64_xor_trip_counts_around_the_width() {
    let mut failures = Vec::new();
    for (name, n) in [
        ("x64_n1", 1u64),
        ("x64_n7", 7),
        ("x64_n8", 8),
        ("x64_n9", 9),
        ("x64_n16", 16),
        ("x64_n24", 24),
        ("x64_n25", 25),
        ("x64_n1000", 1000),
    ] {
        failures.extend(probe(&base(name, Ty::U64, n), ROW0));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

// --- Entry value of the induction -------------------------------------------

#[test]
fn nonzero_constant_starts() {
    let mut failures = Vec::new();
    for (name, k, n) in [
        ("s16_n64", 16u64, 64u64),
        ("s3_n64", 3, 64),
        ("s64_n64", 64, 64),
        ("s48_n64", 48, 64),
        ("s5_n69", 5, 69),
        ("s70_n64", 70, 64),
    ] {
        let mut shape = base(name, Ty::U32, n);
        shape.start = Start::Const(k);
        failures.extend(probe(&shape, ROW0));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The induction's entry value is a block parameter merged from two
/// constants: only one of them leaves an empty tail.
#[test]
fn path_dependent_start() {
    let mut failures = Vec::new();
    for (name, then_start, else_start, n) in [
        ("pd_0_3_n64", 0u64, 3u64, 64u64),
        ("pd_3_0_n64", 3, 0, 64),
        ("pd_0_16_n64", 0, 16, 64),
        ("pd_0_5_n2048", 0, 5, 2048),
        ("pd_5_0_n2048", 5, 0, 2048),
    ] {
        let mut shape = base(name, Ty::U32, n);
        shape.start = Start::Diamond {
            then_start,
            else_start,
        };
        failures.extend(probe(&shape, &[(0, 0, 0), (1, 0, 0)]));
        let mut shape64 = base(name, Ty::U64, n);
        shape64.name = Box::leak(format!("{name}_x64").into_boxed_str());
        shape64.start = Start::Diamond {
            then_start,
            else_start,
        };
        failures.extend(probe(&shape64, &[(0, 0, 0), (1, 0, 0)]));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn runtime_start_and_runtime_bound() {
    let mut failures = Vec::new();
    let mut shape = base("rt_start", Ty::U32, 64);
    shape.start = Start::Param;
    failures.extend(probe(
        &shape,
        &[
            (0, 0, 0),
            (0, 3, 0),
            (0, 16, 0),
            (0, 63, 0),
            (0, 64, 0),
            (0, 65, 0),
        ],
    ));
    let mut shape = base("rt_bound", Ty::U32, 0);
    shape.bound = Bound::ParamUlt;
    failures.extend(probe(
        &shape,
        &[
            (0, 0, 0),
            (0, 0, 1),
            (0, 0, 15),
            (0, 0, 16),
            (0, 0, 17),
            (0, 0, 64),
            (0, 0, 65),
        ],
    ));
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn signed_bound() {
    let mut failures = Vec::new();
    for (name, n) in [("slt_n64", 64u64), ("slt_n65", 65)] {
        let mut shape = base(name, Ty::U32, n);
        shape.bound = Bound::ConstSlt(n);
        failures.extend(probe(&shape, ROW0));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

// --- What the exit observes ---------------------------------------------------

#[test]
fn exit_reads_induction_and_flags() {
    let mut failures = Vec::new();
    for (name, n, iv, retest) in [
        ("exit_iv_n64", 64u64, true, false),
        ("exit_iv_n65", 65, true, false),
        ("exit_retest_n64", 64, false, true),
        ("exit_both_n64", 64, true, true),
        ("exit_both_n64_x64", 64, true, true),
    ] {
        let mut shape = base(
            name,
            if name.ends_with("x64") {
                Ty::U64
            } else {
                Ty::U32
            },
            n,
        );
        shape.exit_reads_iv = iv;
        shape.exit_retests_bound = retest;
        failures.extend(probe(&shape, ROW0));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

// --- Reduction operators and identities ---------------------------------------

#[test]
fn and_or_xor_with_non_identity_seeds() {
    let mut failures = Vec::new();
    for (name, elem, n) in [
        ("ops_x32_n64", Ty::U32, 64u64),
        ("ops_x32_n2048", Ty::U32, 2048),
        ("ops_x64_n64", Ty::U64, 64),
        ("ops_x64_n8", Ty::U64, 8),
    ] {
        let mut shape = base(name, elem, n);
        shape.ops = &[BinOp::And, BinOp::Or, BinOp::Xor];
        shape.seeds = &[
            0xF0F0_F0F0_FFFF_FFF7,
            0x0000_0010_0000_0100,
            0x5555_AAAA_5555_AAAA,
        ];
        failures.extend(probe(&shape, ROW0));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn narrow_elements() {
    let mut failures = Vec::new();
    for (name, elem, n) in [
        ("x8_n64", Ty::U8, 64u64),
        ("x16_n64", Ty::U16, 64),
        ("x8_n65", Ty::U8, 65),
    ] {
        failures.extend(probe(&base(name, elem, n), ROW0));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn without_middle_guard() {
    let mut failures = Vec::new();
    for (name, n) in [("nomid_n64", 64u64), ("nomid_n65", 65)] {
        let mut shape = base(name, Ty::U32, n);
        shape.middle_guard = false;
        failures.extend(probe(&shape, ROW0));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The chain loop starts where a fully unrolled early-exit search stopped.
/// Unrolling rewrites the search's induction into one `Movz x, #k` per
/// unrolled iteration, so the register the chain's induction is copied from
/// has `limit` constant definitions, one per exit edge, and the layout-last
/// one is `Movz x, #limit`. With `N - limit` a multiple of the vector width,
/// only the path that stops at `limit` leaves the scalar tail empty: on every
/// early-exit path (`sel` in 1..limit) the vector loop stops short of `N`, and
/// the scalar tail must reduce the last `(N - sel) % width` elements. The
/// dead-tail skip therefore needs one entry value on every path and must
/// refuse this multi-def start register, which a last-wins def map resolves to
/// its layout-last `#limit`.
#[test]
fn dead_tail_skip_refuses_a_multi_def_start() {
    let mut failures = Vec::new();
    for (name, elem, limit, n) in [
        ("search8_x64_n64", Ty::U64, 8u64, 64u64),
        ("search16_x32_n64", Ty::U32, 16, 64),
        ("search8_x64_n2048", Ty::U64, 8, 2048),
    ] {
        let mut shape = base(name, elem, n);
        shape.start = Start::SearchStop { limit };
        let rows: Vec<(u64, u64, u64)> = (0..=limit + 1).map(|key| (key, 0, 0)).collect();
        failures.extend(probe(&shape, &rows));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The chain loop inside an outer loop: re-entered at its constant start on
/// every outer iteration, or resuming where the previous run stopped.
#[test]
fn chain_inside_an_outer_loop() {
    let mut failures = Vec::new();
    for (name, elem, k, n, reset) in [
        ("outer_reset_x32_n64", Ty::U32, 0u64, 64u64, true),
        ("outer_reset_x64_s8_n64", Ty::U64, 8, 64, true),
        ("outer_keep_x32_n64", Ty::U32, 0, 64, false),
        ("outer_keep_x32_n65", Ty::U32, 0, 65, false),
        ("outer_reset_x32_s3_n64", Ty::U32, 3, 64, true),
    ] {
        let mut shape = base(name, elem, n);
        shape.start = Start::Const(k);
        shape.outer = Some((3, reset));
        shape.exit_reads_iv = true;
        failures.extend(probe(&shape, ROW0));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The chain loop's exit is also entered from the function entry, bypassing
/// the loop, with a different induction and the seeds.
#[test]
fn exit_shared_with_a_bypass() {
    let mut failures = Vec::new();
    for (name, elem, n) in [
        ("shared_x32_n64", Ty::U32, 64u64),
        ("shared_x64_n64", Ty::U64, 64),
        ("shared_x32_n65", Ty::U32, 65),
    ] {
        let mut shape = base(name, elem, n);
        shape.shared_exit = true;
        shape.exit_reads_iv = true;
        shape.exit_retests_bound = true;
        failures.extend(probe(&shape, &[(0, 0, 0), (SHARED_SEL, 0, 0)]));
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
