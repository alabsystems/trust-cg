// trust-cg-codegen - loop recognizers against a step/offset register with several constant definitions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Induction steps, index offsets and address scales read from a register
//! written with different constants on different paths.
//!
//! The invariant these rows pin: a register written with different constants
//! on different paths is not one constant. Machine IR is not SSA: a register
//! written on several paths has several defs, and `build_reaching_def_map`
//! keeps one def per register, the layout-last. A recognizer that resolves
//! such a register through the layout-last def sees the constant it wants
//! (`1` for a step or offset, the element size for a scale) and vectorizes a
//! loop whose real stride, offset or scale is different.
//! `mach_util::const_value` and the pass-local resolvers (which delegate to
//! `mach_util::copied_const`) give a register a constant only when EVERY
//! definition of it writes that constant, so the multi-def rows below are
//! refused rather than read as their layout-last value.
//!
//! These tests JIT-run, at O2 and O3, loops whose induction step (`i += s`),
//! index offset (`a[i + s]`, `iv + s`) or address scale (`base + i * s`)
//! reads such a register `s`, and compare every result with a plain Rust
//! model of the same program. Three producers make `s` multi-def:
//!
//! * [`Src::Search`]: a fully unrolled early-exit search that writes
//!   `Movz s, #k` on every exit edge, the layout-last being the constant the
//!   recognizer wants;
//! * [`Src::Diamond`]: a phi of two constants joined by a diamond;
//! * [`Src::Carried`]: a constant carried around an outer loop, written before
//!   it and in its latch.
//!
//! The diamond and the carried constant reach machine IR as `MovR s, t` copies
//! of single-def `Movz t` registers, which the `Movz`-only resolvers do not
//! follow; they are kept as probes of the same sites. [`Src::Unit`] is the
//! single-def control: the same kernel with `s` the constant the recognizer
//! wants, which every pass under test vectorizes.
//!
//! Each kernel names the pass it targets and its `TRUST_CG_DISABLE_PASSES`
//! key. Setting `TRUST_CG_DUMP_MIR=<function name>` (for example
//! `lw_reduce_iv_search`) prints `=== after pass [<pass>] ===` when that pass
//! changes the function. Each test names the recognizer site it probes. The
//! cases are bounded executions on the host, not a proof.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, BlockId, CastOp, ICmpOp, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

/// Where the step/offset/scale register `s` comes from. `unit` is the
/// constant the recognizer under test wants.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Src {
    /// `j = unit + SPAN; loop { j -= 1; if j == unit || j == sel { break } };
    /// s = j`. O2/O3 unroll the search fully into one `Movz s, #k` per exit
    /// edge, the layout-last being `#unit`; `s == sel` whenever
    /// `unit <= sel < unit + SPAN`, else `s == unit`.
    Search,
    /// `s = if sel == 0 { unit + 1 } else { unit }`, a diamond whose `unit`
    /// arm is laid out last.
    Diamond,
    /// `s = unit + 1; k = 0; while k < sel { KERNEL(s); s = unit; k += 1 }`:
    /// a loop-carried constant written before the outer loop and in its latch.
    Carried,
    /// Control: `s = unit`, a single-def constant.
    Unit,
}

const ALL_SRCS: [Src; 4] = [Src::Search, Src::Diamond, Src::Carried, Src::Unit];

/// Number of exit edges of the unrolled search.
const SPAN: i64 = 4;

/// Elements in each buffer (8 bytes each, so every element type fits).
const CAP: usize = 160;

/// The `s` every kernel run uses under `src`, `sel` and `unit`.
fn steps(src: Src, sel: i64, unit: i64) -> Vec<i64> {
    match src {
        Src::Search => vec![if (unit..unit + SPAN).contains(&sel) {
            sel
        } else {
            unit
        }],
        Src::Diamond => vec![if sel == 0 { unit + 1 } else { unit }],
        Src::Carried => (0..sel.max(0))
            .map(|k| if k == 0 { unit + 1 } else { unit })
            .collect(),
        Src::Unit => vec![unit],
    }
}

/// The `sel` values each source is probed with.
fn sels(src: Src, unit: i64) -> Vec<i64> {
    match src {
        Src::Search => (unit - 1..=unit + SPAN).collect(),
        Src::Diamond => vec![0, 1, 5],
        Src::Carried => vec![0, 1, 2, 3],
        Src::Unit => vec![0],
    }
}

/// Function parameters a kernel reads.
struct Cx {
    a: ValueId,
    b: ValueId,
    /// The element count as `I64`.
    n: ValueId,
}

/// A kernel builder: emits from the current block a loop that reads `s`
/// (typed `Kernel::ty`) and ends with `br cont(result: I64)`.
type Build = fn(&mut FunctionBuilder<'_>, &Cx, ValueId, BlockId);
/// The kernel's model over the two byte buffers: `(a, b, n, s) -> result`.
type Model = fn(&mut [u8], &mut [u8], i64, i64) -> i64;
/// Kernel-specific buffer contents, applied over the random fill.
type Prep = fn(&mut [u8], &mut [u8]);

struct Kernel {
    name: &'static str,
    /// Type of `s`.
    ty: Ty,
    /// The constant the recognizer under test wants `s` to be.
    unit: i64,
    build: Build,
    model: Model,
    prep: Prep,
    /// The pass under test, as `TRUST_CG_DUMP_MIR` names it.
    pass: &'static str,
    /// Its `TRUST_CG_DISABLE_PASSES` key.
    key: &'static str,
}

fn build_module(fname: &str, kernel: &Kernel, src: Src) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new(fname);
    let fty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::I64, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function(fname, fty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let b = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, Ty::I64);
    let sel = fb.add_block_param(entry, Ty::I64);
    let cx = Cx { a, b, n };
    let ty = kernel.ty.clone();
    let unit = i128::from(kernel.unit);
    let exit = fb.create_block();
    let result = fb.add_block_param(exit, Ty::I64);

    fb.switch_to_block(entry);
    let sel_t = if ty == Ty::I64 {
        sel
    } else {
        fb.trunc(Ty::I64, ty.clone(), sel)
    };
    match src {
        Src::Unit => {
            let pre = fb.create_block();
            fb.br(pre, vec![]);
            fb.switch_to_block(pre);
            let s = fb.iconst(ty.clone(), unit);
            (kernel.build)(&mut fb, &cx, s, exit);
        }
        Src::Search => {
            let pre = fb.create_block();
            let s = fb.add_block_param(pre, ty.clone());
            let search = fb.create_block();
            let j = fb.add_block_param(search, ty.clone());
            let test = fb.create_block();
            let start = fb.iconst(ty.clone(), unit + i128::from(SPAN));
            fb.br(search, vec![start]);
            fb.switch_to_block(search);
            let one = fb.iconst(ty.clone(), 1);
            let next = fb.sub(ty.clone(), j, one);
            fb.br(test, vec![]);
            fb.switch_to_block(test);
            let last = fb.iconst(ty.clone(), unit);
            let trip = fb.icmp(ICmpOp::Ne, ty.clone(), next, last);
            let not_found = fb.icmp(ICmpOp::Ne, ty.clone(), next, sel_t);
            let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
            fb.condbr(more, search, vec![next], pre, vec![next]);
            fb.switch_to_block(pre);
            (kernel.build)(&mut fb, &cx, s, exit);
        }
        Src::Diamond => {
            let pre = fb.create_block();
            let s = fb.add_block_param(pre, ty.clone());
            let arm_other = fb.create_block();
            let arm_unit = fb.create_block();
            let zero = fb.iconst(ty.clone(), 0);
            let is_zero = fb.icmp(ICmpOp::Eq, ty.clone(), sel_t, zero);
            fb.condbr(is_zero, arm_other, vec![], arm_unit, vec![]);
            fb.switch_to_block(arm_other);
            let other = fb.iconst(ty.clone(), unit + 1);
            fb.br(pre, vec![other]);
            fb.switch_to_block(arm_unit);
            let u = fb.iconst(ty.clone(), unit);
            fb.br(pre, vec![u]);
            fb.switch_to_block(pre);
            (kernel.build)(&mut fb, &cx, s, exit);
        }
        Src::Carried => {
            let outer = fb.create_block();
            let k = fb.add_block_param(outer, Ty::I64);
            let s = fb.add_block_param(outer, ty.clone());
            let tot = fb.add_block_param(outer, Ty::I64);
            let run = fb.create_block();
            let olatch = fb.create_block();
            let r = fb.add_block_param(olatch, Ty::I64);
            let k0 = fb.iconst(Ty::I64, 0);
            let first = fb.iconst(ty.clone(), unit + 1);
            let t0 = fb.iconst(Ty::I64, 0);
            fb.br(outer, vec![k0, first, t0]);
            fb.switch_to_block(outer);
            let more = fb.icmp(ICmpOp::Slt, Ty::I64, k, sel);
            fb.condbr(more, run, vec![], exit, vec![tot]);
            fb.switch_to_block(run);
            (kernel.build)(&mut fb, &cx, s, olatch);
            fb.switch_to_block(olatch);
            let m31 = fb.iconst(Ty::I64, 31);
            let scaled = fb.mul(Ty::I64, tot, m31);
            let tot2 = fb.add(Ty::I64, scaled, r);
            let one64 = fb.iconst(Ty::I64, 1);
            let k2 = fb.add(Ty::I64, k, one64);
            let u = fb.iconst(ty.clone(), unit);
            fb.br(outer, vec![k2, u, tot2]);
        }
    }
    fb.switch_to_block(exit);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn run_model(kernel: &Kernel, src: Src, sel: i64, a: &mut [u8], b: &mut [u8], n: i64) -> i64 {
    let mut tot = 0i64;
    for s in steps(src, sel, kernel.unit) {
        let r = (kernel.model)(a, b, n, s);
        tot = if src == Src::Carried {
            tot.wrapping_mul(31).wrapping_add(r)
        } else {
            r
        };
    }
    tot
}

// ---------------------------------------------------------------------------
// Byte-buffer accessors for the models
// ---------------------------------------------------------------------------

fn rd_i32_at(m: &[u8], off: i64) -> i32 {
    let o = off as usize;
    i32::from_le_bytes(m[o..o + 4].try_into().unwrap())
}
fn wr_i32_at(m: &mut [u8], off: i64, v: i32) {
    let o = off as usize;
    m[o..o + 4].copy_from_slice(&v.to_le_bytes());
}
fn rd_i32(m: &[u8], i: i64) -> i32 {
    rd_i32_at(m, i * 4)
}
fn wr_i32(m: &mut [u8], i: i64, v: i32) {
    wr_i32_at(m, i * 4, v);
}
fn rd_f32(m: &[u8], i: i64) -> f32 {
    f32::from_bits(rd_i32(m, i) as u32)
}
fn wr_f32(m: &mut [u8], i: i64, v: f32) {
    wr_i32(m, i, v.to_bits() as i32);
}
fn rd_i64(m: &[u8], i: i64) -> i64 {
    let o = i as usize * 8;
    i64::from_le_bytes(m[o..o + 8].try_into().unwrap())
}
fn wr_i64(m: &mut [u8], i: i64, v: i64) {
    let o = i as usize * 8;
    m[o..o + 8].copy_from_slice(&v.to_le_bytes());
}
fn rd_f64(m: &[u8], i: i64) -> f64 {
    f64::from_bits(rd_i64(m, i) as u64)
}
fn wr_f64(m: &mut [u8], i: i64, v: f64) {
    wr_i64(m, i, v.to_bits() as i64);
}

// ---------------------------------------------------------------------------
// Loop scaffolding shared by the kernels
// ---------------------------------------------------------------------------

/// `i = 0; while i <s n { acc = BODY(i, acc); i += step }` over `iv_ty`, with
/// one carried value `acc` (typed `acc_ty`, seeded `seed`). Ends with
/// `br cont(widen(acc))`.
#[allow(clippy::too_many_arguments)]
fn counted_loop(
    fb: &mut FunctionBuilder<'_>,
    cx: &Cx,
    step: ValueId,
    cont: BlockId,
    iv_ty: Ty,
    acc_ty: Ty,
    seed: ValueId,
    body: &dyn Fn(&mut FunctionBuilder<'_>, ValueId, ValueId) -> ValueId,
    widen: &dyn Fn(&mut FunctionBuilder<'_>, ValueId) -> ValueId,
) {
    let header = fb.create_block();
    let iv = fb.add_block_param(header, iv_ty.clone());
    let acc = fb.add_block_param(header, acc_ty.clone());
    let latch = fb.create_block();
    let done = fb.create_block();
    let out = fb.add_block_param(done, acc_ty.clone());
    let n_t = if iv_ty == Ty::I64 {
        cx.n
    } else {
        fb.trunc(Ty::I64, iv_ty.clone(), cx.n)
    };
    let zero = fb.iconst(iv_ty.clone(), 0);
    fb.br(header, vec![zero, seed]);
    fb.switch_to_block(header);
    let go = fb.icmp(ICmpOp::Slt, iv_ty.clone(), iv, n_t);
    fb.condbr(go, latch, vec![], done, vec![acc]);
    fb.switch_to_block(latch);
    let acc2 = body(fb, iv, acc);
    let iv2 = fb.add(iv_ty.clone(), iv, step);
    fb.br(header, vec![iv2, acc2]);
    fb.switch_to_block(done);
    let w = widen(fb, out);
    fb.br(cont, vec![w]);
}

/// An `i32` counted loop with an `i32` accumulator returned sign-extended.
fn i32_loop(
    fb: &mut FunctionBuilder<'_>,
    cx: &Cx,
    step: ValueId,
    cont: BlockId,
    seed: i128,
    body: &dyn Fn(&mut FunctionBuilder<'_>, ValueId, ValueId) -> ValueId,
) {
    let seed = fb.iconst(Ty::I32, seed);
    counted_loop(
        fb,
        cx,
        step,
        cont,
        Ty::I32,
        Ty::I32,
        seed,
        body,
        &|fb, v| fb.sext(Ty::I32, Ty::I64, v),
    );
}

/// `a[i]` over `i32` elements with an `i32` index.
fn load_i32(fb: &mut FunctionBuilder<'_>, base: ValueId, i: ValueId) -> (ValueId, ValueId) {
    let ix = fb.sext(Ty::I32, Ty::I64, i);
    let p = fb.gep(Ty::I32, base, vec![ix]);
    (p, fb.load(Ty::I32, p))
}

/// `*(i32*)(base + sext(i) * scale)`: the address as integer arithmetic, so
/// the element-size factor is the register `scale`.
fn load_i32_scaled(
    fb: &mut FunctionBuilder<'_>,
    base: ValueId,
    i: ValueId,
    scale: ValueId,
) -> (ValueId, ValueId) {
    let ix = fb.sext(Ty::I32, Ty::I64, i);
    let off = fb.mul(Ty::I64, ix, scale);
    let b = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, base);
    let addr = fb.add(Ty::I64, b, off);
    let p = fb.cast(CastOp::IntToPtr, Ty::I64, Ty::Ptr, addr);
    (p, fb.load(Ty::I32, p))
}

fn no_prep(_a: &mut [u8], _b: &mut [u8]) {}

// ---------------------------------------------------------------------------
// Step kernels: `i += s` with the layout-last `s` = 1
// ---------------------------------------------------------------------------

/// neon-reduce induction term: `acc: i32 += i * 3`.
fn build_reduce_iv(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    i32_loop(fb, cx, s, cont, 0, &|fb, iv, acc| {
        let three = fb.iconst(Ty::I32, 3);
        let t = fb.mul(Ty::I32, iv, three);
        fb.add(Ty::I32, acc, t)
    });
}
fn model_reduce_iv(_a: &mut [u8], _b: &mut [u8], n: i64, s: i64) -> i64 {
    let (mut acc, mut i) = (0i32, 0i32);
    while i64::from(i) < n {
        acc = acc.wrapping_add(i.wrapping_mul(3));
        i = i.wrapping_add(s as i32);
    }
    i64::from(acc)
}

/// neon-array memory term: `acc: i32 += a[i]`.
fn build_sum_mem(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let a = cx.a;
    i32_loop(fb, cx, s, cont, 0, &|fb, iv, acc| {
        let (_, v) = load_i32(fb, a, iv);
        fb.add(Ty::I32, acc, v)
    });
}
fn model_sum_mem(a: &mut [u8], _b: &mut [u8], n: i64, s: i64) -> i64 {
    let (mut acc, mut i) = (0i32, 0i64);
    while i < n {
        acc = acc.wrapping_add(rd_i32(a, i));
        i += s;
    }
    i64::from(acc)
}

/// neon-map in place: `a[i] = a[i] + 7` (i32).
fn build_map_inplace(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let a = cx.a;
    i32_loop(fb, cx, s, cont, 0, &|fb, iv, acc| {
        let (p, v) = load_i32(fb, a, iv);
        let seven = fb.iconst(Ty::I32, 7);
        let w = fb.add(Ty::I32, v, seven);
        fb.store(Ty::I32, p, w);
        acc
    });
}
fn model_map_inplace(a: &mut [u8], _b: &mut [u8], n: i64, s: i64) -> i64 {
    let mut i = 0i64;
    while i < n {
        let v = rd_i32(a, i).wrapping_add(7);
        wr_i32(a, i, v);
        i += s;
    }
    0
}

/// neon-map descending in place: `i = n - 1; while i >= 0 { a[i] += 7;
/// i -= s }` (`SubRR(iv, s)`).
fn build_map_desc(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let header = fb.create_block();
    let iv = fb.add_block_param(header, Ty::I32);
    let body = fb.create_block();
    let n32 = fb.trunc(Ty::I64, Ty::I32, cx.n);
    let one = fb.iconst(Ty::I32, 1);
    let start = fb.sub(Ty::I32, n32, one);
    fb.br(header, vec![start]);
    fb.switch_to_block(header);
    let zero = fb.iconst(Ty::I32, 0);
    let go = fb.icmp(ICmpOp::Sge, Ty::I32, iv, zero);
    let r = fb.iconst(Ty::I64, 0);
    fb.condbr(go, body, vec![], cont, vec![r]);
    fb.switch_to_block(body);
    let (p, v) = load_i32(fb, cx.a, iv);
    let seven = fb.iconst(Ty::I32, 7);
    let w = fb.add(Ty::I32, v, seven);
    fb.store(Ty::I32, p, w);
    let iv2 = fb.sub(Ty::I32, iv, s);
    fb.br(header, vec![iv2]);
}
fn model_map_desc(a: &mut [u8], _b: &mut [u8], n: i64, s: i64) -> i64 {
    let mut i = n - 1;
    while i >= 0 {
        let v = rd_i32(a, i).wrapping_add(7);
        wr_i32(a, i, v);
        i -= s;
    }
    0
}

/// neon-minmax: `m = max(m, a[i])` (signed i32, seeded i32::MIN).
fn build_max(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let a = cx.a;
    i32_loop(fb, cx, s, cont, i128::from(i32::MIN), &|fb, iv, acc| {
        let (_, v) = load_i32(fb, a, iv);
        let gt = fb.icmp(ICmpOp::Sgt, Ty::I32, v, acc);
        fb.select(Ty::I32, gt, v, acc)
    });
}
fn model_max(a: &mut [u8], _b: &mut [u8], n: i64, s: i64) -> i64 {
    let (mut m, mut i) = (i32::MIN, 0i64);
    while i < n {
        m = m.max(rd_i32(a, i));
        i += s;
    }
    i64::from(m)
}
/// The maximum sits at odd index 9 only.
fn prep_max(a: &mut [u8], _b: &mut [u8]) {
    wr_i32(a, 9, i32::MAX - 3);
}

/// neon-predsum: `acc += if a[i] > 5000 { a[i] } else { 0 }` (i32 select).
fn build_predsum(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let a = cx.a;
    i32_loop(fb, cx, s, cont, 0, &|fb, iv, acc| {
        let (_, v) = load_i32(fb, a, iv);
        let zero = fb.iconst(Ty::I32, 0);
        let lim = fb.iconst(Ty::I32, 5000);
        let pos = fb.icmp(ICmpOp::Sgt, Ty::I32, v, lim);
        let t = fb.select(Ty::I32, pos, v, zero);
        fb.add(Ty::I32, acc, t)
    });
}
fn model_predsum(a: &mut [u8], _b: &mut [u8], n: i64, s: i64) -> i64 {
    let (mut acc, mut i) = (0i32, 0i64);
    while i < n {
        let v = rd_i32(a, i);
        if v > 5000 {
            acc = acc.wrapping_add(v);
        }
        i += s;
    }
    i64::from(acc)
}

/// neon-find: `for i: if a[i] == 7777 { return i }; return -1` (i32).
fn build_find(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let header = fb.create_block();
    let iv = fb.add_block_param(header, Ty::I32);
    let body = fb.create_block();
    let latch = fb.create_block();
    let hit_blk = fb.create_block();
    let n32 = fb.trunc(Ty::I64, Ty::I32, cx.n);
    let zero = fb.iconst(Ty::I32, 0);
    fb.br(header, vec![zero]);
    fb.switch_to_block(header);
    let go = fb.icmp(ICmpOp::Slt, Ty::I32, iv, n32);
    let miss = fb.iconst(Ty::I64, -1);
    fb.condbr(go, body, vec![], cont, vec![miss]);
    fb.switch_to_block(body);
    let (_, v) = load_i32(fb, cx.a, iv);
    let key = fb.iconst(Ty::I32, 7777);
    let hit = fb.icmp(ICmpOp::Eq, Ty::I32, v, key);
    fb.condbr(hit, hit_blk, vec![], latch, vec![]);
    fb.switch_to_block(hit_blk);
    let found = fb.sext(Ty::I32, Ty::I64, iv);
    fb.br(cont, vec![found]);
    fb.switch_to_block(latch);
    let iv2 = fb.add(Ty::I32, iv, s);
    fb.br(header, vec![iv2]);
}
fn model_find(a: &mut [u8], _b: &mut [u8], n: i64, s: i64) -> i64 {
    let mut i = 0i64;
    while i < n {
        if rd_i32(a, i) == 7777 {
            return i;
        }
        i += s;
    }
    -1
}
/// The key sits at 18 and 40. A stride-3 scan from 0 meets 18; one resumed at
/// the 16-element block base 16 steps 16, 19, ... past it.
fn prep_find(a: &mut [u8], _b: &mut [u8]) {
    wr_i32(a, 18, 7777);
    wr_i32(a, 40, 7777);
}

/// neon-fmap in place: `a[i] = a[i] * 2.0 + 1.0` (f64, i32 index).
fn build_fmap(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let a = cx.a;
    i32_loop(fb, cx, s, cont, 0, &|fb, iv, acc| {
        let ix = fb.sext(Ty::I32, Ty::I64, iv);
        let p = fb.gep(Ty::F64, a, vec![ix]);
        let v = fb.load(Ty::F64, p);
        let two = fb.fconst(Ty::F64, 2.0);
        let w = fb.binop(BinOp::FMul, Ty::F64, v, two);
        let one = fb.fconst(Ty::F64, 1.0);
        let x = fb.binop(BinOp::FAdd, Ty::F64, w, one);
        fb.store(Ty::F64, p, x);
        acc
    });
}
fn model_fmap(a: &mut [u8], _b: &mut [u8], n: i64, s: i64) -> i64 {
    let mut i = 0i64;
    while i < n {
        let v = rd_f64(a, i) * 2.0 + 1.0;
        wr_f64(a, i, v);
        i += s;
    }
    0
}
/// Distinct finite f64 elements.
fn prep_f64_ramp(a: &mut [u8], _b: &mut [u8]) {
    for k in 0..CAP as i64 {
        wr_f64(a, k, k as f64 * 0.75 - 3.0);
    }
}

/// Bytes the bytesum kernel reads.
const BYTES: i128 = 128;

/// neon-bytesum: `while i <u 128 { if !(i <u 128) { return -7 }; acc: u64 +=
/// a_u8[i]; i += s }`, the bounds-checked chain a safe-Rust index lowers to.
fn build_bytesum(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let a = cx.a;
    let header = fb.create_block();
    let iv = fb.add_block_param(header, Ty::I64);
    let acc = fb.add_block_param(header, Ty::I64);
    let check = fb.create_block();
    let j = fb.add_block_param(check, Ty::I64);
    let body = fb.create_block();
    let oob = fb.create_block();
    let zero = fb.iconst(Ty::I64, 0);
    let seed = fb.iconst(Ty::I64, 0);
    fb.br(header, vec![zero, seed]);
    fb.switch_to_block(header);
    let nn = fb.iconst(Ty::I64, BYTES);
    let go = fb.icmp(ICmpOp::Ult, Ty::I64, iv, nn);
    fb.condbr(go, check, vec![iv], cont, vec![acc]);
    fb.switch_to_block(check);
    let nn2 = fb.iconst(Ty::I64, BYTES);
    let inb = fb.icmp(ICmpOp::Ult, Ty::I64, j, nn2);
    fb.condbr(inb, body, vec![], oob, vec![]);
    fb.switch_to_block(oob);
    let bad = fb.iconst(Ty::I64, -7);
    fb.br(cont, vec![bad]);
    fb.switch_to_block(body);
    let base = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, a);
    let addr = fb.add(Ty::I64, base, iv);
    let p = fb.cast(CastOp::IntToPtr, Ty::I64, Ty::Ptr, addr);
    let v = fb.load(Ty::U8, p);
    let w = fb.zext(Ty::U8, Ty::I64, v);
    let acc2 = fb.add(Ty::I64, acc, w);
    let iv2 = fb.add(Ty::I64, iv, s);
    fb.br(header, vec![iv2, acc2]);
}
fn model_bytesum(a: &mut [u8], _b: &mut [u8], _n: i64, s: i64) -> i64 {
    let (mut acc, mut i) = (0u64, 0u64);
    while i < BYTES as u64 {
        acc = acc.wrapping_add(u64::from(a[i as usize]));
        i = i.wrapping_add(s as u64);
    }
    acc as i64
}

/// Constant trip bound of the f64 IV reduction.
const FPRED_N: i64 = 5000;

/// neon-fpred: `i = 0; do { acc: f64 += (double)i * 0.5; i += s } while
/// !(i >= FPRED_N)`, stored to `b[0]`.
fn build_fpred(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let header = fb.create_block();
    let iv = fb.add_block_param(header, Ty::I64);
    let acc = fb.add_block_param(header, Ty::F64);
    let done = fb.create_block();
    let out = fb.add_block_param(done, Ty::F64);
    let zero = fb.iconst(Ty::I64, 0);
    let seed = fb.fconst(Ty::F64, 0.0);
    fb.br(header, vec![zero, seed]);
    fb.switch_to_block(header);
    let d = fb.cast(CastOp::SIToFP, Ty::I64, Ty::F64, iv);
    let half = fb.fconst(Ty::F64, 0.5);
    let t = fb.binop(BinOp::FMul, Ty::F64, d, half);
    let acc2 = fb.binop(BinOp::FAdd, Ty::F64, acc, t);
    let iv2 = fb.add(Ty::I64, iv, s);
    let bound = fb.iconst(Ty::I64, i128::from(FPRED_N));
    let finished = fb.icmp(ICmpOp::Sge, Ty::I64, iv2, bound);
    fb.condbr(finished, done, vec![acc2], header, vec![iv2, acc2]);
    fb.switch_to_block(done);
    fb.store(Ty::F64, cx.b, out);
    let r = fb.iconst(Ty::I64, 0);
    fb.br(cont, vec![r]);
}
fn model_fpred(_a: &mut [u8], b: &mut [u8], _n: i64, s: i64) -> i64 {
    let (mut acc, mut i) = (0.0f64, 0i64);
    loop {
        acc += i as f64 * 0.5;
        i += s;
        if i >= FPRED_N {
            break;
        }
    }
    wr_f64(b, 0, acc);
    0
}

/// f64 slot of `b` the f64 array reduction stores its result to (past every
/// element the loop reads).
const FARRAY_OUT: i64 = 150;

/// neon-farray widening dot: `if 0 < n { i = 0; do { acc: f64 += (f64)a[i] *
/// (f64)b[i]; i += s } while !(i >= n) }` over f32 arrays, stored to
/// `b_f64[FARRAY_OUT]`.
fn build_farray(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let header = fb.create_block();
    let iv = fb.add_block_param(header, Ty::I64);
    let acc = fb.add_block_param(header, Ty::F64);
    let done = fb.create_block();
    let out = fb.add_block_param(done, Ty::F64);
    let zero = fb.iconst(Ty::I64, 0);
    let seed = fb.fconst(Ty::F64, 0.0);
    let nonempty = fb.icmp(ICmpOp::Slt, Ty::I64, zero, cx.n);
    fb.condbr(nonempty, header, vec![zero, seed], done, vec![seed]);
    fb.switch_to_block(header);
    let pa = fb.gep(Ty::F32, cx.a, vec![iv]);
    let va = fb.load(Ty::F32, pa);
    let da = fb.cast(CastOp::FPExt, Ty::F32, Ty::F64, va);
    let pb = fb.gep(Ty::F32, cx.b, vec![iv]);
    let vb = fb.load(Ty::F32, pb);
    let db = fb.cast(CastOp::FPExt, Ty::F32, Ty::F64, vb);
    let t = fb.binop(BinOp::FMul, Ty::F64, da, db);
    let acc2 = fb.binop(BinOp::FAdd, Ty::F64, acc, t);
    let iv2 = fb.add(Ty::I64, iv, s);
    let finished = fb.icmp(ICmpOp::Sge, Ty::I64, iv2, cx.n);
    fb.condbr(finished, done, vec![acc2], header, vec![iv2, acc2]);
    fb.switch_to_block(done);
    let slot = fb.iconst(Ty::I64, i128::from(FARRAY_OUT));
    let p = fb.gep(Ty::F64, cx.b, vec![slot]);
    fb.store(Ty::F64, p, out);
    let r = fb.iconst(Ty::I64, 0);
    fb.br(cont, vec![r]);
}
fn model_farray(a: &mut [u8], b: &mut [u8], n: i64, s: i64) -> i64 {
    let (mut acc, mut i) = (0.0f64, 0i64);
    if 0 < n {
        loop {
            acc += f64::from(rd_f32(a, i)) * f64::from(rd_f32(b, i));
            i += s;
            if i >= n {
                break;
            }
        }
    }
    wr_f64(b, FARRAY_OUT, acc);
    0
}
/// Small finite f32 elements in both arrays.
fn prep_farray(a: &mut [u8], b: &mut [u8]) {
    for k in 0..(CAP as i64) {
        wr_f32(a, k, (k % 13) as f32 * 0.5 - 2.0);
        wr_f32(b, k, (k % 7) as f32 * 0.25 + 1.0);
    }
}

/// closed-form-reduction: `acc: i64 += i * 5 + 3` over an i64 induction.
fn build_closed_form(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let seed = fb.iconst(Ty::I64, 0);
    counted_loop(
        fb,
        cx,
        s,
        cont,
        Ty::I64,
        Ty::I64,
        seed,
        &|fb, iv, acc| {
            let five = fb.iconst(Ty::I64, 5);
            let t5 = fb.mul(Ty::I64, iv, five);
            let three = fb.iconst(Ty::I64, 3);
            let t = fb.add(Ty::I64, t5, three);
            fb.add(Ty::I64, acc, t)
        },
        &|_, v| v,
    );
}
fn model_closed_form(_a: &mut [u8], _b: &mut [u8], n: i64, s: i64) -> i64 {
    let (mut acc, mut i) = (0i64, 0i64);
    while i < n {
        acc = acc.wrapping_add(i.wrapping_mul(5).wrapping_add(3));
        i += s;
    }
    acc
}

// ---------------------------------------------------------------------------
// Offset kernels: unit step, `iv + s` / `a[i + s]` with the layout-last s = 1
// ---------------------------------------------------------------------------

/// neon-array shifted iota: `acc: i32 += (i + s) ^ a[i]`, step 1.
fn build_iota_array(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let a = cx.a;
    let one = fb.iconst(Ty::I32, 1);
    i32_loop(fb, cx, one, cont, 0, &|fb, iv, acc| {
        let (_, v) = load_i32(fb, a, iv);
        let sh = fb.add(Ty::I32, iv, s);
        let t = fb.binop(BinOp::Xor, Ty::I32, sh, v);
        fb.add(Ty::I32, acc, t)
    });
}
fn model_iota_array(a: &mut [u8], _b: &mut [u8], n: i64, s: i64) -> i64 {
    let mut acc = 0i32;
    for i in 0..n.max(0) {
        acc = acc.wrapping_add((i as i32).wrapping_add(s as i32) ^ rd_i32(a, i));
    }
    i64::from(acc)
}

/// neon-fmap in place with a shifted read: `a[i] = a[i + s] * 2.0 + 1.0`
/// over f64, step 1. A shifted read of the store base is a carried
/// dependence the pass refuses, so the layout-last `s` is `0`.
fn build_fmap_off(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let a = cx.a;
    let one = fb.iconst(Ty::I32, 1);
    i32_loop(fb, cx, one, cont, 0, &|fb, iv, acc| {
        let j = fb.add(Ty::I32, iv, s);
        let jx = fb.sext(Ty::I32, Ty::I64, j);
        let p = fb.gep(Ty::F64, a, vec![jx]);
        let v = fb.load(Ty::F64, p);
        let two = fb.fconst(Ty::F64, 2.0);
        let w = fb.binop(BinOp::FMul, Ty::F64, v, two);
        let onef = fb.fconst(Ty::F64, 1.0);
        let x = fb.binop(BinOp::FAdd, Ty::F64, w, onef);
        let ix = fb.sext(Ty::I32, Ty::I64, iv);
        let q = fb.gep(Ty::F64, a, vec![ix]);
        fb.store(Ty::F64, q, x);
        acc
    });
}
fn model_fmap_off(a: &mut [u8], _b: &mut [u8], n: i64, s: i64) -> i64 {
    for i in 0..n.max(0) {
        let x = rd_f64(a, i + s) * 2.0 + 1.0;
        wr_f64(a, i, x);
    }
    0
}

/// Pseudo-random f64 elements in [-1, 1).
fn prep_f64_noise(a: &mut [u8], b: &mut [u8]) {
    let mut x = 0x2545_F491_4F6C_DD1D_u64;
    for k in 0..CAP as i64 {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        wr_f64(a, k, (x >> 11) as f64 / (1u64 << 53) as f64 * 2.0 - 1.0);
        wr_f64(b, k, 0.0);
    }
}

// ---------------------------------------------------------------------------
// Scale kernels: `*(i32*)(a + i * s)` with the layout-last s = 4
// ---------------------------------------------------------------------------

/// neon-map in place through a register-scaled address: `p = a + i * s;
/// *p = *p + 7` (i32 elements, step 1).
fn build_es_map(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let a = cx.a;
    let one = fb.iconst(Ty::I32, 1);
    i32_loop(fb, cx, one, cont, 0, &|fb, iv, acc| {
        let (p, v) = load_i32_scaled(fb, a, iv, s);
        let seven = fb.iconst(Ty::I32, 7);
        let w = fb.add(Ty::I32, v, seven);
        fb.store(Ty::I32, p, w);
        acc
    });
}
fn model_es_map(a: &mut [u8], _b: &mut [u8], n: i64, s: i64) -> i64 {
    for i in 0..n.max(0) {
        let v = rd_i32_at(a, i * s).wrapping_add(7);
        wr_i32_at(a, i * s, v);
    }
    0
}

/// neon-array through a register-scaled address: `acc += *(a + i * s)`.
fn build_es_sum(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let a = cx.a;
    let one = fb.iconst(Ty::I32, 1);
    i32_loop(fb, cx, one, cont, 0, &|fb, iv, acc| {
        let (_, v) = load_i32_scaled(fb, a, iv, s);
        fb.add(Ty::I32, acc, v)
    });
}
fn model_es_sum(a: &mut [u8], _b: &mut [u8], n: i64, s: i64) -> i64 {
    let mut acc = 0i32;
    for i in 0..n.max(0) {
        acc = acc.wrapping_add(rd_i32_at(a, i * s));
    }
    i64::from(acc)
}

/// neon-minmax through a register-scaled address: `m = max(m, *(a + i*s))`.
fn build_es_max(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let a = cx.a;
    let one = fb.iconst(Ty::I32, 1);
    i32_loop(fb, cx, one, cont, i128::from(i32::MIN), &|fb, iv, acc| {
        let (_, v) = load_i32_scaled(fb, a, iv, s);
        let gt = fb.icmp(ICmpOp::Sgt, Ty::I32, v, acc);
        fb.select(Ty::I32, gt, v, acc)
    });
}
fn model_es_max(a: &mut [u8], _b: &mut [u8], n: i64, s: i64) -> i64 {
    let mut m = i32::MIN;
    for i in 0..n.max(0) {
        m = m.max(rd_i32_at(a, i * s));
    }
    i64::from(m)
}

/// neon-minmax shifted iota under max: `m = max(m, (i + s) ^ a[i])`, step 1.
fn build_iota_max(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let a = cx.a;
    let one = fb.iconst(Ty::I32, 1);
    i32_loop(fb, cx, one, cont, i128::from(i32::MIN), &|fb, iv, acc| {
        let (_, v) = load_i32(fb, a, iv);
        let sh = fb.add(Ty::I32, iv, s);
        let t = fb.binop(BinOp::Xor, Ty::I32, sh, v);
        let gt = fb.icmp(ICmpOp::Sgt, Ty::I32, t, acc);
        fb.select(Ty::I32, gt, t, acc)
    });
}
fn model_iota_max(a: &mut [u8], _b: &mut [u8], n: i64, s: i64) -> i64 {
    let mut m = i32::MIN;
    for i in 0..n.max(0) {
        m = m.max((i as i32).wrapping_add(s as i32) ^ rd_i32(a, i));
    }
    i64::from(m)
}
/// Small non-negative i32 elements, so `(i + s) ^ a[i]` decides the maximum.
fn prep_small_i32(a: &mut [u8], _b: &mut [u8]) {
    for k in 0..(2 * CAP as i64) {
        wr_i32(a, k, ((k * 37) % 61) as i32);
    }
}

/// neon-predsum through a register-scaled address:
/// `acc += if *(a + i*s) > 5000 { *(a + i*s) } else { 0 }`.
fn build_es_predsum(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let a = cx.a;
    let one = fb.iconst(Ty::I32, 1);
    i32_loop(fb, cx, one, cont, 0, &|fb, iv, acc| {
        let (_, v) = load_i32_scaled(fb, a, iv, s);
        let zero = fb.iconst(Ty::I32, 0);
        let lim = fb.iconst(Ty::I32, 5000);
        let pos = fb.icmp(ICmpOp::Sgt, Ty::I32, v, lim);
        let t = fb.select(Ty::I32, pos, v, zero);
        fb.add(Ty::I32, acc, t)
    });
}
fn model_es_predsum(a: &mut [u8], _b: &mut [u8], n: i64, s: i64) -> i64 {
    let mut acc = 0i32;
    for i in 0..n.max(0) {
        let v = rd_i32_at(a, i * s);
        if v > 5000 {
            acc = acc.wrapping_add(v);
        }
    }
    i64::from(acc)
}

/// neon-find through a register-scaled address:
/// `for i: if *(a + i*s) == 7777 { return i }; return -1`.
fn build_es_find(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let header = fb.create_block();
    let iv = fb.add_block_param(header, Ty::I32);
    let body = fb.create_block();
    let latch = fb.create_block();
    let hit_blk = fb.create_block();
    let n32 = fb.trunc(Ty::I64, Ty::I32, cx.n);
    let zero = fb.iconst(Ty::I32, 0);
    fb.br(header, vec![zero]);
    fb.switch_to_block(header);
    let go = fb.icmp(ICmpOp::Slt, Ty::I32, iv, n32);
    let miss = fb.iconst(Ty::I64, -1);
    fb.condbr(go, body, vec![], cont, vec![miss]);
    fb.switch_to_block(body);
    let (_, v) = load_i32_scaled(fb, cx.a, iv, s);
    let key = fb.iconst(Ty::I32, 7777);
    let hit = fb.icmp(ICmpOp::Eq, Ty::I32, v, key);
    fb.condbr(hit, hit_blk, vec![], latch, vec![]);
    fb.switch_to_block(hit_blk);
    let found = fb.sext(Ty::I32, Ty::I64, iv);
    fb.br(cont, vec![found]);
    fb.switch_to_block(latch);
    let one = fb.iconst(Ty::I32, 1);
    let iv2 = fb.add(Ty::I32, iv, one);
    fb.br(header, vec![iv2]);
}
fn model_es_find(a: &mut [u8], _b: &mut [u8], n: i64, s: i64) -> i64 {
    for i in 0..n.max(0) {
        if rd_i32_at(a, i * s) == 7777 {
            return i;
        }
    }
    -1
}
/// The key at unaligned byte offsets 5, 18 and 35: scale 5 meets it at
/// i = 1, scale 6 at i = 3, scale 7 at i = 5, and no aligned i32 (the scale-4
/// view a 16-element block filter reads) holds it.
fn prep_es_find(a: &mut [u8], _b: &mut [u8]) {
    for off in [5, 18, 35] {
        wr_i32_at(a, off, 7777);
    }
}

/// neon-fmap in place through a register-scaled f64 address:
/// `p = a + i * s; *p = *p * 2.0 + 1.0`.
fn build_es_fmap(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let a = cx.a;
    let one = fb.iconst(Ty::I32, 1);
    i32_loop(fb, cx, one, cont, 0, &|fb, iv, acc| {
        let ix = fb.sext(Ty::I32, Ty::I64, iv);
        let off = fb.mul(Ty::I64, ix, s);
        let b = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, a);
        let addr = fb.add(Ty::I64, b, off);
        let p = fb.cast(CastOp::IntToPtr, Ty::I64, Ty::Ptr, addr);
        let v = fb.load(Ty::F64, p);
        let two = fb.fconst(Ty::F64, 2.0);
        let w = fb.binop(BinOp::FMul, Ty::F64, v, two);
        let onef = fb.fconst(Ty::F64, 1.0);
        let x = fb.binop(BinOp::FAdd, Ty::F64, w, onef);
        fb.store(Ty::F64, p, x);
        acc
    });
}
fn model_es_fmap(a: &mut [u8], _b: &mut [u8], n: i64, s: i64) -> i64 {
    for i in 0..n.max(0) {
        let o = (i * s) as usize;
        let v = f64::from_le_bytes(a[o..o + 8].try_into().unwrap()) * 2.0 + 1.0;
        a[o..o + 8].copy_from_slice(&v.to_le_bytes());
    }
    0
}

/// neon-farray widening dot through register-scaled f32 addresses:
/// `acc: f64 += (f64)*(a + i*s) * (f64)b[i]`, step 1, stored like `farray`.
fn build_es_farray(fb: &mut FunctionBuilder<'_>, cx: &Cx, s: ValueId, cont: BlockId) {
    let header = fb.create_block();
    let iv = fb.add_block_param(header, Ty::I64);
    let acc = fb.add_block_param(header, Ty::F64);
    let done = fb.create_block();
    let out = fb.add_block_param(done, Ty::F64);
    let zero = fb.iconst(Ty::I64, 0);
    let seed = fb.fconst(Ty::F64, 0.0);
    let nonempty = fb.icmp(ICmpOp::Slt, Ty::I64, zero, cx.n);
    fb.condbr(nonempty, header, vec![zero, seed], done, vec![seed]);
    fb.switch_to_block(header);
    let off = fb.mul(Ty::I64, iv, s);
    let base = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, cx.a);
    let addr = fb.add(Ty::I64, base, off);
    let pa = fb.cast(CastOp::IntToPtr, Ty::I64, Ty::Ptr, addr);
    let va = fb.load(Ty::F32, pa);
    let da = fb.cast(CastOp::FPExt, Ty::F32, Ty::F64, va);
    let pb = fb.gep(Ty::F32, cx.b, vec![iv]);
    let vb = fb.load(Ty::F32, pb);
    let db = fb.cast(CastOp::FPExt, Ty::F32, Ty::F64, vb);
    let t = fb.binop(BinOp::FMul, Ty::F64, da, db);
    let acc2 = fb.binop(BinOp::FAdd, Ty::F64, acc, t);
    let one = fb.iconst(Ty::I64, 1);
    let iv2 = fb.add(Ty::I64, iv, one);
    let finished = fb.icmp(ICmpOp::Sge, Ty::I64, iv2, cx.n);
    fb.condbr(finished, done, vec![acc2], header, vec![iv2, acc2]);
    fb.switch_to_block(done);
    let slot = fb.iconst(Ty::I64, i128::from(FARRAY_OUT));
    let p = fb.gep(Ty::F64, cx.b, vec![slot]);
    fb.store(Ty::F64, p, out);
    let r = fb.iconst(Ty::I64, 0);
    fb.br(cont, vec![r]);
}
fn model_es_farray(a: &mut [u8], b: &mut [u8], n: i64, s: i64) -> i64 {
    let mut acc = 0.0f64;
    for i in 0..n.max(0) {
        let va = f32::from_bits(rd_i32_at(a, i * s) as u32);
        acc += f64::from(va) * f64::from(rd_f32(b, i));
    }
    wr_f64(b, FARRAY_OUT, acc);
    0
}

const KERNELS: &[Kernel] = &[
    Kernel {
        name: "reduce_iv",
        ty: Ty::I32,
        unit: 1,
        build: build_reduce_iv,
        model: model_reduce_iv,
        prep: no_prep,
        pass: "neon-reduce",
        key: "neonreduce",
    },
    Kernel {
        name: "sum_mem",
        ty: Ty::I32,
        unit: 1,
        build: build_sum_mem,
        model: model_sum_mem,
        prep: no_prep,
        pass: "neon-array",
        key: "neon_array",
    },
    Kernel {
        name: "map_inplace",
        ty: Ty::I32,
        unit: 1,
        build: build_map_inplace,
        model: model_map_inplace,
        prep: no_prep,
        pass: "neon-map",
        key: "neon_map",
    },
    Kernel {
        name: "map_desc",
        ty: Ty::I32,
        unit: 1,
        build: build_map_desc,
        model: model_map_desc,
        prep: no_prep,
        pass: "neon-map",
        key: "neon_map",
    },
    Kernel {
        name: "max",
        ty: Ty::I32,
        unit: 1,
        build: build_max,
        model: model_max,
        prep: prep_max,
        pass: "neon-minmax",
        key: "neon_minmax",
    },
    Kernel {
        name: "predsum",
        ty: Ty::I32,
        unit: 1,
        build: build_predsum,
        model: model_predsum,
        prep: no_prep,
        pass: "neon-predsum",
        key: "neon_predsum",
    },
    Kernel {
        name: "find",
        ty: Ty::I32,
        unit: 1,
        build: build_find,
        model: model_find,
        prep: prep_find,
        pass: "neon-find",
        key: "neon_find",
    },
    Kernel {
        name: "fmap",
        ty: Ty::I32,
        unit: 1,
        build: build_fmap,
        model: model_fmap,
        prep: prep_f64_ramp,
        pass: "neon-fmap",
        key: "neon_fmap",
    },
    Kernel {
        name: "bytesum",
        ty: Ty::I64,
        unit: 1,
        build: build_bytesum,
        model: model_bytesum,
        prep: no_prep,
        pass: "neon-bytesum",
        key: "neon_bytesum",
    },
    Kernel {
        name: "fpred",
        ty: Ty::I64,
        unit: 1,
        build: build_fpred,
        model: model_fpred,
        prep: no_prep,
        pass: "neon-fpred",
        key: "neonfpred",
    },
    Kernel {
        name: "farray",
        ty: Ty::I64,
        unit: 1,
        build: build_farray,
        model: model_farray,
        prep: prep_farray,
        pass: "neon-farray",
        key: "neonfarray",
    },
    Kernel {
        name: "closed_form",
        ty: Ty::I64,
        unit: 1,
        build: build_closed_form,
        model: model_closed_form,
        prep: no_prep,
        pass: "closed-form-reduction",
        key: "closed_form_reduction",
    },
    Kernel {
        name: "iota_array",
        ty: Ty::I32,
        unit: 1,
        build: build_iota_array,
        model: model_iota_array,
        prep: no_prep,
        pass: "neon-array",
        key: "neon_array",
    },
    Kernel {
        name: "fmap_off",
        ty: Ty::I32,
        unit: 0,
        build: build_fmap_off,
        model: model_fmap_off,
        prep: prep_f64_noise,
        pass: "neon-fmap",
        key: "neon_fmap",
    },
    Kernel {
        name: "es_map",
        ty: Ty::I64,
        unit: 4,
        build: build_es_map,
        model: model_es_map,
        prep: no_prep,
        pass: "neon-map",
        key: "neon_map",
    },
    Kernel {
        name: "es_sum",
        ty: Ty::I64,
        unit: 4,
        build: build_es_sum,
        model: model_es_sum,
        prep: no_prep,
        pass: "neon-array",
        key: "neon_array",
    },
    Kernel {
        name: "es_max",
        ty: Ty::I64,
        unit: 4,
        build: build_es_max,
        model: model_es_max,
        prep: prep_max,
        pass: "neon-minmax",
        key: "neon_minmax",
    },
    Kernel {
        name: "iota_max",
        ty: Ty::I32,
        unit: 1,
        build: build_iota_max,
        model: model_iota_max,
        prep: prep_small_i32,
        pass: "neon-minmax",
        key: "neon_minmax",
    },
    Kernel {
        name: "es_predsum",
        ty: Ty::I64,
        unit: 4,
        build: build_es_predsum,
        model: model_es_predsum,
        prep: no_prep,
        pass: "neon-predsum",
        key: "neon_predsum",
    },
    Kernel {
        name: "es_find",
        ty: Ty::I64,
        unit: 4,
        build: build_es_find,
        model: model_es_find,
        prep: prep_es_find,
        pass: "neon-find",
        key: "neon_find",
    },
    Kernel {
        name: "es_fmap",
        ty: Ty::I64,
        unit: 8,
        build: build_es_fmap,
        model: model_es_fmap,
        prep: prep_f64_ramp,
        pass: "neon-fmap",
        key: "neon_fmap",
    },
    Kernel {
        name: "es_farray",
        ty: Ty::I64,
        unit: 4,
        build: build_es_farray,
        model: model_es_farray,
        prep: prep_farray,
        pass: "neon-farray",
        key: "neonfarray",
    },
];

fn as_bytes_mut(v: &mut [u64]) -> &mut [u8] {
    // SAFETY: u64 storage reinterpreted as its bytes; lifetime tied to `v`.
    unsafe { std::slice::from_raw_parts_mut(v.as_mut_ptr().cast::<u8>(), v.len() * 8) }
}

/// Deterministic buffer contents: random words, then the kernel's `prep`.
fn fill(kernel: &Kernel) -> (Vec<u64>, Vec<u64>) {
    let mut x = 0x0F1E_2D3C_4B5A_6978_u64;
    let mut next = || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    let mut a: Vec<u64> = (0..CAP).map(|_| next()).collect();
    let mut b: Vec<u64> = (0..CAP).map(|_| next()).collect();
    (kernel.prep)(as_bytes_mut(&mut a), as_bytes_mut(&mut b));
    (a, b)
}

fn kernel(name: &str) -> &'static Kernel {
    KERNELS.iter().find(|k| k.name == name).expect("kernel")
}

/// Every `n` and `sel` at O2 and O3 for one kernel and source. Returns the
/// mismatches against the model as text.
fn probe(kernel: &Kernel, src: Src) -> Vec<String> {
    let fname = format!("lw_{}_{:?}", kernel.name, src).to_lowercase();
    let module = build_module(&fname, kernel, src);
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
                failures.push(format!("{fname} {opt_level:?}: compile refused: {error}"));
                continue;
            }
        };
        // SAFETY: the entry's trust-ir signature is (ptr, ptr, i64, i64) ->
        // i64, both buffers hold CAP 8-byte words (every access the model
        // performs is in bounds), and `result` outlives every call.
        let entry = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut u8, *mut u8, i64, i64) -> i64>(&fname)
        }
        .expect("entry symbol");
        for n in [40i64, 67] {
            for sel in sels(src, kernel.unit) {
                let (mut ga, mut gb) = fill(kernel);
                let (mut wa, mut wb) = (ga.clone(), gb.clone());
                let want = run_model(
                    kernel,
                    src,
                    sel,
                    as_bytes_mut(&mut wa),
                    as_bytes_mut(&mut wb),
                    n,
                );
                let got = entry.as_ref()(ga.as_mut_ptr().cast(), gb.as_mut_ptr().cast(), n, sel);
                if got != want || ga != wa || gb != wb {
                    let first_a = (0..CAP).find(|&k| ga[k] != wa[k]);
                    let first_b = (0..CAP).find(|&k| gb[k] != wb[k]);
                    failures.push(format!(
                        "{fname} {opt_level:?} n={n} sel={sel} s={:?}: got {got:#x}, \
                         expected {want:#x}; first differing word of a {first_a:?}, of b {first_b:?}",
                        steps(src, sel, kernel.unit)
                    ));
                }
            }
        }
    }
    failures
}

/// Probes `name` under every source and reports each source's mismatches.
fn check(name: &str) {
    let kernel = kernel(name);
    let mut failures = Vec::new();
    for src in ALL_SRCS {
        failures.extend(probe(kernel, src));
    }
    assert!(
        failures.is_empty(),
        "{} ({}; TRUST_CG_DISABLE_PASSES={}):\n{}",
        kernel.name,
        kernel.pass,
        kernel.key,
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// One test per recognizer site. Each probes Search, Diamond, Carried and Unit.
// ---------------------------------------------------------------------------

/// neon_reduce `is_increment_by_one`: `acc += i * 3` stepping by `s`.
#[test]
fn neon_reduce_step_is_not_unit_for_a_multi_def_register() {
    check("reduce_iv");
}

/// neon_array `is_increment_by_one` (the `const_value` disjunct of
/// `step_is_one`): `acc += a[i]` stepping by `s`.
#[test]
fn neon_array_step_is_not_unit_for_a_multi_def_register() {
    check("sum_mem");
}

/// neon_map `is_increment_by_one`: in-place `a[i] += 7` stepping by `s`.
#[test]
fn neon_map_step_is_not_unit_for_a_multi_def_register() {
    check("map_inplace");
}

/// neon_map `is_decrement_by_one` (`SubRR`): descending `a[i] += 7`.
#[test]
fn neon_map_descending_step_is_not_unit_for_a_multi_def_register() {
    check("map_desc");
}

/// neon_minmax `is_increment_by_one`: `m = max(m, a[i])` stepping by `s`.
#[test]
fn neon_minmax_step_is_not_unit_for_a_multi_def_register() {
    check("max");
}

/// neon_predsum `is_increment_by_one`: a clamped sum stepping by `s`.
#[test]
fn neon_predsum_step_is_not_unit_for_a_multi_def_register() {
    check("predsum");
}

/// neon_find `is_increment_by_one`: an early-exit search stepping by `s`.
#[test]
fn neon_find_step_is_not_unit_for_a_multi_def_register() {
    check("find");
}

/// neon_fmap `is_increment_by_one`: in-place f64 map stepping by `s`.
#[test]
fn neon_fmap_step_is_not_unit_for_a_multi_def_register() {
    check("fmap");
}

/// neon_bytesum latch step (pass-local `const_value`): byte sum stepping by
/// `s` over the bounds-checked chain.
#[test]
fn neon_bytesum_step_is_not_unit_for_a_multi_def_register() {
    check("bytesum");
}

/// neon_fpred `is_increment_by_one`: `acc += (double)i * 0.5` stepping by
/// `s`.
#[test]
fn neon_fpred_step_is_not_unit_for_a_multi_def_register() {
    check("fpred");
}

/// neon_farray `is_increment_by_one`: widening f32 dot stepping by `s`.
#[test]
fn neon_farray_step_is_not_unit_for_a_multi_def_register() {
    check("farray");
}

/// reduction_split `increment_step` (via `resolve_const`), reached through
/// closed-form-reduction: `acc += i * 5 + 3` stepping by `s`.
#[test]
fn closed_form_reduction_step_is_not_unit_for_a_multi_def_register() {
    check("closed_form");
}

/// neon_array `shift_of_iv`: `acc += (i + s) ^ a[i]`.
#[test]
fn neon_array_iota_shift_is_not_one_for_a_multi_def_register() {
    check("iota_array");
}

/// neon_minmax `shift_of_iv`: `m = max(m, (i + s) ^ a[i])`.
#[test]
fn neon_minmax_iota_shift_is_not_one_for_a_multi_def_register() {
    check("iota_max");
}

/// neon_fmap `resolve_stream` offset `K`: in-place `a[i] = a[i + s] * 2 + 1`.
#[test]
fn neon_fmap_stream_offset_is_not_zero_for_a_multi_def_register() {
    check("fmap_off");
}

/// neon_map `resolve_ai_base` `es_ok`: in place through `a + i * s`.
#[test]
fn neon_map_element_scale_is_not_four_for_a_multi_def_register() {
    check("es_map");
}

/// neon_array `load_base` `es_ok`: `acc += *(a + i * s)`.
#[test]
fn neon_array_element_scale_is_not_four_for_a_multi_def_register() {
    check("es_sum");
}

/// neon_minmax `load_base` `es_ok`: `m = max(m, *(a + i * s))`.
#[test]
fn neon_minmax_element_scale_is_not_four_for_a_multi_def_register() {
    check("es_max");
}

/// neon_predsum `load_base` `es_ok`: clamped sum through `a + i * s`.
#[test]
fn neon_predsum_element_scale_is_not_four_for_a_multi_def_register() {
    check("es_predsum");
}

/// neon_find `load_base` `es_ok`: search through `a + i * s`.
#[test]
fn neon_find_element_scale_is_not_four_for_a_multi_def_register() {
    check("es_find");
}

/// neon_fmap `resolve_stream` `es_ok`: in-place f64 map through `a + i * s`.
#[test]
fn neon_fmap_element_scale_is_not_eight_for_a_multi_def_register() {
    check("es_fmap");
}

/// neon_farray `strided_load_base` `es_ok`: widening dot through `a + i * s`.
#[test]
fn neon_farray_element_scale_is_not_four_for_a_multi_def_register() {
    check("es_farray");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
