// trust-cg-codegen - vectorizer constant leaves read from a register with several constant definitions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Constant leaves (broadcast terms, compare operands, select arms, addends,
//! closed-form operands) read from a register written with different
//! constants on different paths.
//!
//! The invariant these rows pin: a register written with different constants
//! on different paths is not one constant. Machine IR is not SSA, and
//! `effects::build_reaching_def_map` keeps one definition per vreg id, the
//! layout-last one; a resolver that reads it without checking how many
//! definitions the register has takes that definition's constant on every
//! path. `mach_util::const_value` and `mach_util::copied_const` (which
//! `neon_array` and `neon_iota_fill` now call in place of their pass-local
//! copies) give a register a constant only when EVERY definition of it
//! writes that constant, and
//! `reduction_split::resolve_const` requires every definition to write the
//! same constant, so the multi-def rows below are refused rather than read as
//! their layout-last value.
//!
//! The register here is the stop value `k` of a small early-exit search
//!
//! ```text
//! j = j0; loop { j += step; if j == limit || j == sel { break } }   // k = j
//! ```
//!
//! O2/O3 fully unroll the search and rewrite `j` into one `Movz k, #c` per
//! exit edge, so `k` has one constant definition per path and the layout-last
//! one is `Movz k, #limit`. A loop after the search then uses `k` as a
//! loop-invariant term operand. Each test JIT-runs such a loop at O2 and O3
//! for every `sel` (every exit edge plus two values that never match) and
//! compares with a plain Rust model of the same program.
//!
//! The loops are written in the layouts the passes recognize after
//! `loop-latch-layout` (see [`Layout`]). Every test first checks a control:
//! the same kernel and layout with a single-definition `k` must be rewritten
//! by the pass under test (`PreparationMetrics::optimization_pass_changes`),
//! so a test cannot pass because the loop left the pass's domain.
//!
//! Only full unrolling writes `Movz` straight into the multi-definition
//! register. A phi of two constants (a diamond) and a constant carried round
//! an outer loop both lower to one `MovR` copy per incoming edge, which these
//! resolvers do not read as constants, so they are not used here.
//!
//! Each test's doc names what a resolver that reads the layout-last
//! definition does with its kernel: the misreading the row pins against. The
//! cases are bounded executions on the host, not a proof of any pass.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, BlockId, CastOp, ICmpOp, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

#[path = "common/native_host.rs"]
mod native_host;

/// Elements processed by every kernel loop.
const N: u64 = 100;

const LEVELS: [OptLevel; 2] = [OptLevel::O2, OptLevel::O3];

/// Where the kernel's loop-invariant operand `k` comes from.
#[derive(Clone, Copy, Debug)]
enum KSource {
    /// A compile-time constant (single definition).
    Const(u64),
    /// The run-time `sel` argument truncated to `k`'s type (single definition,
    /// not a constant).
    Runtime,
    /// The stop value of `j = j0; loop { j += step; if j == limit || j == sel
    /// { break } }`. Fully unrolled, `k` has one `Movz` per exit edge and the
    /// layout-last one is `Movz k, #limit`.
    Search { j0: u64, step: u64, limit: u64 },
}

/// `k` in `1..=8`; layout-last definition `Movz k, #8`.
const UP_TO_8: KSource = KSource::Search {
    j0: 0,
    step: 1,
    limit: 8,
};
/// `k` in `8..=0`; layout-last definition `Movz k, #0`.
const DOWN_TO_0: KSource = KSource::Search {
    j0: 9,
    step: u64::MAX,
    limit: 0,
};
/// `k` in `8..=1`; layout-last definition `Movz k, #1`.
const DOWN_TO_1: KSource = KSource::Search {
    j0: 9,
    step: u64::MAX,
    limit: 1,
};

impl KSource {
    /// The value of `k` for argument `sel`.
    fn k(self, sel: u64) -> u64 {
        match self {
            KSource::Const(k) => k,
            KSource::Runtime => sel,
            KSource::Search { j0, step, limit } => {
                let mut j = j0;
                loop {
                    j = j.wrapping_add(step);
                    if j == limit || j == sel {
                        break j;
                    }
                }
            }
        }
    }

    /// The `sel` arguments to run: every exit edge of a search plus two values
    /// that never match it.
    fn sels(self) -> Vec<u64> {
        match self {
            KSource::Const(_) => vec![0, 1],
            KSource::Runtime => vec![3, 5],
            KSource::Search { j0, step, limit } => {
                let mut sels = vec![0x7FFF, 0xFFFF_FFFF];
                let mut j = j0;
                loop {
                    j = j.wrapping_add(step);
                    sels.push(j);
                    if j == limit {
                        break sels;
                    }
                }
            }
        }
    }
}

/// How the kernel loop is laid out. `loop-latch-layout` (which runs before
/// the NEON passes) rotates a test-first two-block loop whose exit follows
/// its latch, and each pass recognizes particular layouts, so a kernel is
/// written in the layout its pass accepts.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Layout {
    /// `if i < N { body } else { exit }`, constant `N`.
    Natural,
    /// `if i >= N { exit } else { body }`, constant `N`.
    ExitFirst,
    /// `if i < n { body } else { exit }` with the run-time `n` argument
    /// (always `N`).
    RuntimeBound,
    /// [`Layout::Natural`], plus a preheader edge straight to the exit taken
    /// when the run-time `z` argument is non-zero (never, here).
    SharedExit,
}

/// The loop that consumes `k`.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Kernel {
    /// `p[i] = p[i] OP k` over `i32`, signed `i32` induction.
    Map32(BinOp),
    /// `p[i] = p[i] OP k` over `i64`, signed `i64` induction.
    Map64(BinOp),
    /// `p[i] = p[i] OP k` over `i32`, unsigned `u64` induction.
    Map32U(BinOp),
    /// `acc: i32 += i OP k`.
    ReduceIv(BinOp),
    /// `acc: i32 += (i * k) ^ i` (an unfused `i * k`).
    ReduceIvMulXor,
    /// `acc: i32 += a[i] OP k`.
    ArraySum(BinOp),
    /// `acc: i32 ^= a[i] OP k`.
    XorRed(BinOp),
    /// `acc: i32 = smax(acc, a[i] OP k)`.
    MaxRed(BinOp),
    /// `acc += a[i] > k ? a[i] : 0`.
    PredThreshold,
    /// `acc += a[i] > z ? k : 0` (`z` the run-time zero).
    PredArm,
    /// `acc += a[i] > z ? a[i] : k`.
    PredElse,
    /// `acc += a[i] < k ? k - a[i] : a[i]`.
    PredAbs,
    /// `while i <u N { if a[i] > k { acc += a[i] } }`, a branch diamond.
    ChainPred,
    /// `p[i] = trunc32(i) + k`, unsigned `u64` induction.
    Iota,
    /// `acc: u64 += i * k` (a fused `Madd` reduction).
    ClosedFormMul,
    /// `acc: u64 += (i + k) * i`.
    ClosedFormAddMul,
    /// `acc: u64 += i * k + i` (a `Madd` term feeding an add reduction).
    ClosedFormMaddTerm,
}

impl Kernel {
    fn kty(self) -> Ty {
        match self {
            Kernel::Map64(_) => Ty::I64,
            Kernel::ClosedFormMul | Kernel::ClosedFormAddMul | Kernel::ClosedFormMaddTerm => {
                Ty::U64
            }
            _ => Ty::I32,
        }
    }

    fn elem_bytes(self) -> usize {
        match self {
            Kernel::Map64(_) => 8,
            _ => 4,
        }
    }
}

fn wrap(op: BinOp, a: u64, b: u64, bits: u32) -> u64 {
    let mask = if bits == 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    };
    let r = match op {
        BinOp::Add => a.wrapping_add(b),
        BinOp::Sub => a.wrapping_sub(b),
        BinOp::Mul => a.wrapping_mul(b),
        BinOp::Xor => a ^ b,
        BinOp::And => a & b,
        BinOp::Or => a | b,
        other => panic!("unsupported op {other:?}"),
    };
    r & mask
}

fn s32(x: u64) -> i32 {
    x as u32 as i32
}

/// Loop shape shared by every kernel.
struct LoopCtx {
    layout: Layout,
    n_rt: ValueId,
    z: ValueId,
}

impl LoopCtx {
    fn bound(&self, fb: &mut FunctionBuilder<'_>, ty: Ty) -> ValueId {
        if self.layout == Layout::RuntimeBound {
            // The runtime bound arrives as `u64`; an `i64` loop test reads it
            // as `i64` (trust-ir refuses an `icmp` whose operands are not of
            // its type, `OperandTypeMismatch`, at every ingestion entry since
            // WS7.3): the same register, reinterpreted.
            match ty {
                Ty::U64 => self.n_rt,
                Ty::I64 => fb.cast(CastOp::Bitcast, Ty::U64, Ty::I64, self.n_rt),
                other => fb.trunc(Ty::U64, other, self.n_rt),
            }
        } else {
            fb.iconst(ty, i128::from(N))
        }
    }

    /// Branch from the current block into the loop `header`.
    fn enter(
        &self,
        fb: &mut FunctionBuilder<'_>,
        header: BlockId,
        hargs: Vec<ValueId>,
        exit: BlockId,
        eargs: Vec<ValueId>,
    ) {
        if self.layout == Layout::SharedExit {
            let zero = fb.iconst(Ty::U64, 0);
            let skip = fb.icmp(ICmpOp::Ne, Ty::U64, self.z, zero);
            fb.condbr(skip, exit, eargs, header, hargs);
        } else {
            fb.br(header, hargs);
        }
    }

    /// The header test: `i CC n` continues into `body`, otherwise `exit`.
    #[allow(clippy::too_many_arguments)]
    fn test(
        &self,
        fb: &mut FunctionBuilder<'_>,
        cc: ICmpOp,
        ty: Ty,
        i: ValueId,
        n: ValueId,
        body: BlockId,
        exit: BlockId,
        eargs: Vec<ValueId>,
    ) {
        if self.layout == Layout::ExitFirst {
            let inv = match cc {
                ICmpOp::Slt => ICmpOp::Sge,
                ICmpOp::Ult => ICmpOp::Uge,
                other => panic!("unsupported loop test {other:?}"),
            };
            let stop = fb.icmp(inv, ty, i, n);
            fb.condbr(stop, exit, eargs, body, vec![]);
        } else {
            let go = fb.icmp(cc, ty, i, n);
            fb.condbr(go, body, vec![], exit, eargs);
        }
    }
}

/// Emit `kernel` from the current block; the builder ends in the kernel's
/// exit block and the returned value is its `u64` result.
fn emit_kernel(
    fb: &mut FunctionBuilder<'_>,
    cx: &LoopCtx,
    kernel: Kernel,
    p: ValueId,
    k: ValueId,
) -> ValueId {
    match kernel {
        Kernel::Map32(op) | Kernel::Map64(op) | Kernel::Map32U(op) => {
            let (ity, ety, cc) = match kernel {
                Kernel::Map64(_) => (Ty::I64, Ty::I64, ICmpOp::Slt),
                Kernel::Map32U(_) => (Ty::U64, Ty::I32, ICmpOp::Ult),
                _ => (Ty::I32, Ty::I32, ICmpOp::Slt),
            };
            let header = fb.create_block();
            let i = fb.add_block_param(header, ity.clone());
            let body = fb.create_block();
            let exit = fb.create_block();
            let i0 = fb.iconst(ity.clone(), 0);
            cx.enter(fb, header, vec![i0], exit, vec![]);
            fb.switch_to_block(header);
            let n = cx.bound(fb, ity.clone());
            cx.test(fb, cc, ity.clone(), i, n, body, exit, vec![]);
            fb.switch_to_block(body);
            let idx = if ity == Ty::I32 {
                fb.sext(Ty::I32, Ty::I64, i)
            } else {
                i
            };
            let a = fb.gep(ety.clone(), p, vec![idx]);
            let v = fb.load(ety.clone(), a);
            let r = fb.binop(op, ety.clone(), v, k);
            fb.store(ety, a, r);
            let one = fb.iconst(ity.clone(), 1);
            let i1 = fb.binop(BinOp::Add, ity, i, one);
            fb.br(header, vec![i1]);
            fb.switch_to_block(exit);
            fb.iconst(Ty::U64, 0)
        }
        Kernel::Iota => {
            let header = fb.create_block();
            let i = fb.add_block_param(header, Ty::U64);
            let body = fb.create_block();
            let exit = fb.create_block();
            let i0 = fb.iconst(Ty::U64, 0);
            cx.enter(fb, header, vec![i0], exit, vec![]);
            fb.switch_to_block(header);
            let n = cx.bound(fb, Ty::U64);
            cx.test(fb, ICmpOp::Ult, Ty::U64, i, n, body, exit, vec![]);
            fb.switch_to_block(body);
            let t = fb.trunc(Ty::U64, Ty::I32, i);
            let r = fb.binop(BinOp::Add, Ty::I32, t, k);
            let a = fb.gep(Ty::I32, p, vec![i]);
            fb.store(Ty::I32, a, r);
            let one = fb.iconst(Ty::U64, 1);
            let i1 = fb.binop(BinOp::Add, Ty::U64, i, one);
            fb.br(header, vec![i1]);
            fb.switch_to_block(exit);
            fb.iconst(Ty::U64, 0)
        }
        Kernel::ChainPred => {
            let header = fb.create_block();
            let i = fb.add_block_param(header, Ty::U64);
            let s = fb.add_block_param(header, Ty::I32);
            let body = fb.create_block();
            let then_b = fb.create_block();
            let join = fb.create_block();
            let s2 = fb.add_block_param(join, Ty::I32);
            let exit = fb.create_block();
            let r = fb.add_block_param(exit, Ty::I32);
            let i0 = fb.iconst(Ty::U64, 0);
            let a0 = fb.iconst(Ty::I32, 0);
            cx.enter(fb, header, vec![i0, a0], exit, vec![a0]);
            fb.switch_to_block(header);
            let n = cx.bound(fb, Ty::U64);
            cx.test(fb, ICmpOp::Ult, Ty::U64, i, n, body, exit, vec![s]);
            fb.switch_to_block(body);
            let a = fb.gep(Ty::I32, p, vec![i]);
            let v = fb.load(Ty::I32, a);
            let c = fb.icmp(ICmpOp::Sgt, Ty::I32, v, k);
            fb.condbr(c, then_b, vec![], join, vec![s]);
            fb.switch_to_block(then_b);
            let s1 = fb.binop(BinOp::Add, Ty::I32, s, v);
            fb.br(join, vec![s1]);
            fb.switch_to_block(join);
            let one = fb.iconst(Ty::U64, 1);
            let i1 = fb.binop(BinOp::Add, Ty::U64, i, one);
            fb.br(header, vec![i1, s2]);
            fb.switch_to_block(exit);
            fb.zext(Ty::I32, Ty::U64, r)
        }
        Kernel::ClosedFormMul | Kernel::ClosedFormAddMul | Kernel::ClosedFormMaddTerm => {
            let header = fb.create_block();
            let i = fb.add_block_param(header, Ty::U64);
            let acc = fb.add_block_param(header, Ty::U64);
            let body = fb.create_block();
            let exit = fb.create_block();
            let r = fb.add_block_param(exit, Ty::U64);
            let i0 = fb.iconst(Ty::U64, 0);
            let a0 = fb.iconst(Ty::U64, 0);
            cx.enter(fb, header, vec![i0, a0], exit, vec![a0]);
            fb.switch_to_block(header);
            let n = cx.bound(fb, Ty::U64);
            cx.test(fb, ICmpOp::Ult, Ty::U64, i, n, body, exit, vec![acc]);
            fb.switch_to_block(body);
            let t = match kernel {
                Kernel::ClosedFormAddMul => {
                    let s = fb.binop(BinOp::Add, Ty::U64, i, k);
                    fb.binop(BinOp::Mul, Ty::U64, s, i)
                }
                Kernel::ClosedFormMaddTerm => {
                    let m = fb.binop(BinOp::Mul, Ty::U64, i, k);
                    fb.binop(BinOp::Add, Ty::U64, m, i)
                }
                _ => fb.binop(BinOp::Mul, Ty::U64, i, k),
            };
            let acc1 = fb.binop(BinOp::Add, Ty::U64, acc, t);
            let one = fb.iconst(Ty::U64, 1);
            let i1 = fb.binop(BinOp::Add, Ty::U64, i, one);
            fb.br(header, vec![i1, acc1]);
            fb.switch_to_block(exit);
            r
        }
        _ => emit_i32_reduction(fb, cx, kernel, p, k),
    }
}

/// The `i32` reductions over a signed `i32` induction.
fn emit_i32_reduction(
    fb: &mut FunctionBuilder<'_>,
    cx: &LoopCtx,
    kernel: Kernel,
    p: ValueId,
    k: ValueId,
) -> ValueId {
    let z32 = fb.trunc(Ty::U64, Ty::I32, cx.z);
    let header = fb.create_block();
    let i = fb.add_block_param(header, Ty::I32);
    let acc = fb.add_block_param(header, Ty::I32);
    let body = fb.create_block();
    let exit = fb.create_block();
    let r = fb.add_block_param(exit, Ty::I32);
    let i0 = fb.iconst(Ty::I32, 0);
    let seed = if matches!(kernel, Kernel::MaxRed(_)) {
        i128::from(i32::MIN)
    } else {
        0
    };
    let a0 = fb.iconst(Ty::I32, seed);
    cx.enter(fb, header, vec![i0, a0], exit, vec![a0]);
    fb.switch_to_block(header);
    let n = cx.bound(fb, Ty::I32);
    cx.test(fb, ICmpOp::Slt, Ty::I32, i, n, body, exit, vec![acc]);
    fb.switch_to_block(body);
    let load = |fb: &mut FunctionBuilder<'_>| {
        let idx = fb.sext(Ty::I32, Ty::I64, i);
        let a = fb.gep(Ty::I32, p, vec![idx]);
        fb.load(Ty::I32, a)
    };
    let acc1 = match kernel {
        Kernel::ReduceIv(op) => {
            let t = fb.binop(op, Ty::I32, i, k);
            fb.binop(BinOp::Add, Ty::I32, acc, t)
        }
        Kernel::ReduceIvMulXor => {
            let m = fb.binop(BinOp::Mul, Ty::I32, i, k);
            let t = fb.binop(BinOp::Xor, Ty::I32, m, i);
            fb.binop(BinOp::Add, Ty::I32, acc, t)
        }
        Kernel::ArraySum(op) => {
            let v = load(fb);
            let t = fb.binop(op, Ty::I32, v, k);
            fb.binop(BinOp::Add, Ty::I32, acc, t)
        }
        Kernel::XorRed(op) => {
            let v = load(fb);
            let t = fb.binop(op, Ty::I32, v, k);
            fb.binop(BinOp::Xor, Ty::I32, acc, t)
        }
        Kernel::MaxRed(op) => {
            let v = load(fb);
            let t = fb.binop(op, Ty::I32, v, k);
            let c = fb.icmp(ICmpOp::Sgt, Ty::I32, t, acc);
            fb.select(Ty::I32, c, t, acc)
        }
        Kernel::PredThreshold => {
            let v = load(fb);
            let zero = fb.iconst(Ty::I32, 0);
            let c = fb.icmp(ICmpOp::Sgt, Ty::I32, v, k);
            let t = fb.select(Ty::I32, c, v, zero);
            fb.binop(BinOp::Add, Ty::I32, acc, t)
        }
        Kernel::PredArm => {
            let v = load(fb);
            let zero = fb.iconst(Ty::I32, 0);
            let c = fb.icmp(ICmpOp::Sgt, Ty::I32, v, z32);
            let t = fb.select(Ty::I32, c, k, zero);
            fb.binop(BinOp::Add, Ty::I32, acc, t)
        }
        Kernel::PredElse => {
            let v = load(fb);
            let c = fb.icmp(ICmpOp::Sgt, Ty::I32, v, z32);
            let t = fb.select(Ty::I32, c, v, k);
            fb.binop(BinOp::Add, Ty::I32, acc, t)
        }
        Kernel::PredAbs => {
            let v = load(fb);
            let c = fb.icmp(ICmpOp::Slt, Ty::I32, v, k);
            let neg = fb.binop(BinOp::Sub, Ty::I32, k, v);
            let t = fb.select(Ty::I32, c, neg, v);
            fb.binop(BinOp::Add, Ty::I32, acc, t)
        }
        other => panic!("not an i32 reduction: {other:?}"),
    };
    let one = fb.iconst(Ty::I32, 1);
    let i1 = fb.binop(BinOp::Add, Ty::I32, i, one);
    fb.br(header, vec![i1, acc1]);
    fb.switch_to_block(exit);
    fb.zext(Ty::I32, Ty::U64, r)
}

/// `fn(p: *mut T, sel: u64, n: u64, z: u64) -> u64`: compute `k` from `src`,
/// then run `kernel`.
fn build_module(name: &str, kernel: Kernel, src: KSource, layout: Layout) -> trust_ir::Module {
    let kty = kernel.kty();
    let mut mb = ModuleBuilder::new(name);
    let fty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(name, fty);
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, Ty::Ptr);
    let sel = fb.add_block_param(entry, Ty::U64);
    let n_rt = fb.add_block_param(entry, Ty::U64);
    let z = fb.add_block_param(entry, Ty::U64);
    let cx = LoopCtx { layout, n_rt, z };
    let wide = matches!(kty, Ty::U64 | Ty::I64);
    fb.switch_to_block(entry);
    let sel_k = if wide {
        sel
    } else {
        fb.trunc(Ty::U64, kty.clone(), sel)
    };
    let kconst = |fb: &mut FunctionBuilder<'_>, v: u64| {
        if kty == Ty::U64 {
            fb.iconst(kty.clone(), i128::from(v))
        } else {
            fb.iconst(kty.clone(), i128::from(v as i64))
        }
    };
    let pre = fb.create_block();
    match src {
        KSource::Const(v) => {
            let k = kconst(&mut fb, v);
            fb.br(pre, vec![]);
            fb.switch_to_block(pre);
            let r = emit_kernel(&mut fb, &cx, kernel, p, k);
            fb.ret(vec![r]);
        }
        KSource::Runtime => {
            fb.br(pre, vec![]);
            fb.switch_to_block(pre);
            let r = emit_kernel(&mut fb, &cx, kernel, p, sel_k);
            fb.ret(vec![r]);
        }
        KSource::Search { j0, step, limit } => {
            let k = fb.add_block_param(pre, kty.clone());
            let search = fb.create_block();
            let j = fb.add_block_param(search, kty.clone());
            let test = fb.create_block();
            let start = kconst(&mut fb, j0);
            fb.br(search, vec![start]);
            fb.switch_to_block(search);
            let st = kconst(&mut fb, step);
            let next = fb.binop(BinOp::Add, kty.clone(), j, st);
            fb.br(test, vec![]);
            fb.switch_to_block(test);
            let lim = kconst(&mut fb, limit);
            let trip = fb.icmp(ICmpOp::Ne, kty.clone(), next, lim);
            let miss = fb.icmp(ICmpOp::Ne, kty.clone(), next, sel_k);
            let more = fb.binop(BinOp::And, Ty::Bool, trip, miss);
            fb.condbr(more, search, vec![next], pre, vec![next]);
            fb.switch_to_block(pre);
            let r = emit_kernel(&mut fb, &cx, kernel, p, k);
            fb.ret(vec![r]);
        }
    }
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// One kernel run with `k` over `mem` (elements as `u64`).
fn model_kernel(kernel: Kernel, mem: &mut [u64], k: u64) -> u64 {
    let n = N as usize;
    match kernel {
        Kernel::Map32(op) | Kernel::Map32U(op) => {
            for x in mem.iter_mut().take(n) {
                *x = wrap(op, *x, k, 32);
            }
            0
        }
        Kernel::Map64(op) => {
            for x in mem.iter_mut().take(n) {
                *x = wrap(op, *x, k, 64);
            }
            0
        }
        Kernel::Iota => {
            for (i, x) in mem.iter_mut().take(n).enumerate() {
                *x = wrap(BinOp::Add, i as u64, k, 32);
            }
            0
        }
        Kernel::ClosedFormMul | Kernel::ClosedFormAddMul | Kernel::ClosedFormMaddTerm => (0..N)
            .fold(0u64, |acc, i| {
                let t = match kernel {
                    Kernel::ClosedFormAddMul => i.wrapping_add(k).wrapping_mul(i),
                    Kernel::ClosedFormMaddTerm => i.wrapping_mul(k).wrapping_add(i),
                    _ => i.wrapping_mul(k),
                };
                acc.wrapping_add(t)
            }),
        _ => {
            let k32 = s32(k);
            let mut acc: i32 = if matches!(kernel, Kernel::MaxRed(_)) {
                i32::MIN
            } else {
                0
            };
            for (i, x) in mem.iter().take(n).enumerate() {
                let v = s32(*x);
                let vu = u64::from(v as u32);
                acc = match kernel {
                    Kernel::ReduceIv(op) => acc.wrapping_add(s32(wrap(op, i as u64, k, 32))),
                    Kernel::ReduceIvMulXor => {
                        let t = wrap(BinOp::Mul, i as u64, k, 32) ^ i as u64;
                        acc.wrapping_add(s32(t))
                    }
                    Kernel::ArraySum(op) => acc.wrapping_add(s32(wrap(op, vu, k, 32))),
                    Kernel::XorRed(op) => acc ^ s32(wrap(op, vu, k, 32)),
                    Kernel::MaxRed(op) => acc.max(s32(wrap(op, vu, k, 32))),
                    Kernel::PredThreshold | Kernel::ChainPred => {
                        acc.wrapping_add(if v > k32 { v } else { 0 })
                    }
                    Kernel::PredArm => acc.wrapping_add(if v > 0 { k32 } else { 0 }),
                    Kernel::PredElse => acc.wrapping_add(if v > 0 { v } else { k32 }),
                    Kernel::PredAbs => {
                        acc.wrapping_add(if v < k32 { k32.wrapping_sub(v) } else { v })
                    }
                    other => panic!("not an i32 reduction: {other:?}"),
                };
            }
            u64::from(acc as u32)
        }
    }
}

/// Deterministic elements: every third a full-width word, the rest small
/// signed values around the predicates' thresholds.
fn data() -> Vec<u64> {
    let mut x = 0x2545_F491_4F6C_DD1D_u64;
    (0..N as usize + 16)
        .map(|i| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            if i % 3 == 0 {
                x
            } else {
                ((x % 41) as i64 - 20) as u64
            }
        })
        .collect()
}

/// JIT-run `kernel` fed by `src` at O2 and O3 for every `sel` and compare the
/// return value and the array with [`model`]. Returns the mismatches.
fn mismatches(name: &str, kernel: Kernel, src: KSource, layout: Layout) -> Vec<String> {
    let module = build_module(name, kernel, src, layout);
    let mut failures = Vec::new();
    for opt_level in LEVELS {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = opt_level;
        let result = match Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &HashMap::new())
        {
            Ok(result) => result,
            Err(error) => {
                failures.push(format!("{name} {opt_level:?}: compile refused: {error}"));
                continue;
            }
        };
        // SAFETY: the entry's trust-ir signature is (ptr, u64, u64, u64) ->
        // u64, every access is below index N of a buffer of N + 16 elements,
        // and `result` outlives every call through `entry`.
        let entry = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut u8, u64, u64, u64) -> u64>(name)
        }
        .expect("entry symbol");
        for sel in src.sels() {
            let mut want_mem = data();
            let want = model_kernel(kernel, &mut want_mem, src.k(sel));
            let (got, got_mem): (u64, Vec<u64>) = if kernel.elem_bytes() == 8 {
                let mut mem = data();
                let r = entry.as_ref()(mem.as_mut_ptr().cast(), sel, N, 0);
                (r, mem)
            } else {
                let mut mem: Vec<u32> = data().iter().map(|x| *x as u32).collect();
                let r = entry.as_ref()(mem.as_mut_ptr().cast(), sel, N, 0);
                want_mem.iter_mut().for_each(|x| *x &= 0xFFFF_FFFF);
                (r, mem.iter().map(|x| u64::from(*x)).collect())
            };
            if got != want || got_mem != want_mem {
                let first = (0..got_mem.len()).find(|&i| got_mem[i] != want_mem[i]);
                failures.push(format!(
                    "{name} {opt_level:?} sel={sel:#x} k={}: returned {got:#x}, expected {want:#x}; \
                     first array difference (index, got, expected) {:?}",
                    src.k(sel),
                    first.map(|i| (i, got_mem[i], want_mem[i]))
                ));
            }
        }
    }
    failures
}

/// How many times `pass` rewrote the function at `opt_level`, from the opt
/// pipeline's own change counts.
fn pass_changes(module: &trust_ir::Module, opt_level: OptLevel, pass: &str) -> u32 {
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("lowering: {error}"));
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level,
        target_triple: native_host::TRIPLE.into(),
        disabled_passes_override: Some(String::new()),
        ..PipelineConfig::default()
    });
    let mut changes = 0;
    for (function, _) in &lowered {
        let (_, metrics) = pipeline
            .prepare_function_with_metrics(function, None)
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        changes += metrics
            .optimization_pass_changes
            .iter()
            .filter(|(name, _)| name == pass)
            .map(|(_, count)| count)
            .sum::<u32>();
    }
    changes
}

/// One kernel/layout pair, the single-definition source that puts it in the
/// pass's domain, and the multi-definition sources to run.
struct Case {
    name: &'static str,
    kernel: Kernel,
    layout: Layout,
    control: KSource,
    sources: &'static [(&'static str, KSource)],
}

/// Check every case's control (the pass rewrites it and its results are
/// right), then collect the mismatches of every multi-definition source.
fn run_cases(pass: &str, cases: &[Case]) -> Vec<String> {
    let mut failures = Vec::new();
    for case in cases {
        let control = format!("{}_control", case.name);
        let module = build_module(&control, case.kernel, case.control, case.layout);
        for opt_level in LEVELS {
            assert!(
                pass_changes(&module, opt_level, pass) > 0,
                "{control} {opt_level:?}: `{pass}` no longer rewrites the control loop, \
                 so this case no longer reaches the pass"
            );
        }
        let wrong = mismatches(&control, case.kernel, case.control, case.layout);
        assert!(wrong.is_empty(), "{}", wrong.join("\n"));
        for (tag, src) in case.sources {
            let name = format!("{}_{tag}", case.name);
            failures.extend(mismatches(&name, case.kernel, *src, case.layout));
        }
    }
    failures
}

const UP: &[(&str, KSource)] = &[("up_to_8", UP_TO_8)];
const UP_AND_DOWN: &[(&str, KSource)] = &[("up_to_8", UP_TO_8), ("down_to_0", DOWN_TO_0)];

/// `neon_map` `Recognized::node_ok` admits a multi-definition `k` as a
/// constant leaf and `lower` broadcasts its layout-last constant, so
/// `p[i] = p[i] OP k` stores `p[i] OP limit` on every early-exit path.
/// Kill switch: `TRUST_CG_DISABLE_PASSES=neon_map`.
#[test]
fn neon_map_broadcasts_a_multi_def_leaf_as_its_last_constant() {
    let failures = run_cases(
        "neon-map",
        &[
            Case {
                name: "lw_map32_add",
                kernel: Kernel::Map32(BinOp::Add),
                layout: Layout::ExitFirst,
                control: KSource::Const(5),
                sources: UP_AND_DOWN,
            },
            Case {
                name: "lw_map32_mul",
                kernel: Kernel::Map32(BinOp::Mul),
                layout: Layout::RuntimeBound,
                control: KSource::Const(5),
                sources: UP,
            },
            Case {
                name: "lw_map64_add",
                kernel: Kernel::Map64(BinOp::Add),
                layout: Layout::ExitFirst,
                control: KSource::Const(5),
                sources: UP,
            },
            Case {
                name: "lw_map32u_xor",
                kernel: Kernel::Map32U(BinOp::Xor),
                layout: Layout::SharedExit,
                control: KSource::Const(5),
                sources: UP,
            },
        ],
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `neon_reduce` `node_ok` / `lower` treat a multi-definition `k` in
/// `acc += i OP k` as its layout-last constant; for an unfused `i * k`
/// (`acc += (i * k) ^ i`) the cross-accumulator offsets of
/// `shared_iv_multiplier` use the same constant.
/// Kill switch: `TRUST_CG_DISABLE_PASSES=neonreduce`.
#[test]
fn neon_reduce_induction_term_uses_a_multi_def_leaf_as_its_last_constant() {
    let failures = run_cases(
        "neon-reduce",
        &[
            Case {
                name: "lw_rediv_mul",
                kernel: Kernel::ReduceIv(BinOp::Mul),
                layout: Layout::ExitFirst,
                control: KSource::Const(5),
                sources: UP_AND_DOWN,
            },
            Case {
                name: "lw_rediv_mulxor",
                kernel: Kernel::ReduceIvMulXor,
                layout: Layout::ExitFirst,
                control: KSource::Const(5),
                sources: UP,
            },
            Case {
                name: "lw_rediv_add",
                kernel: Kernel::ReduceIv(BinOp::Add),
                layout: Layout::ExitFirst,
                control: KSource::Const(5),
                sources: UP,
            },
        ],
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `neon_minmax` `node_ok` / `lower` treat a multi-definition `k` in
/// `m = max(m, a[i] + k)` / `m ^= a[i] + k` as its layout-last constant.
/// Kill switch: `TRUST_CG_DISABLE_PASSES=neon_minmax`.
#[test]
fn neon_minmax_reduces_with_a_multi_def_leaf_as_its_last_constant() {
    let failures = run_cases(
        "neon-minmax",
        &[
            Case {
                name: "lw_maxred_add",
                kernel: Kernel::MaxRed(BinOp::Add),
                layout: Layout::ExitFirst,
                control: KSource::Const(5),
                sources: UP_AND_DOWN,
            },
            Case {
                name: "lw_xorred_add",
                kernel: Kernel::XorRed(BinOp::Add),
                layout: Layout::ExitFirst,
                control: KSource::Const(5),
                sources: UP,
            },
        ],
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `neon_array` `node_ok` / `lower` treat a multi-definition `k` in
/// `acc += a[i] OP k` as its layout-last constant (its pass-local
/// `const_value` has no definition-count check).
/// Kill switch: `TRUST_CG_DISABLE_PASSES=neon_array`.
#[test]
fn neon_array_reduces_with_a_multi_def_leaf_as_its_last_constant() {
    let failures = run_cases(
        "neon-array",
        &[
            Case {
                name: "lw_arrsum_mul",
                kernel: Kernel::ArraySum(BinOp::Mul),
                layout: Layout::RuntimeBound,
                control: KSource::Const(5),
                sources: UP_AND_DOWN,
            },
            Case {
                name: "lw_arrsum_xor",
                kernel: Kernel::ArraySum(BinOp::Xor),
                layout: Layout::RuntimeBound,
                control: KSource::Const(5),
                sources: UP,
            },
        ],
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `neon_predsum` strict path: `Recognized::node_ok` / `lower` broadcast the
/// layout-last constant of a multi-definition compare operand (`a[i] > k`).
/// Kill switch: `TRUST_CG_DISABLE_PASSES=neon_predsum`.
#[test]
fn neon_predsum_compares_against_a_multi_def_leaf_as_its_last_constant() {
    let failures = run_cases(
        "neon-predsum",
        &[Case {
            name: "lw_pred_thr",
            kernel: Kernel::PredThreshold,
            layout: Layout::ExitFirst,
            control: KSource::Const(5),
            sources: UP_AND_DOWN,
        }],
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `neon_predsum` forward-chain path: `ChainValidator::node_ok` admits a
/// multi-definition branch threshold as a constant and `lower` broadcasts its
/// layout-last value. Kill switch: `TRUST_CG_DISABLE_PASSES=neon_predsum`.
#[test]
fn neon_predsum_chain_compares_against_a_multi_def_leaf_as_its_last_constant() {
    let failures = run_cases(
        "neon-predsum",
        &[Case {
            name: "lw_chainpred",
            kernel: Kernel::ChainPred,
            layout: Layout::Natural,
            control: KSource::Runtime,
            sources: UP_AND_DOWN,
        }],
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `neon_predsum` `apply_candidate` root-select counting fusion: the arm `k`
/// of `select(a[i] > z, k, 0)` resolves to its layout-last `1`, so the sum is
/// lowered as `acc -= mask` (a count) instead of adding `k`.
/// Kill switch: `TRUST_CG_DISABLE_PASSES=neon_predsum`.
#[test]
fn neon_predsum_counting_fusion_reads_a_multi_def_arm_as_one() {
    let failures = run_cases(
        "neon-predsum",
        &[Case {
            name: "lw_pred_arm",
            kernel: Kernel::PredArm,
            layout: Layout::ExitFirst,
            control: KSource::Const(5),
            sources: &[("down_to_1", DOWN_TO_1)],
        }],
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `neon_predsum` `lower_select` masked-constant fast path: the else arm `k`
/// of `select(a[i] > z, a[i], k)` resolves to its layout-last `0`, so the
/// select is lowered as `mask & a[i]` and drops `k`.
/// Kill switch: `TRUST_CG_DISABLE_PASSES=neon_predsum`.
#[test]
fn neon_predsum_masked_select_reads_a_multi_def_else_arm_as_zero() {
    let failures = run_cases(
        "neon-predsum",
        &[Case {
            name: "lw_pred_else",
            kernel: Kernel::PredElse,
            layout: Layout::ExitFirst,
            control: KSource::Const(5),
            sources: &[("down_to_0", DOWN_TO_0)],
        }],
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `neon_predsum` `try_abs`: `k` in `a[i] < k ? k - a[i] : a[i]` resolves to
/// its layout-last `0`, so the select is lowered as `ABS(a[i])`.
/// Kill switch: `TRUST_CG_DISABLE_PASSES=neon_predsum`.
#[test]
fn neon_predsum_abs_reads_a_multi_def_operand_as_zero() {
    let failures = run_cases(
        "neon-predsum",
        &[Case {
            name: "lw_pred_abs",
            kernel: Kernel::PredAbs,
            layout: Layout::ExitFirst,
            control: KSource::Const(5),
            sources: &[("down_to_0", DOWN_TO_0), ("up_to_8", UP_TO_8)],
        }],
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `neon_iota_fill` `value_shape` reads the addend of `p[i] = trunc32(i) + k`
/// through its pass-local `const_value`, so a multi-definition `k` is stored
/// as `i + limit`. Kill switch: `TRUST_CG_DISABLE_PASSES=neon_iota_fill`.
#[test]
fn neon_iota_fill_stores_a_multi_def_addend_as_its_last_constant() {
    let failures = run_cases(
        "neon-iota-fill",
        &[Case {
            name: "lw_iota",
            kernel: Kernel::Iota,
            layout: Layout::SharedExit,
            control: KSource::Const(5),
            sources: UP_AND_DOWN,
        }],
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `ClosedFormReduction` (`reduction_split.rs`) resolves a loop-invariant
/// term operand with `resolve_const`, a layout-order fold over every
/// definition outside the loop, so it keeps the last one. It then DELETES the
/// loop and returns a closed form built with that constant: through
/// `closed_form_term_poly` for the fused reduction `acc += i * k` (`Madd`),
/// through `cf_operand_poly` for the `Madd` term of `acc += i * k + i`, and
/// through `inst_poly_core` for the `AddRR` term of `acc += (i + k) * i`.
/// Kill switch: `TRUST_CG_DISABLE_PASSES=closed_form_reduction`.
#[test]
fn closed_form_reduction_folds_a_multi_def_operand_as_its_last_constant() {
    let failures = run_cases(
        "closed-form-reduction",
        &[
            Case {
                name: "lw_cform_mul",
                kernel: Kernel::ClosedFormMul,
                layout: Layout::RuntimeBound,
                control: KSource::Const(5),
                sources: UP_AND_DOWN,
            },
            Case {
                name: "lw_cform_maddterm",
                kernel: Kernel::ClosedFormMaddTerm,
                layout: Layout::RuntimeBound,
                control: KSource::Const(5),
                sources: UP,
            },
            Case {
                name: "lw_cform_addmul",
                kernel: Kernel::ClosedFormAddMul,
                layout: Layout::RuntimeBound,
                control: KSource::Const(5),
                sources: UP,
            },
        ],
    );
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
