// trust-cg-opt - x86-64 conservative SSE2 integer vectorizer (OPT-12-TRANSFORM)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A **conservative** x86-64 SSE2 integer vectorizer operating on post-ISel
//! [`X86ISelFunction`]s.
//!
//! # Soundness stance
//!
//! Vectorization legality (no-aliasing, no loop-carried dependence) is **not**
//! checked by the per-instruction certificate stack: a wrong legality decision
//! is a *silent miscompile* that passes every downstream gate. Therefore this
//! pass makes legality **provable by construction** rather than by analysis, and
//! **refuses to transform** anything it cannot fully account for. The scalar
//! loop is always correct, so the fail-safe is: do nothing.
//!
//! # The single recognized shape
//!
//! An element-wise integer map over **distinct fixed-size local arrays**:
//!
//! ```text
//! let a = [..; N]; let b = [..; N]; let mut c = [0; N];
//! for i in 0..N { c[i] = a[i] OP b[i]; }   // OP in { +, -, &, |, ^ }
//! ```
//!
//! Post-ISel this is a natural loop whose body is a *linear chain* of blocks:
//! a unit-stride counter `iv` (init `0` in the preheader, `+1` in the latch,
//! `iv <u N` test in the header), three array accesses (`load a[iv]`,
//! `load b[iv]`, `store c[iv]`) each addressed by `base + iv*4` where `base` is
//! `Lea r, [StackSlot(k)]`, an i32 `AddRR`/`SubRR`/`AndRR`/`OrRR`/`XorRR`
//! combining the two loads into the stored value, and one **bounds-check
//! diamond per access** (`iv <u N` → continue else `Ud2`).
//!
//! # Legality by construction
//!
//! * **No aliasing.** The three accesses' bases each trace to a *distinct*
//!   `StackSlot(k)` (different `k`). Distinct stack slots occupy disjoint frame
//!   regions, so `a[iv]`, `b[iv]`, `c[iv]` provably never overlap for any `iv`.
//!   A base that is *not* a distinct local `StackSlot` (a pointer/reference/
//!   slice) is rejected — aliasing would be possible.
//! * **No loop-carried dependence.** The destination slot is written but never
//!   read (it is a third, distinct slot); each lane `iv` reads only `a[iv]`,
//!   `b[iv]` at the *same* index and writes only `c[iv]`. There is no recurrence
//!   or reduction. An index with any offset (`a[iv+1]`), a source that is also
//!   the destination slot, a reduction, or a non-unit stride all fail to match.
//! * **Unit stride, known trip count.** The counter is `0..N` unit stride with
//!   `N` a compile-time constant read off the header's `iv <u N` test. The
//!   packed body runs `floor(N/4)` iterations (4 i32 lanes) and the *unchanged
//!   original scalar loop* runs the `N % 4` remainder (trivially correct).
//! * **In-bounds, no trap.** Each array's stack slot is `>= N*4` bytes, and the
//!   index equals `iv < N`, so every access is in bounds: the original
//!   bounds-check `Ud2`s provably never fire for `iv in [0, N)`, and the packed
//!   loads/stores (indices `iv..iv+3 < N`) never touch memory outside a slot.
//!   Every off-chain edge of the body must target a single-`Ud2` block and its
//!   block must carry an `iv <u N` compare — anything else (e.g. an overflow
//!   trap) is rejected. So eliding the guards in the packed body is sound.
//! * **Wrapping arithmetic.** The scalar op is a plain `AddRR`/`SubRR`/… (no
//!   overflow guard); `PADDD`/`PSUBD` wrap mod 2^32 and `PAND`/`POR`/`PXOR` are
//!   bitwise — lane-for-lane identical to the scalar op.
//!
//! The emitted packed ops (`MOVDQU` loads/stores + `PADDD`/…) are proof-covered
//! (OPT-12-ENABLE) so the certificate stack and the translation validator
//! re-check them; this pass owns only the *legality* decision, which is made by
//! construction above.
//!
//! Beyond the element-wise map above, the pass recognizes four sibling slices
//! under the same soundness stance (each documented at its recognizer): the
//! constant/invariant FILL (`recognize_fill_loop`), the i32 saxpy
//! (`recognize_saxpy_loop`), the i32 sum/dot REDUCTION
//! (`recognize_reduction_loop`), and the i64 saxpy-ACCUMULATE at loop-invariant
//! flat offsets (`recognize_saxpyq_loop` — matmul's inner loop; the first slice
//! with RUNTIME legality checks that fail-safe to the scalar loop).
//!
//! Kill switch: `TCG_NO_VECTORIZE` (wired in the codegen pipeline).

use std::collections::{BTreeSet, HashMap, HashSet};

use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode};
use trust_cg_lower::function::StackSlotInfo;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelBlock, X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::x86_produces_value;
use crate::mach_view::{CfgAnalysis, GenericLoop, dominates};
use crate::x86_pass_manager::X86MachinePass;

/// SSE2 integer lanes for a 128-bit packed i32 operation.
const LANES: i64 = 4;
/// Byte size of the element type (i32) this slice handles.
const ELEM_SIZE: u8 = 4;
/// SSE2 integer lanes for a 128-bit packed i64 operation (the saxpy-Q slice).
const LANES_Q: i64 = 2;
/// Byte size of the i64 element type the saxpy-Q slice handles.
const ELEM_SIZE_Q: u8 = 8;

/// The conservative SSE2 integer vectorizer pass.
pub struct X86Vectorize;

impl X86Vectorize {
    /// Convenience entry point mirroring the other x86 passes.
    pub fn run_on_function(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func)
    }
}

impl X86MachinePass for X86Vectorize {
    fn name(&self) -> &str {
        "x86-vectorize"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(func)
    }
}

fn trace_enabled() -> bool {
    std::env::var_os("TCG_TRACE_VECTORIZE").is_some()
}

fn run_impl(func: &mut X86ISelFunction) -> bool {
    if func.block_order.len() < 2 {
        return false;
    }

    // Arch-neutral CFG analyses (preds / idom / natural loops) come from
    // `crate::mach_view`; only the vectorizer's single-latch rule stays
    // private (see `loops_from_cfg_analysis`).
    let cfg = CfgAnalysis::compute(func);
    let loops = loops_from_cfg_analysis(func, &cfg.loops);
    if loops.is_empty() {
        return false;
    }
    let preds = cfg.preds;
    let idom = cfg.idom;

    // DIAGNOSTIC (TCG_TRACE_VECTORIZE_DUMP): dump every natural loop's raw
    // post-ISel body so recognizer rejections can be diagnosed offline. This is
    // how new loop shapes are triaged (a dumped loop either matches a
    // recognizer's documented shape or shows exactly which construct broke it).
    if std::env::var_os("TCG_TRACE_VECTORIZE_DUMP").is_some() {
        for lp in &loops {
            eprintln!(
                "x86-vectorize[diag]: fn `{}` loop header={:?} latch={:?} depth={} preheader={:?} body_blocks={}",
                func.name,
                lp.header,
                lp.latch,
                lp.depth,
                lp.preheader,
                lp.body.len()
            );
            if lp.body.len() <= 12 {
                let mut blocks: Vec<Block> = lp.body.iter().copied().collect();
                blocks.sort_by_key(|b| {
                    func.block_order
                        .iter()
                        .position(|x| x == b)
                        .unwrap_or(usize::MAX)
                });
                for b in blocks {
                    if let Some(blk) = func.blocks.get(&b) {
                        eprintln!("  block {:?} succs={:?}", b, blk.successors);
                        for i in &blk.insts {
                            eprintln!("    {:?} {:?}", i.opcode, i.operands);
                        }
                    }
                }
            }
        }
    }

    // Recognize each loop against the immutable function first; only distinct,
    // fully-accounted-for element-wise maps (or constant fills) produce a plan.
    // Applying a plan touches only that loop's preheader terminator plus a few
    // fresh blocks (and, for a fill, one fresh 16-byte scratch slot), so plans
    // for different loops are independent.
    let mut plans: Vec<LoopPlan> = Vec::new();
    for lp in &loops {
        if let Some(plan) = recognize_elementwise_loop(func, &preds, lp) {
            plans.push(LoopPlan::Elementwise(plan));
        } else if let Some(plan) = recognize_fill_loop(func, &preds, &idom, lp) {
            plans.push(LoopPlan::Fill(plan));
        } else if let Some(plan) = recognize_runtime_byte_fill_loop(func, &preds, &idom, lp) {
            plans.push(LoopPlan::RuntimeByteFill(plan));
        } else if let Some(plan) = recognize_saxpy_loop(func, &preds, &idom, lp) {
            plans.push(LoopPlan::Saxpy(plan));
        } else if let Some(plan) = recognize_saxpyq_loop(func, &preds, &idom, lp) {
            plans.push(LoopPlan::SaxpyQ(plan));
        } else if let Some(plan) = recognize_reduction_loop(func, &preds, &idom, lp) {
            plans.push(LoopPlan::Reduction(plan));
        } else if let Some(plan) = recognize_byte_sum_reduction_loop(func, &preds, &idom, lp) {
            plans.push(LoopPlan::ByteSum(plan));
        } else if let Some(plan) = recognize_byte_eq_count_loop(func, &idom, lp) {
            plans.push(LoopPlan::ByteEqCount(plan));
        } else if let Some(plan) = recognize_kernighan_popcount_loop(func, lp) {
            plans.push(LoopPlan::Popcount(plan));
        } else if let Some(plan) = recognize_bitrev_loop(func, lp) {
            plans.push(LoopPlan::Bitrev(plan));
        } else if let Some(plan) = recognize_crc_table_loop(func, lp) {
            plans.push(LoopPlan::CrcTable(plan));
        } else if let Some(plan) = recognize_heap_sumq_loop(func, &preds, &idom, lp) {
            plans.push(LoopPlan::HeapSumQ(plan));
        } else if let Some(plan) = recognize_regarg_sumq_loop(func, &preds, &idom, lp) {
            plans.push(LoopPlan::RegArgSumQ(plan));
        } else if let Some(plan) = recognize_window_scan_loop(func, &preds, lp, &loops) {
            plans.push(LoopPlan::WindowScan(plan));
        }
    }
    if plans.is_empty() {
        return false;
    }

    let mut changed = false;
    for plan in plans {
        match plan {
            LoopPlan::Elementwise(plan) => {
                apply_plan(func, &plan);
                if trace_enabled() {
                    eprintln!(
                        "x86-vectorize: fn `{}` VECTORIZED elementwise {:?} loop: \
                         c[slot{}]=a[slot{}] {:?} b[slot{}], N={}, vN={}, lanes={} (i32)",
                        func.name,
                        plan.packed_op,
                        plan.slot_c,
                        plan.slot_lhs,
                        plan.packed_op,
                        plan.slot_rhs,
                        plan.n_trip,
                        (plan.n_trip / LANES) * LANES,
                        LANES,
                    );
                }
            }
            LoopPlan::Fill(plan) => {
                let lanes = 16 / plan.elem_size as i64;
                apply_fill_plan(func, &plan);
                if trace_enabled() {
                    let value = match plan.fill_value {
                        FillValue::Const(k) => format!("{:#x} (const)", k as u32),
                        FillValue::Invariant(v) => format!("{v} (loop-invariant runtime)"),
                    };
                    eprintln!(
                        "x86-vectorize: fn `{}` VECTORIZED fill loop: \
                         a[slot{}]={}, N={}, vN={}, lanes={} (u{})",
                        func.name,
                        plan.slot_c,
                        value,
                        plan.n_trip,
                        (plan.n_trip / lanes) * lanes,
                        lanes,
                        plan.elem_size as u32 * 8,
                    );
                }
            }
            LoopPlan::RuntimeByteFill(plan) => {
                apply_runtime_byte_fill_plan(func, &plan);
                if trace_enabled() {
                    eprintln!(
                        "x86-vectorize: fn `{}` VECTORIZED runtime byte-fill loop: \
                         *({:?} + iv) = low8({:?}) while iv <s {:?} (runtime), lanes=16 \
                         (u8; n<16 guard fail-safe to scalar)",
                        func.name, plan.base, plan.src, plan.n,
                    );
                }
            }
            LoopPlan::Reduction(plan) => {
                apply_reduction_plan(func, &plan);
                if trace_enabled() {
                    let k = match plan.kind {
                        ReduceKind::Sum => format!("s += a[slot{}]", plan.slot_a),
                        ReduceKind::Dot => {
                            format!("s += a[slot{}] * b[slot{}]", plan.slot_a, plan.slot_b)
                        }
                    };
                    eprintln!(
                        "x86-vectorize: fn `{}` VECTORIZED integer reduction loop: \
                         {k}, N={}, vN={}, lanes={} (i32, Paddd-accumulate + covered \
                         horizontal reduce)",
                        func.name,
                        plan.n_trip,
                        (plan.n_trip / LANES) * LANES,
                        LANES,
                    );
                }
            }
            LoopPlan::ByteEqCount(plan) => {
                let (k, bound, slot) = (plan.k, plan.bound, plan.slot);
                apply_byte_eq_count_plan(func, &plan);
                if trace_enabled() {
                    eprintln!(
                        "x86-vectorize: fn `{}` VECTORIZED byte-equality count: \
                         count += (a[slot{}][k] == {}) as u64, bound={}, lanes={} \
                         (u8, PCMPEQB+PSADBW accumulate; any IV start)",
                        func.name, slot, k, bound, LANES_B
                    );
                }
            }
            LoopPlan::ByteSum(plan) => {
                let vn = (plan.n_trip / LANES_B) * LANES_B;
                apply_byte_sum_plan(func, &plan);
                if trace_enabled() {
                    eprintln!(
                        "x86-vectorize: fn `{}` VECTORIZED widening byte sum-reduction: \
                         acc += a[slot{}][k] as u64, N={}, vN={}, lanes={} (u8, PSADBW \
                         byte-sum-accumulate + covered horizontal reduce)",
                        func.name, plan.slot, plan.n_trip, vn, LANES_B,
                    );
                }
            }
            LoopPlan::Popcount(plan) => {
                apply_popcount_swar(func, &plan);
                if trace_enabled() {
                    eprintln!(
                        "x86-vectorize: fn `{}` REWROTE Kernighan popcount loop -> \
                         branch-free SWAR popcount (c += popcount(x))",
                        func.name,
                    );
                }
            }
            LoopPlan::Bitrev(plan) => {
                apply_bitrev_swar(func, &plan);
                if trace_enabled() {
                    eprintln!(
                        "x86-vectorize: fn `{}` REWROTE 64-bit bit-reversal loop -> \
                         branch-free SWAR bit-reverse (r = reverse_bits(x))",
                        func.name,
                    );
                }
            }
            LoopPlan::CrcTable(plan) => {
                let poly = plan.poly;
                apply_crc_table(func, &plan);
                if trace_enabled() {
                    eprintln!(
                        "x86-vectorize: fn `{}` REWROTE 8-bit CRC bit-loop -> \
                         table lookup (POLY={:#x}, 256-entry stack table)",
                        func.name, poly,
                    );
                }
            }
            LoopPlan::HeapSumQ(plan) => {
                apply_heap_sumq_plan(func, &plan);
                if trace_enabled() {
                    eprintln!(
                        "x86-vectorize: fn `{}` VECTORIZED heap-slice i64 sum reduction: \
                         acc += elem[[slot{}+{}] + k*8], k <u len=[slot{}+{}] (runtime), \
                         {} replayed slice-temp store(s), lanes={} (i64, Paddq-accumulate \
                         + covered horizontal reduce; vN==0 fail-safe to scalar)",
                        func.name,
                        plan.ptr_slot,
                        plan.ptr_disp,
                        plan.len_slot,
                        plan.len_disp,
                        plan.stores.len(),
                        LANES_Q,
                    );
                }
            }
            LoopPlan::RegArgSumQ(plan) => {
                apply_regarg_sumq_plan(func, &plan);
                if trace_enabled() {
                    eprintln!(
                        "x86-vectorize: fn `{}` VECTORIZED reg-arg i64 sum reduction: \
                         acc += *(ptr{} + k*8), k <u len(reg {:?}) (runtime), \
                         ptr_reload={}, lanes={} (i64, Paddq-accumulate + covered \
                         horizontal reduce; vN==0 fail-safe to scalar)",
                        func.name,
                        if plan.ptr_reload {
                            format!("=[reg {:?}+{}]", plan.ptr_base, plan.ptr_disp)
                        } else {
                            format!("(reg {:?})", plan.ptr_base)
                        },
                        plan.len_reg,
                        plan.ptr_reload,
                        LANES_Q,
                    );
                }
            }
            LoopPlan::WindowScan(plan) => {
                apply_window_scan_plan(func, &plan);
                if trace_enabled() {
                    eprintln!(
                        "x86-vectorize: fn `{}` VECTORIZED window scan: \
                         matches += (hay[s..s+{}] == pat), s + {} <= {}, 16 windows/iter \
                         (PCMPEQB splats + PAND join + mask/POPCNT; scalar remainder)",
                        func.name, plan.m, plan.m, plan.n,
                    );
                }
            }
            LoopPlan::SaxpyQ(plan) => {
                apply_saxpyq_plan(func, &plan);
                if trace_enabled() {
                    eprintln!(
                        "x86-vectorize: fn `{}` VECTORIZED saxpy-Q (i64 RMW accumulate) loop: \
                         c[slot{}][{:?}*{}+j] += k*x[slot{}][{:?}*{}+j], k={:?}, N={}, vN={}, \
                         lanes={} (i64; PMULUDQ/PSLLQ/PSRLQ/PADDQ compose; {} runtime bound \
                         check(s) fail-safe to scalar)",
                        func.name,
                        plan.slot_c,
                        plan.leaf_c,
                        plan.mult_c,
                        plan.slot_x,
                        plan.leaf_x,
                        plan.mult_x,
                        plan.k,
                        plan.n_trip,
                        (plan.n_trip / LANES_Q) * LANES_Q,
                        LANES_Q,
                        plan.obligations.len(),
                    );
                }
            }
            LoopPlan::Saxpy(plan) => {
                apply_saxpy_plan(func, &plan);
                if trace_enabled() {
                    let k = match plan.k {
                        FillValue::Const(c) => format!("{} (const)", c as i32),
                        FillValue::Invariant(v) => format!("{v:?} (loop-invariant runtime)"),
                    };
                    let (o1, o2) = if plan.mul_is_first {
                        ("k*x", "y")
                    } else {
                        ("y", "k*x")
                    };
                    eprintln!(
                        "x86-vectorize: fn `{}` VECTORIZED saxpy loop: \
                         dest[slot{}] = {:?}({o1}, {o2}) with x[slot{}], y[slot{}], k={k}, \
                         N={}, vN={}, lanes={} (i32)",
                        func.name,
                        plan.slot_c,
                        plan.packed_op,
                        plan.slot_x,
                        plan.slot_add,
                        plan.n_trip,
                        (plan.n_trip / LANES) * LANES,
                        LANES,
                    );
                }
            }
        }
        changed = true;
    }
    changed
}

/// A recognized, legal-by-construction vectorization plan for one loop.
enum LoopPlan {
    /// `c[i] = a[i] OP b[i]` over three distinct local i32 arrays.
    Elementwise(VecPlan),
    /// `a[i] = CONST` over one distinct, write-only local i32 array.
    Fill(FillPlan),
    /// `for i in 0..n (signed) { *(base + i) = v }` with a RUNTIME trip count
    /// `n` and a loop-invariant pointer `base` — the `__trustcg_array_fill_i8`
    /// helper-loop shape: a pure byte fill through an invariant pointer,
    /// vectorized behind a runtime `n >= 16` guard. Sound with NO base
    /// provenance because the packed stores touch EXACTLY the byte addresses
    /// the scalar loop itself stores (a strict subset per entry guard).
    RuntimeByteFill(RuntimeByteFillPlan),
    /// `dest[i] = (INV * x[i]) (+|-) y[i]` (saxpy / element-wise FMA) over local
    /// i32 arrays, where `dest` may equal a source slot (same-index only).
    Saxpy(SaxpyPlan),
    /// `c[INV_C + i] = c[INV_C + i] + K * x[INV_X + i]` (the i64 read-modify-
    /// write accumulate at a loop-invariant flat offset — matmul's inner loop)
    /// over local i64 arrays, with runtime bound checks that fail-safe to the
    /// scalar loop.
    SaxpyQ(SaxpyQPlan),
    /// An integer sum-reduction `for k { acc = acc + a[k] }` (Sum) or
    /// `for k { acc = acc + a[k]*b[k] }` (Dot) over local i32 arrays, with `acc`
    /// a loop-carried scalar (register) accumulator that never escapes to memory
    /// mid-loop and is used only for the reduction.
    Reduction(ReducePlan),
    /// A widening byte sum-reduction `for k { acc += a[k] as u64 }` over a local
    /// `[u8; N]` with a Gpr64 accumulator, lowered to a PSADBW byte-sum loop.
    /// Opt-in behind `TCG_X86_BYTE_SUM`. See [`ByteSumPlan`].
    ByteSum(ByteSumPlan),
    /// Byte-equality count reduction. See [`ByteEqCountPlan`].
    ByteEqCount(ByteEqCountPlan),
    /// A Kernighan popcount idiom `while x!=0 { x&=x-1; c+=1 }` lowered to the
    /// branch-free SWAR popcount. Opt-in behind `TCG_X86_POPCOUNT_IDIOM`. See
    /// [`PopcountPlan`].
    Popcount(PopcountPlan),
    /// A 64-bit bit-reversal idiom `for _ in 0..64 { r=(r<<1)|(x&1); x>>=1 }`
    /// lowered to the branch-free SWAR bit-reverse. Opt-in behind
    /// `TCG_X86_BITREV_IDIOM`. See [`BitrevPlan`].
    Bitrev(BitrevPlan),
    /// An 8-bit CRC bit-serial loop `for _ in 0..8 { crc=(crc>>1)^(POLY&-(crc&1)) }`
    /// lowered to a stack-table lookup. Opt-in behind `TCG_X86_CRC_TABLE`. See
    /// [`CrcTablePlan`].
    CrcTable(CrcTablePlan),
    /// An i64 sum-reduction over a HEAP slice with a RUNTIME trip count
    /// (`while k < v.len() { acc += v[k] }` over a `Vec<u64>`/`&[u64]`), with
    /// the slice (ptr, len) read from invariant stack-slot fields and a
    /// runtime `vN = len & !1` gate that fail-safes to the scalar loop.
    HeapSumQ(HeapSumQPlan),
    /// An i64 sum-reduction `for i in 0..s.len() { acc += s[i] }` over a slice
    /// whose `(ptr, len)` arrive in REGISTERS (a `&[i64]`/`Vec<i64>` argument,
    /// post-SROA), with a runtime trip count. The header bound and every
    /// per-element guard are the SAME loop-invariant length register (own-length
    /// identity) and the loop contains no stores (a pure reduction ⇒ no aliasing
    /// and any invariant-address reload is sound). Runtime `vN = len & !1` gate
    /// fail-safes to the scalar loop. See [`RegArgSumQPlan`].
    RegArgSumQ(RegArgSumQPlan),
    /// The b16 window-scan nest: `matches += (hay[s..s+M] == pat)` counted
    /// branchlessly 16 windows at a time (PCMPEQB splats + PAND join +
    /// mask-extract/POPCNT). Opt-in behind `TCG_X86_WINDOW_SCAN` (stage 1).
    /// See [`WindowScanPlan`].
    WindowScan(WindowScanPlan),
}

// ===========================================================================
// Recognition
// ===========================================================================

/// A verified-legal element-wise map ready to be rewritten to a packed loop
/// plus a scalar remainder. Every field is established by construction in
/// `recognize_elementwise_loop`.
struct VecPlan {
    /// The loop counter vreg (element index; init 0, +1 per scalar iteration).
    iv: VReg,
    /// Compile-time trip count `N` (from the header `iv <u N` test).
    n_trip: i64,
    /// Base-address vregs (`Lea r, [StackSlot(k)]`) of the two source arrays
    /// and the destination array; `slot_*` are their (distinct) slot indices.
    base_lhs: VReg,
    base_rhs: VReg,
    base_c: VReg,
    slot_lhs: u32,
    slot_rhs: u32,
    slot_c: u32,
    /// Packed opcode to emit (PADDD/PSUBD/PAND/POR/PXOR).
    packed_op: X86Opcode,
    /// The loop's preheader (its terminator is redirected to the vector loop).
    preheader: Block,
    /// The scalar loop header (the vector loop falls into it for the remainder).
    header: Block,
}

/// Symbolic provenance of a value/address inside the loop, relative to the IV.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Prov {
    /// Exactly the loop counter value `iv`.
    Iv,
    /// A compile-time constant.
    Const(i64),
    /// The base address of `StackSlot(k)` (a distinct local allocation).
    SlotBase(u32),
    /// `iv * k`.
    ScaledIv(i64),
    /// The address `&slot[k][iv]` with a per-element stride of `scale` bytes
    /// (i.e. `SlotBase(k) + iv*scale`, disp 0). `ElemAddr(slot, scale)`. The
    /// scale is carried (not fixed to `ELEM_SIZE`) so the same provenance is
    /// element-width-agnostic: the *caller* checks `scale` against the memory
    /// op's actual width. This keeps the `prov` memo correct regardless of which
    /// element size a recognizer is looking for.
    ElemAddr(u32, i64),
    /// `leaf * m` where `leaf` is a vreg the template cannot classify further
    /// (its canonical vreg identity is carried so two syntactic recomputations
    /// of the same product compare equal). NOTE: this says NOTHING about
    /// invariance — the consumer must independently prove `leaf` has no def
    /// inside the loop body before treating the product as loop-invariant.
    InvMulConst(VReg, i64),
    /// `leaf*m + iv` — a flat element index at a (potentially) loop-invariant
    /// base offset (`c[i*N + j]` with `iv = j`, `leaf = i`, `m = N`).
    IvPlusInvMul(VReg, i64),
    /// `(leaf*m + iv) * scale` — the flat index scaled to a byte offset.
    ScaledIvPlusInvMul(VReg, i64, i64),
    /// `SlotBase(slot) + (leaf*m + iv)*scale` — the address
    /// `&slot[leaf*m + iv]` with a per-element stride of `scale` bytes.
    /// `ElemAddrInvMul(slot, scale, leaf, m)`.
    ElemAddrInvMul(u32, i64, VReg, i64),
    /// Anything not matched by the template.
    Unknown,
}

/// Single-def index over the whole function (only vregs with exactly one def).
struct DefIndex {
    /// vreg -> its unique defining (block, inst-index), if def count == 1.
    single: HashMap<VReg, (Block, usize)>,
}

impl DefIndex {
    fn build(func: &X86ISelFunction) -> Self {
        let mut counts: HashMap<VReg, u32> = HashMap::new();
        let mut single: HashMap<VReg, (Block, usize)> = HashMap::new();
        for block_id in &func.block_order {
            let Some(block) = func.blocks.get(block_id) else {
                continue;
            };
            for (idx, inst) in block.insts.iter().enumerate() {
                if !x86_produces_value(inst.opcode) {
                    continue;
                }
                if let Some(X86ISelOperand::VReg(v)) = inst.operands.first() {
                    *counts.entry(*v).or_insert(0) += 1;
                    single.insert(*v, (*block_id, idx));
                }
            }
        }
        // Drop multi-def vregs from `single` so a lookup means "unique def".
        single.retain(|v, _| counts.get(v) == Some(&1));
        DefIndex { single }
    }

    fn def_inst<'a>(&self, func: &'a X86ISelFunction, v: VReg) -> Option<&'a X86ISelInst> {
        let (b, i) = *self.single.get(&v)?;
        func.blocks.get(&b)?.insts.get(i)
    }
}

/// Follow `MovRR`/`MovRR32` single-def copy chains to a canonical root vreg.
fn canon(func: &X86ISelFunction, defs: &DefIndex, mut v: VReg) -> VReg {
    for _ in 0..64 {
        let Some(inst) = defs.def_inst(func, v) else {
            return v;
        };
        match inst.opcode {
            X86Opcode::MovRR | X86Opcode::MovRR32 => {
                if let Some(X86ISelOperand::VReg(s)) = inst.operands.get(1) {
                    v = *s;
                    continue;
                }
                return v;
            }
            _ => return v,
        }
    }
    v
}

/// Symbolic provenance of `v` relative to `iv` (memoized, bounded recursion).
fn prov(
    func: &X86ISelFunction,
    defs: &DefIndex,
    iv: VReg,
    v: VReg,
    memo: &mut HashMap<VReg, Prov>,
    depth: u32,
) -> Prov {
    if v == iv {
        return Prov::Iv;
    }
    if let Some(p) = memo.get(&v) {
        return *p;
    }
    if depth > 64 {
        return Prov::Unknown;
    }
    let result = (|| {
        let Some(inst) = defs.def_inst(func, v) else {
            return Prov::Unknown;
        };
        match inst.opcode {
            X86Opcode::MovRR | X86Opcode::MovRR32 => match inst.operands.get(1) {
                Some(X86ISelOperand::VReg(s)) => prov(func, defs, iv, *s, memo, depth + 1),
                _ => Prov::Unknown,
            },
            X86Opcode::MovRI => match inst.operands.get(1) {
                Some(X86ISelOperand::Imm(c)) => Prov::Const(*c),
                _ => Prov::Unknown,
            },
            X86Opcode::Lea => match inst.operands.get(1) {
                Some(X86ISelOperand::MemAddr { base, disp }) if *disp == 0 => match base.as_ref() {
                    X86ISelOperand::StackSlot(s) => Prov::SlotBase(*s),
                    _ => Prov::Unknown,
                },
                _ => Prov::Unknown,
            },
            X86Opcode::LeaSib => match inst.operands.get(1) {
                Some(X86ISelOperand::SibMemAddr {
                    base,
                    index,
                    scale,
                    disp,
                }) if *disp == 0 => {
                    let base_p = match base.as_ref() {
                        X86ISelOperand::VReg(b) => prov(func, defs, iv, *b, memo, depth + 1),
                        _ => Prov::Unknown,
                    };
                    let index_p = match index.as_ref() {
                        X86ISelOperand::VReg(ix) => prov(func, defs, iv, *ix, memo, depth + 1),
                        _ => Prov::Unknown,
                    };
                    match (base_p, index_p) {
                        // Element-width-agnostic: carry the SIB scale; the caller
                        // checks it against the memory op's actual width.
                        (Prov::SlotBase(s), Prov::Iv) => Prov::ElemAddr(s, *scale as i64),
                        _ => Prov::Unknown,
                    }
                }
                _ => Prov::Unknown,
            },
            X86Opcode::ImulRR => {
                let (x, y) = match (inst.operands.get(1), inst.operands.get(2)) {
                    (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => (*x, *y),
                    _ => return Prov::Unknown,
                };
                let px = prov(func, defs, iv, x, memo, depth + 1);
                let py = prov(func, defs, iv, y, memo, depth + 1);
                match (px, py) {
                    (Prov::Iv, Prov::Const(c)) | (Prov::Const(c), Prov::Iv) => Prov::ScaledIv(c),
                    // `(leaf*m + iv) * scale` — the flat index scaled to bytes.
                    (Prov::IvPlusInvMul(l, m), Prov::Const(s))
                    | (Prov::Const(s), Prov::IvPlusInvMul(l, m)) => {
                        Prov::ScaledIvPlusInvMul(l, m, s)
                    }
                    // `leaf * m` where `leaf` is otherwise unclassifiable: carry
                    // the canonical leaf vreg so structurally-equal recomputations
                    // compare equal. Restricted to `Unknown` on purpose — an
                    // iv-derived or slot-derived side must NOT be folded into a
                    // "leaf" (the consumer's invariance check is per-vreg).
                    (Prov::Unknown, Prov::Const(c)) => Prov::InvMulConst(canon(func, defs, x), c),
                    (Prov::Const(c), Prov::Unknown) => Prov::InvMulConst(canon(func, defs, y), c),
                    _ => Prov::Unknown,
                }
            }
            X86Opcode::AddRR => {
                let (x, y) = match (inst.operands.get(1), inst.operands.get(2)) {
                    (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => (*x, *y),
                    _ => return Prov::Unknown,
                };
                let px = prov(func, defs, iv, x, memo, depth + 1);
                let py = prov(func, defs, iv, y, memo, depth + 1);
                match (px, py) {
                    // `base + iv*k` → element address with per-element stride `k`
                    // bytes. The scale is carried; the caller checks it against
                    // the memory op's actual width.
                    (Prov::SlotBase(s), Prov::ScaledIv(k))
                    | (Prov::ScaledIv(k), Prov::SlotBase(s)) => Prov::ElemAddr(s, k),
                    // `base + iv` → element address with per-element stride 1 (a
                    // `[u8; N]` byte array: u8 elements need no index scaling, so
                    // isel emits a plain `AddRR base, iv`). The scale-1 carry is
                    // checked against the memory op's actual width by the caller
                    // (`elem_addr_slot(.., elem_size)` — only a 1-byte access
                    // matches), so this is INERT for the i32/i64 recognizers
                    // (elem_size 4/8) — verified: default (byte-sum-off) codegen
                    // is byte-identical to HEAD on all 18 perf benches. Only the
                    // opt-in byte-sum reduction recognizer passes elem_size 1.
                    (Prov::SlotBase(s), Prov::Iv) | (Prov::Iv, Prov::SlotBase(s)) => {
                        Prov::ElemAddr(s, 1)
                    }
                    // `leaf*m + iv` — a flat index at an invariant-candidate
                    // offset.
                    (Prov::InvMulConst(l, m), Prov::Iv) | (Prov::Iv, Prov::InvMulConst(l, m)) => {
                        Prov::IvPlusInvMul(l, m)
                    }
                    // `base + (leaf*m + iv)*scale` → `&slot[leaf*m + iv]`.
                    (Prov::SlotBase(s), Prov::ScaledIvPlusInvMul(l, m, k))
                    | (Prov::ScaledIvPlusInvMul(l, m, k), Prov::SlotBase(s)) => {
                        Prov::ElemAddrInvMul(s, k, l, m)
                    }
                    _ => Prov::Unknown,
                }
            }
            _ => Prov::Unknown,
        }
    })();
    memo.insert(v, result);
    result
}

/// Opcodes permitted to appear in the loop body outside the recognized memory
/// ops / arithmetic op / IV update. All are side-effect-free control/compute
/// (no memory write, no call, no trap). Any opcode outside this set (plus the
/// explicitly-recognized load/store/op opcodes) forces a bail.
fn is_whitelisted_body_opcode(op: X86Opcode) -> bool {
    matches!(
        op,
        X86Opcode::MovRR
            | X86Opcode::MovRR32
            | X86Opcode::MovRI
            | X86Opcode::Movzx
            | X86Opcode::MovzxW
            | X86Opcode::MovsxB
            | X86Opcode::MovsxW
            | X86Opcode::Movsx
            | X86Opcode::CmpRR
            | X86Opcode::CmpRI
            | X86Opcode::CmpRI8
            | X86Opcode::TestRR
            | X86Opcode::TestRI
            | X86Opcode::Setcc
            | X86Opcode::AndRI
            | X86Opcode::Lea
            | X86Opcode::LeaSib
            | X86Opcode::ImulRR
            | X86Opcode::ImulRRI
            | X86Opcode::AddRR
            | X86Opcode::SubRR
            | X86Opcode::AndRR
            | X86Opcode::OrRR
            | X86Opcode::XorRR
            | X86Opcode::Jcc
            | X86Opcode::Jmp
    )
}

/// Map an i32 scalar reg-reg arithmetic opcode to its SSE2 packed-dword form.
fn scalar_to_packed(op: X86Opcode) -> Option<X86Opcode> {
    match op {
        X86Opcode::AddRR => Some(X86Opcode::Paddd),
        X86Opcode::SubRR => Some(X86Opcode::Psubd),
        X86Opcode::AndRR => Some(X86Opcode::Pand),
        X86Opcode::OrRR => Some(X86Opcode::Por),
        X86Opcode::XorRR => Some(X86Opcode::Pxor),
        _ => None,
    }
}

fn is_load_opcode(op: X86Opcode) -> bool {
    matches!(
        op,
        X86Opcode::MovRM8
            | X86Opcode::MovRM16
            | X86Opcode::MovRM32
            | X86Opcode::MovRM
            | X86Opcode::MovRMSib
            | X86Opcode::MovdquRM
            | X86Opcode::MovdqaRM
            | X86Opcode::MovsdRM
            | X86Opcode::MovssRM
    )
}

fn is_store_opcode(op: X86Opcode) -> bool {
    matches!(
        op,
        X86Opcode::MovMR8
            | X86Opcode::MovMR16
            | X86Opcode::MovMR32
            | X86Opcode::MovMR
            | X86Opcode::MovMRSib
            | X86Opcode::MovdquMR
            | X86Opcode::MovdqaMR
            | X86Opcode::MovsdMR
            | X86Opcode::MovssMR
    )
}

/// Return the block's single successor that lies inside `body` (the next chain
/// block), or `None` if the count of in-body successors is not exactly one.
fn unique_in_body_succ(succs: &[Block], body: &BTreeSet<Block>) -> Option<Block> {
    let mut in_body = succs.iter().filter(|s| body.contains(s));
    let first = in_body.next()?;
    if in_body.next().is_some() {
        return None;
    }
    Some(*first)
}

/// A pure-trap block is exactly one `Ud2` (a bounds-check panic under
/// panic=abort). We require this exact shape so we never elide a guard whose
/// failure path does anything observable.
fn is_pure_trap_block(func: &X86ISelFunction, b: Block) -> bool {
    match func.blocks.get(&b) {
        Some(block) => block.insts.len() == 1 && block.insts[0].opcode == X86Opcode::Ud2,
        None => false,
    }
}

/// True if `block_id`'s instructions contain a compare of `iv` against a
/// constant `c` with `c >= n_trip` — i.e. a bounds check that provably never
/// traps for `iv in [0, n_trip)`. Used to confirm every trapping side-exit is
/// an in-bounds bounds check (not, e.g., an overflow trap).
fn block_has_iv_bound_compare(
    func: &X86ISelFunction,
    defs: &DefIndex,
    iv: VReg,
    memo: &mut HashMap<VReg, Prov>,
    block_id: Block,
    n_trip: i64,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    for inst in &block.insts {
        match inst.opcode {
            X86Opcode::CmpRR => {
                if let (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) =
                    (inst.operands.first(), inst.operands.get(1))
                {
                    let px = prov(func, defs, iv, *x, memo, 0);
                    let py = prov(func, defs, iv, *y, memo, 0);
                    if let (Prov::Iv, Prov::Const(c)) | (Prov::Const(c), Prov::Iv) = (px, py)
                        && c >= n_trip
                    {
                        return true;
                    }
                }
            }
            X86Opcode::CmpRI | X86Opcode::CmpRI8 => {
                if let (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::Imm(c))) =
                    (inst.operands.first(), inst.operands.get(1))
                    && prov(func, defs, iv, *x, memo, 0) == Prov::Iv
                    && *c >= n_trip
                {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

/// True if `inst` is a `TrapBoundsCheckExact [base, index, Imm(bound)]`
/// proof-only bounds-check carrier that provably never traps for
/// `iv in [0, n_trip)`. The carrier expands to `CMP index, bound; Jcc AE -> UD2`
/// (traps iff `index >=u bound`), so it is a redundant in-bounds guard exactly
/// when `index` is the loop counter itself and `bound >= n_trip`: then
/// `iv < n_trip <= bound` for every vectorized iteration (`iv >= 0`), so no trap
/// ever fires. Such a carrier is safe to OMIT from the packed loop — the packed
/// accesses are independently proven in-slot by the recognizer's slot-size check,
/// and the untouched scalar remainder retains the carrier — so dropping it in the
/// vector portion is behavior-preserving. This is the inline-carrier analogue of
/// [`block_has_iv_bound_compare`] (which handles the `Jcc AE -> Ud2` trap-block
/// form of the same guard) and enforces the identical `bound >= n_trip`
/// discipline.
fn is_safe_iv_bounds_carrier(
    func: &X86ISelFunction,
    defs: &DefIndex,
    iv: VReg,
    memo: &mut HashMap<VReg, Prov>,
    inst: &X86ISelInst,
    n_trip: i64,
) -> bool {
    if inst.opcode != X86Opcode::TrapBoundsCheckExact {
        return false;
    }
    let (index, bound) = match (inst.operands.get(1), inst.operands.get(2)) {
        (Some(X86ISelOperand::VReg(index)), Some(X86ISelOperand::Imm(bound))) => (*index, *bound),
        _ => return false,
    };
    prov(func, defs, iv, index, memo, 0) == Prov::Iv && bound >= n_trip
}

/// Extract `(iv, n_trip, body_entry)` from the loop header: the header must
/// compare a copy of a unit-stride counter against a constant and branch into
/// the body on `iv <u N`. Returns the counter vreg, the constant N, and the
/// header's in-body successor.
fn recognize_header(
    func: &X86ISelFunction,
    defs: &DefIndex,
    header: Block,
    body: &BTreeSet<Block>,
) -> Option<(VReg, i64)> {
    let block = func.blocks.get(&header)?;
    // A header comparing `iv` against a constant: find a CmpRR/CmpRI whose
    // operands are {a counter vreg, a constant}. The counter is whatever the
    // caller confirms as the IV (init 0 / +1); here we return the candidate.
    for inst in &block.insts {
        match inst.opcode {
            X86Opcode::CmpRR => {
                let (a, b) = match (inst.operands.first(), inst.operands.get(1)) {
                    (Some(X86ISelOperand::VReg(a)), Some(X86ISelOperand::VReg(b))) => (*a, *b),
                    _ => continue,
                };
                // One side must be a MovRI constant; the other the counter.
                if let Some(n) = const_of(func, defs, b) {
                    let iv = canon(func, defs, a);
                    if is_counter(func, defs, iv, body) {
                        return Some((iv, n));
                    }
                    report_zero_init_only_decline(func, defs, iv, body, header);
                }
                if let Some(n) = const_of(func, defs, a) {
                    let iv = canon(func, defs, b);
                    if is_counter(func, defs, iv, body) {
                        return Some((iv, n));
                    }
                    report_zero_init_only_decline(func, defs, iv, body, header);
                }
            }
            X86Opcode::CmpRI | X86Opcode::CmpRI8 => {
                if let (Some(X86ISelOperand::VReg(a)), Some(X86ISelOperand::Imm(n))) =
                    (inst.operands.first(), inst.operands.get(1))
                {
                    let iv = canon(func, defs, *a);
                    if is_counter(func, defs, iv, body) {
                        return Some((iv, *n));
                    }
                    report_zero_init_only_decline(func, defs, iv, body, header);
                }
            }
            _ => {}
        }
    }
    None
}

/// Diagnostic for the ONE reason this header analysis declines that is a
/// generality gap rather than a real disqualifier: the IV is a perfectly good
/// unit counter, but it does not start at literal 0.
///
/// ⚑ Silence proves nothing, so this logs the ACCEPT-but-for-init case
/// explicitly. It exists to answer "would relaxing the zero-init rule actually
/// fire on anything?" with a measurement instead of a guess — the zero-init
/// restriction is load-bearing for every tier that still uses the
/// `(n / 16) * 16` guard, so relaxing it is only worth doing where it pays.
fn report_zero_init_only_decline(
    func: &X86ISelFunction,
    defs: &DefIndex,
    iv: VReg,
    body: &BTreeSet<Block>,
    header: Block,
) {
    if !trace_enabled() {
        return;
    }
    if is_counter_any_init(func, defs, iv, body) {
        eprintln!(
            "x86-vectorize[diag]: fn `{}` header={header:?} DECLINED ONLY BY ZERO-INIT: \
             {iv:?} is a unit counter with a non-zero/runtime start",
            func.name
        );
    }
}

fn const_of(func: &X86ISelFunction, defs: &DefIndex, v: VReg) -> Option<i64> {
    match defs.def_inst(func, v)?.opcode {
        X86Opcode::MovRI => match defs.def_inst(func, v)?.operands.get(1) {
            Some(X86ISelOperand::Imm(c)) => Some(*c),
            _ => None,
        },
        _ => None,
    }
}

/// A unit-stride loop counter: defined `= 0` outside the body (preheader) and
/// re-defined `= iv + 1` inside the latch (both defs are the same vreg). We
/// verify: at least one def is `MovRR from (MovRI 0)` reached from a non-body
/// block, and at least one def is the writeback of `AddRR [iv, iv, MovRI 1]`.
fn is_counter(func: &X86ISelFunction, defs: &DefIndex, iv: VReg, body: &BTreeSet<Block>) -> bool {
    let mut saw_zero_init_outside = false;
    let mut saw_unit_increment_inside = false;
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        let in_body = body.contains(block_id);
        for (idx, inst) in block.insts.iter().enumerate() {
            // A def of `iv` via `MovRR [iv, src]`.
            if inst.opcode == X86Opcode::MovRR
                && matches!(inst.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == iv)
            {
                let Some(X86ISelOperand::VReg(src)) = inst.operands.get(1) else {
                    continue;
                };
                if !in_body {
                    // Preheader-style init: src is a constant 0.
                    if const_of(func, defs, *src) == Some(0) {
                        saw_zero_init_outside = true;
                    }
                } else {
                    // Latch-style writeback: src = iv + 1.
                    if is_iv_plus_one(func, defs, iv, *src) {
                        saw_unit_increment_inside = true;
                    }
                }
                let _ = idx;
            }
        }
    }
    saw_zero_init_outside && saw_unit_increment_inside
}

/// True if `v` is defined by `AddRR [v, iv, one]` (or `iv, MovRI 1` in either
/// order) — i.e. `v == iv + 1`.
fn is_iv_plus_one(func: &X86ISelFunction, defs: &DefIndex, iv: VReg, v: VReg) -> bool {
    let Some(inst) = defs.def_inst(func, v) else {
        return false;
    };
    if inst.opcode != X86Opcode::AddRR {
        return false;
    }
    let (x, y) = match (inst.operands.get(1), inst.operands.get(2)) {
        (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => (*x, *y),
        _ => return false,
    };
    let cx = canon(func, defs, x);
    let cy = canon(func, defs, y);
    (cx == iv && const_of(func, defs, y) == Some(1))
        || (cy == iv && const_of(func, defs, x) == Some(1))
}

/// The core recognizer: returns a legal `VecPlan` iff `lp` is exactly the
/// distinct-array element-wise i32 map described in the module docs, or `None`.
fn recognize_elementwise_loop(
    func: &X86ISelFunction,
    preds: &HashMap<Block, Vec<Block>>,
    lp: &LoopInfo,
) -> Option<VecPlan> {
    let header = lp.header;
    let latch = lp.latch;
    let body = &lp.body;
    let preheader = lp.preheader?;

    // No PHI pseudo anywhere in the loop (this backend's isel is non-SSA here;
    // a PHI would need incoming-edge rewiring we do not perform).
    for block_id in body {
        let block = func.blocks.get(block_id)?;
        if block.insts.iter().any(|i| i.opcode == X86Opcode::Phi) {
            return None;
        }
    }

    let defs = DefIndex::build(func);
    let mut memo: HashMap<VReg, Prov> = HashMap::new();

    // 1. IV + trip count from the header.
    let (iv, n_trip) = recognize_header(func, &defs, header, body)?;
    if n_trip < LANES {
        return None; // no full vector iteration to gain from.
    }

    // 2. The header's in-body successor starts the body chain; its other
    //    successor is the loop exit (unchanged).
    let header_succs = &func.blocks.get(&header)?.successors;
    let body_entry = unique_in_body_succ(header_succs, body)?;

    // 3. Walk the body as a linear chain body_entry -> ... -> latch. Confirm
    //    every visited block is in `body`, every off-chain edge targets a
    //    pure-`Ud2` trap block, and every block with a trap edge carries an
    //    `iv <u N` bounds compare (so all traps are in-bounds bounds checks
    //    that provably never fire for iv in [0, N)).
    let mut chain: Vec<Block> = Vec::new();
    let mut visited: HashSet<Block> = HashSet::new();
    let mut cur = body_entry;
    loop {
        if !body.contains(&cur) || !visited.insert(cur) {
            return None;
        }
        chain.push(cur);
        let succs = &func.blocks.get(&cur)?.successors;
        // Off-chain edges must be pure traps.
        let mut has_trap_edge = false;
        for s in succs {
            if body.contains(s) {
                continue;
            }
            if !is_pure_trap_block(func, *s) {
                return None;
            }
            has_trap_edge = true;
        }
        if has_trap_edge && !block_has_iv_bound_compare(func, &defs, iv, &mut memo, cur, n_trip) {
            return None;
        }
        if cur == latch {
            break;
        }
        let next = unique_in_body_succ(succs, body)?;
        cur = next;
    }
    // The latch's only in-body successor must be the header (the back-edge).
    if unique_in_body_succ(&func.blocks.get(&latch)?.successors, body)? != header {
        return None;
    }
    // Every body block except the header must be on the chain (nothing hidden).
    for block_id in body {
        if *block_id != header && !visited.contains(block_id) {
            return None;
        }
    }
    // The header must have exactly one non-body (exit) successor and one body
    // successor, and the preheader must be the header's only non-body pred.
    {
        let hsuccs = &func.blocks.get(&header)?.successors;
        let non_body: Vec<Block> = hsuccs
            .iter()
            .copied()
            .filter(|s| !body.contains(s))
            .collect();
        if non_body.len() != 1 {
            return None;
        }
        let empty = Vec::new();
        let hpreds = preds.get(&header).unwrap_or(&empty);
        let non_body_preds: Vec<Block> = hpreds
            .iter()
            .copied()
            .filter(|p| !body.contains(p))
            .collect();
        if non_body_preds != vec![preheader] {
            return None;
        }
    }

    // 4. Collect the memory ops in the chain and classify addresses.
    //    Exactly two i32 loads from distinct ElemAddr slots and one i32 store
    //    to a third ElemAddr slot; no other memory op or call anywhere.
    let mut loads: Vec<(VReg, u32)> = Vec::new(); // (canonical dst, slot)
    let mut store: Option<(u32, VReg)> = None; // (slot, canonical stored src)
    for block_id in &chain {
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            let op = inst.opcode;
            if op == X86Opcode::Call || op == X86Opcode::CallR || op == X86Opcode::CallM {
                return None;
            }
            if is_load_opcode(op) {
                // Only i32 loads with a plain [ElemAddr + 0] address.
                if op != X86Opcode::MovRM32 {
                    return None;
                }
                let dst = match inst.operands.first() {
                    Some(X86ISelOperand::VReg(d)) => *d,
                    _ => return None,
                };
                let slot = elem_addr_slot(
                    func,
                    &defs,
                    iv,
                    &mut memo,
                    inst.operands.get(1),
                    ELEM_SIZE as i64,
                )?;
                loads.push((canon(func, &defs, dst), slot));
            } else if is_store_opcode(op) {
                if op != X86Opcode::MovMR32 || store.is_some() {
                    return None;
                }
                let slot = elem_addr_slot(
                    func,
                    &defs,
                    iv,
                    &mut memo,
                    inst.operands.first(),
                    ELEM_SIZE as i64,
                )?;
                let src = match inst.operands.get(1) {
                    Some(X86ISelOperand::VReg(s)) => canon(func, &defs, *s),
                    _ => return None,
                };
                store = Some((slot, src));
            } else if op == X86Opcode::TrapBoundsCheckExact {
                // Inline proof-only bounds-check carrier: admit only when it
                // provably never traps for iv in [0, n_trip) (index==iv,
                // bound>=n_trip). The packed loop omits it (accesses proven
                // in-slot); the scalar remainder retains it.
                if !is_safe_iv_bounds_carrier(func, &defs, iv, &mut memo, inst, n_trip) {
                    return None;
                }
            } else if !is_whitelisted_body_opcode(op) {
                // Closed world: any unclassified opcode is a potential hidden
                // side effect (or trap) — refuse.
                return None;
            }
        }
    }
    if loads.len() != 2 {
        return None;
    }
    let (slot_c, stored_src) = store?;

    // 5. The stored value must be `packed_op(load_lhs, load_rhs)` — a single
    //    plain i32 reg-reg arithmetic op combining the two loaded values.
    let op_inst = defs.def_inst(func, stored_src)?;
    let packed_op = scalar_to_packed(op_inst.opcode)?;
    let (ox, oy) = match (op_inst.operands.get(1), op_inst.operands.get(2)) {
        (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => {
            (canon(func, &defs, *x), canon(func, &defs, *y))
        }
        _ => return None,
    };
    let slot_of = |v: VReg| -> Option<u32> { loads.iter().find(|(d, _)| *d == v).map(|(_, s)| *s) };
    let slot_lhs = slot_of(ox)?;
    let slot_rhs = slot_of(oy)?;

    // 6. No-alias / no-dependence by construction: the two source slots and the
    //    destination slot must all be distinct.
    if slot_lhs == slot_rhs || slot_lhs == slot_c || slot_rhs == slot_c {
        return None;
    }

    // 7. Each slot must be at least N*4 bytes (holds >= N i32 elements), so the
    //    packed accesses over indices [0, floor(N/4)*4) stay strictly in-slot.
    let need_bytes = n_trip.checked_mul(ELEM_SIZE as i64)?;
    for slot in [slot_lhs, slot_rhs, slot_c] {
        let info = func.stack_slots.get(slot as usize)?;
        if (info.size as i64) < need_bytes {
            return None;
        }
    }

    // 8. Resolve each slot back to its base-address vreg (`Lea r,[StackSlot]`).
    let base_lhs = slot_base_vreg(func, &defs, slot_lhs)?;
    let base_rhs = slot_base_vreg(func, &defs, slot_rhs)?;
    let base_c = slot_base_vreg(func, &defs, slot_c)?;

    Some(VecPlan {
        iv,
        n_trip,
        base_lhs,
        base_rhs,
        base_c,
        slot_lhs,
        slot_rhs,
        slot_c,
        packed_op,
        preheader,
        header,
    })
}

/// The per-element value written by a recognized fill.
#[derive(Clone, Copy)]
enum FillValue {
    /// A compile-time constant. Only the low `elem_size` bytes are used.
    Const(i64),
    /// A **loop-invariant runtime** value held in an integer (GPR) vreg. Proven
    /// invariant by construction (see `recognize_fill_loop`): the vreg is
    /// single-def and its unique def lies outside the loop body and dominates the
    /// preheader, so it holds a fixed value throughout every execution of the
    /// loop. Only the low `elem_size` bytes are used.
    Invariant(VReg),
}

/// A verified-legal fill (`a[i] = v`, `v` const or loop-invariant) ready to be
/// rewritten to a packed-store loop plus a scalar remainder. Every field is
/// established by construction in `recognize_fill_loop`.
struct FillPlan {
    /// The loop counter vreg (element index; init 0, +1 per scalar iteration).
    iv: VReg,
    /// Compile-time trip count `N` (from the header `iv <u N` test).
    n_trip: i64,
    /// Base-address vreg (`Lea r, [StackSlot(slot_c)]`) of the destination array.
    base_c: VReg,
    /// The (distinct, write-only) destination array's stack slot index.
    slot_c: u32,
    /// The value stored into every element (constant or loop-invariant runtime).
    fill_value: FillValue,
    /// Element size in bytes: 1 (u8, `MovMR8`), 2 (u16, `MovMR16`), or 4 (u32,
    /// `MovMR32`). Determines the packed lane count (`16 / elem_size`) and the
    /// SIB scale of the packed store address.
    elem_size: u8,
    /// The loop's preheader (its terminator is redirected to the vector loop).
    preheader: Block,
    /// The scalar loop header (the vector loop falls into it for the remainder).
    header: Block,
}

/// The element size (bytes) of a covered element store opcode, or `None` if the
/// opcode is not a recognized scalar element store. Only the byte/word/dword
/// integer stores are handled (a 16-byte packed `MOVDQU` fills their lanes).
fn store_elem_size(op: X86Opcode) -> Option<u8> {
    match op {
        X86Opcode::MovMR8 => Some(1),
        X86Opcode::MovMR16 => Some(2),
        X86Opcode::MovMR32 => Some(4),
        _ => None,
    }
}

/// Recognizer for the fill shape:
///
/// ```text
/// let mut a = [_; N]; for i in 0..N { a[i] = v; }   // v const OR loop-invariant
/// ```
///
/// over a **single distinct, write-only** local `[u8/u16/u32; N]` array, where
/// `v` is either a compile-time constant or a **provably loop-invariant runtime
/// value**. Returns a legal `FillPlan`, or `None` for anything else.
///
/// # Legality by construction
///
/// * **No aliasing / no dependence.** The destination base traces to a distinct
///   local `StackSlot(k)` and the loop contains **no loads at all** — every lane
///   `i` writes only `a[i]` and reads nothing, so there is provably no aliasing
///   and no loop-carried dependence. A base that is not a distinct local
///   `StackSlot` (a pointer/reference/slice) is rejected.
/// * **Constant or loop-invariant value.** The stored value must be either:
///   - a `MovRI` immediate reached through copies (the same constant every
///     iteration), or
///   - a **loop-invariant** runtime GPR value. Invariance is established *by
///     construction and fail-safe*: the value's canonical vreg must be
///     **single-def** (never reassigned anywhere in the function), its unique
///     def must lie **outside the loop body**, and that def must **dominate the
///     preheader**. Together these prove the value is computed once, before the
///     loop, and never changes across iterations — so broadcasting it once per
///     loop entry is sound. Anything that fails these checks (a value defined
///     inside the loop, a multi-def value, an IV-dependent value, or one we
///     cannot place relative to the loop) is rejected and stays scalar. A wrong
///     invariance decision would broadcast a stale value — a miscompile — so the
///     checks are strict and the fallback is *do nothing*.
/// * **Unit stride, known trip, in-bounds.** Identical to the element-wise
///   recognizer: `0..N` unit stride, `N` a compile-time constant, the slot is
///   `>= N*elem_size` bytes, and every trapping side-exit is an `iv <u N` bounds
///   check that provably never fires for `iv in [0, N)`.
///
/// The rewrite materializes `[v; lanes]` (`lanes = 16/elem_size`) once into a
/// fresh 16-byte scratch slot with `lanes` covered width-matched integer stores
/// plus one covered `MOVDQU` load, then issues `floor(N/lanes)` covered `MOVDQU`
/// stores; the unchanged scalar loop runs the `N % lanes` remainder. The scratch
/// build lives in a fresh vector-preheader that runs **once per loop entry**, so
/// a loop-invariant `v` that differs across *outer* iterations is re-broadcast
/// correctly each entry. No broadcast/`PSHUFD`/`MOVD` is used, so the transform
/// stays entirely within the proof-covered op set.
fn recognize_fill_loop(
    func: &X86ISelFunction,
    preds: &HashMap<Block, Vec<Block>>,
    // Dominance is no longer consulted for the stored value: invariance is
    // decided by `loop_invariant_vreg` (no def inside the loop), which is both
    // weaker and correct for an inner loop whose outer body re-computes it.
    _idom: &HashMap<Block, Block>,
    lp: &LoopInfo,
) -> Option<FillPlan> {
    let header = lp.header;
    let latch = lp.latch;
    let body = &lp.body;
    let preheader = lp.preheader?;

    // No PHI pseudo anywhere in the loop (non-SSA at this stage).
    for block_id in body {
        let block = func.blocks.get(block_id)?;
        if block.insts.iter().any(|i| i.opcode == X86Opcode::Phi) {
            return None;
        }
    }

    let defs = DefIndex::build(func);
    let mut memo: HashMap<VReg, Prov> = HashMap::new();

    // 1. IV + trip count from the header.
    let (iv, n_trip) = recognize_header(func, &defs, header, body)?;
    if n_trip < LANES {
        return None; // no full vector iteration to gain from.
    }

    // 2. Body chain entry.
    let header_succs = &func.blocks.get(&header)?.successors;
    let body_entry = unique_in_body_succ(header_succs, body)?;

    // 3. Walk the body as a linear chain; every off-chain edge must be a pure
    //    `Ud2` trap guarded by an `iv <u N` bounds compare (same discipline as
    //    the element-wise recognizer — so eliding the guards in the packed body
    //    is sound).
    let mut chain: Vec<Block> = Vec::new();
    let mut visited: HashSet<Block> = HashSet::new();
    let mut cur = body_entry;
    loop {
        if !body.contains(&cur) || !visited.insert(cur) {
            return None;
        }
        chain.push(cur);
        let succs = &func.blocks.get(&cur)?.successors;
        let mut has_trap_edge = false;
        for s in succs {
            if body.contains(s) {
                continue;
            }
            if !is_pure_trap_block(func, *s) {
                return None;
            }
            has_trap_edge = true;
        }
        if has_trap_edge && !block_has_iv_bound_compare(func, &defs, iv, &mut memo, cur, n_trip) {
            return None;
        }
        if cur == latch {
            break;
        }
        let next = unique_in_body_succ(succs, body)?;
        cur = next;
    }
    // The latch's only in-body successor must be the header (the back-edge).
    if unique_in_body_succ(&func.blocks.get(&latch)?.successors, body)? != header {
        return None;
    }
    // Every body block except the header must be on the chain (nothing hidden).
    for block_id in body {
        if *block_id != header && !visited.contains(block_id) {
            return None;
        }
    }
    // The header must have exactly one exit successor and one body successor,
    // and the preheader must be the header's only non-body pred.
    {
        let hsuccs = &func.blocks.get(&header)?.successors;
        let non_body: Vec<Block> = hsuccs
            .iter()
            .copied()
            .filter(|s| !body.contains(s))
            .collect();
        if non_body.len() != 1 {
            return None;
        }
        let empty = Vec::new();
        let hpreds = preds.get(&header).unwrap_or(&empty);
        let non_body_preds: Vec<Block> = hpreds
            .iter()
            .copied()
            .filter(|p| !body.contains(p))
            .collect();
        if non_body_preds != vec![preheader] {
            return None;
        }
    }

    // 4. Collect the memory ops in the chain: exactly ZERO loads and exactly ONE
    //    element store (u8/u16/u32) to a distinct `ElemAddr` slot whose SIB scale
    //    matches the store width; no call, no other memory op.
    let mut store: Option<(u32, VReg, u8)> = None; // (slot, canonical src, elem_size)
    for block_id in &chain {
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            let op = inst.opcode;
            if op == X86Opcode::Call || op == X86Opcode::CallR || op == X86Opcode::CallM {
                return None;
            }
            if is_load_opcode(op) {
                // A fill reads nothing; any load disqualifies it (it is not a
                // pure fill, and a read would reintroduce a dependence question).
                return None;
            } else if is_store_opcode(op) {
                // Only a covered u8/u16/u32 element store; anything else (a wide
                // MovMR, a packed store, a second store) disqualifies.
                let elem_size = store_elem_size(op)?;
                if store.is_some() {
                    return None;
                }
                // The address must be `&slot[iv]` with a SIB scale equal to the
                // store width — proving the index steps exactly one element per
                // `iv` (contiguous, unit stride) for this element size.
                let slot = elem_addr_slot(
                    func,
                    &defs,
                    iv,
                    &mut memo,
                    inst.operands.first(),
                    elem_size as i64,
                )?;
                let src = match inst.operands.get(1) {
                    Some(X86ISelOperand::VReg(s)) => canon(func, &defs, *s),
                    _ => return None,
                };
                store = Some((slot, src, elem_size));
            } else if op == X86Opcode::TrapBoundsCheckExact {
                // Inline proof-only bounds-check carrier: admit only when it
                // provably never traps for iv in [0, n_trip) (index==iv,
                // bound>=n_trip). The packed loop omits it (accesses proven
                // in-slot); the scalar remainder retains it.
                if !is_safe_iv_bounds_carrier(func, &defs, iv, &mut memo, inst, n_trip) {
                    return None;
                }
            } else if !is_whitelisted_body_opcode(op) {
                // Closed world: any unclassified opcode is a potential hidden
                // side effect (or trap) — refuse.
                return None;
            }
        }
    }
    let (slot_c, stored_src, elem_size) = store?;

    // 5. Precise vector-benefit check for this element width: at least one full
    //    packed iteration (`lanes = 16 / elem_size`) must exist.
    let lanes = 16 / elem_size as i64;
    if n_trip < lanes {
        return None;
    }

    // 6. The stored value must be a compile-time constant OR a provably
    //    loop-invariant runtime GPR value.
    let fill_value = if let Some(k) = const_of(func, &defs, stored_src) {
        // Constant: the same value every iteration (unchanged from the original
        // constant-fill recognizer).
        FillValue::Const(k)
    } else {
        // Runtime value: prove loop-invariance BY CONSTRUCTION and FAIL SAFE.
        //  (a) NO def of `stored_src` (already canonicalized through copies) may
        //      lie inside the loop — see `loop_invariant_vreg`. It may have any
        //      number of defs OUTSIDE the loop.
        //  (b) it must be an integer (GPR) value — the broadcast uses covered
        //      integer stores.
        // (a) proves the value is fixed throughout every execution of the loop:
        // the loop's only non-body predecessor is its preheader (established
        // above) and the scratch broadcast is rebuilt once per loop entry, so it
        // observes exactly the value every scalar iteration would read. Any
        // failure → stay scalar (a wrong decision here would broadcast a stale
        // value).
        //
        // This previously demanded a SINGLE def function-wide plus dominance
        // over the preheader. Both are stronger than invariance needs and they
        // reject the common nested case outright — a value computed in an OUTER
        // loop (`v2_memfill`'s `v = (r as u8) | 1`) has a def that neither is
        // unique nor dominates, yet is perfectly invariant for the inner loop,
        // which is re-entered after each outer update. Same defect, same fix as
        // the saxpy `k`; that one was worth 8.75x -> 1.97x.
        if !loop_invariant_vreg(func, stored_src, body) {
            return None; // (a)
        }
        if !matches!(stored_src.class, RegClass::Gpr32 | RegClass::Gpr64) {
            return None; // (b)
        }
        FillValue::Invariant(stored_src)
    };

    // 7. In-slot: the destination holds >= N elements of `elem_size` bytes, so
    //    the packed stores over byte range [0, floor(N/lanes)*lanes*elem_size)
    //    stay strictly in-slot.
    let need_bytes = n_trip.checked_mul(elem_size as i64)?;
    let info = func.stack_slots.get(slot_c as usize)?;
    if (info.size as i64) < need_bytes {
        return None;
    }

    // 8. Resolve the destination slot back to its base-address vreg.
    let base_c = slot_base_vreg(func, &defs, slot_c)?;

    Some(FillPlan {
        iv,
        n_trip,
        base_c,
        slot_c,
        fill_value,
        elem_size,
        preheader,
        header,
    })
}

/// A verified-legal RUNTIME-count byte fill through a loop-invariant pointer,
/// ready to be rewritten to a guarded packed loop plus the unchanged scalar
/// remainder. Established by construction in `recognize_runtime_byte_fill_loop`.
struct RuntimeByteFillPlan {
    /// The loop counter vreg (byte index; init 0, +1 per scalar iteration).
    iv: VReg,
    /// The RUNTIME trip-count vreg (canonical): loop-invariant, single-def
    /// outside the loop, def dominates the preheader.
    n: VReg,
    /// The canonical base-pointer vreg: loop-invariant like `n`. NOT required
    /// to trace to a stack slot — see the soundness argument on the recognizer.
    base: VReg,
    /// The canonical stored-value vreg (its low byte is what the scalar
    /// `MovMR8` stores): loop-invariant like `n`.
    src: VReg,
    /// The loop's preheader (must end `Jmp header`; redirected to the guard).
    preheader: Block,
    /// The scalar loop header (the vector loop falls into it for the tail).
    header: Block,
}

/// Recognizer for the RUNTIME-count invariant-pointer byte-fill shape — the
/// loop the bridge's `__trustcg_array_fill_i8` helper is built from:
///
/// ```text
/// i = 0; while i <s n { *(base + i) = v; i += 1; }   // n, base, v invariant
/// ```
///
/// Returns a legal `RuntimeByteFillPlan`, or `None` for anything else.
///
/// # Legality by construction (why NO base provenance is needed)
///
/// Unlike `recognize_fill_loop` (compile-time `N`, `StackSlot` base — in-bounds
/// proven against the slot size), this slice proves in-bounds by SUBSETTING the
/// scalar loop's own store set:
///
/// * **The scalar loop's semantics define the writable range.** The loop body
///   is a single `MovMR8` at `base + iv` (verified: exactly one store, ZERO
///   loads, no calls, no off-chain edges, every opcode whitelisted-pure), and
///   the counter walks `0, 1, …` while `iv <s n` — so the scalar loop stores
///   the low byte of `v` to every address in `[base, base + n)` exactly.
/// * **The packed loop stores a SUBSET of those addresses.** The vector body
///   runs only while `iv <= n - 16` (guarded by a runtime `n >= 16` entry
///   check, so `n - 15` cannot wrap), and writes exactly the 16 bytes
///   `[base + iv, base + iv + 16)` — every one at an offset `< n`, i.e. an
///   address the scalar loop itself writes. It writes the SAME byte (the
///   broadcast low byte of the same invariant `v`) — so memory after
///   vector-prefix + scalar-tail is byte-for-byte identical to scalar-only.
///   Whatever memory `base` points to (stack slot, heap, caller pointer), the
///   ORIGINAL loop already writes it; the packed loop introduces no new
///   addresses. There is no aliasing question: the loop reads nothing.
/// * **Register state is preserved.** The transform writes only fresh vregs
///   plus `iv`; the scalar loop exits with `iv == n` under unit stepping from
///   any intermediate value `<= n`, identical to the untransformed exit state,
///   and every flag consumer in the (strictly matched) header is dominated by
///   the header's own compare.
/// * **Invariance of `n` / `base` / `v`** is established exactly as
///   `recognize_fill_loop`'s runtime-value case: canonical vreg single-def,
///   def outside the loop body, def-block dominates the preheader; fail-safe
///   (anything else stays scalar).
/// * **Exact trip semantics.** The header is matched STRICTLY — `CmpRR(iv, n)`
///   followed by either `Jcc L` directly or the ISel bool materialization
///   `Setcc L / Movzx* / AndRI ,1 / CmpRI ,0 / Jcc NE` and a trailing
///   `Jmp exit`, with nothing else in the block — so the loop provably runs
///   iff `iv <s n` (a `!=`-style loop or reversed compare does not match, and
///   its divergent-for-negative-`n` semantics can never be admitted).
///
/// The rewrite (see `apply_runtime_byte_fill_plan`) inserts, in front of the
/// untouched scalar loop: a guard block (`n < 16` → scalar), a vector
/// preheader broadcasting the low byte of `v` into a fresh 16-byte scratch
/// slot (the same covered `MovMR8` x16 + `MOVDQU` mechanism as
/// `apply_fill_plan` — no new opcode shapes), and a `MOVDQU`-store loop
/// stepping `iv` by 16 while `iv <s n - 15`.
fn recognize_runtime_byte_fill_loop(
    func: &X86ISelFunction,
    preds: &HashMap<Block, Vec<Block>>,
    // Dominance is no longer consulted: invariance is decided by
    // `loop_invariant_vreg` (no def inside the loop), which is weaker and
    // correct for a loop whose enclosing scope re-copies the value.
    _idom: &HashMap<Block, Block>,
    lp: &LoopInfo,
) -> Option<RuntimeByteFillPlan> {
    let header = lp.header;
    let latch = lp.latch;
    let body = &lp.body;
    let preheader = lp.preheader?;

    // No PHI pseudo anywhere in the loop (non-SSA at this stage).
    for block_id in body {
        let block = func.blocks.get(block_id)?;
        if block.insts.iter().any(|i| i.opcode == X86Opcode::Phi) {
            return None;
        }
    }

    let defs = DefIndex::build(func);

    // Loop-invariance discipline shared by `n` / `base` / `src`: the canonical
    // vreg has NO def inside the loop (see `loop_invariant_vreg`), so its value
    // is fixed for the whole loop execution and the vector preheader — placed on
    // the preheader -> loop edge — reads exactly what every scalar iteration
    // would.
    //
    // This previously required a SINGLE def function-wide plus dominance over
    // the preheader. Both are stronger than invariance needs and reject the
    // ordinary nested shape where an enclosing loop re-copies the value; the
    // same over-conservatism kept `v1_saxpy` scalar at 8.75x of LLVM.
    let invariant_gpr = |v: VReg| -> Option<VReg> {
        let c = canon(func, &defs, v);
        if !loop_invariant_vreg(func, c, body) {
            return None;
        }
        if !matches!(c.class, RegClass::Gpr32 | RegClass::Gpr64) {
            return None;
        }
        Some(c)
    };

    // 1. STRICT header match: `CmpRR(iv, n)` then either a direct `Jcc L` or
    //    the materialized-bool chain, then `Jmp exit` — and NOTHING else. The
    //    match is positional so no unmodeled instruction can hide in between.
    let hblock = func.blocks.get(&header)?;
    let insts = &hblock.insts;
    let mut pos = 0usize;
    let (cmp_a, cmp_b) = match insts.first() {
        Some(i) if i.opcode == X86Opcode::CmpRR => match (i.operands.first(), i.operands.get(1)) {
            (Some(X86ISelOperand::VReg(a)), Some(X86ISelOperand::VReg(b))) => (*a, *b),
            _ => return None,
        },
        _ => return None,
    };
    pos += 1;
    // Either `Jcc L` directly…
    let body_target;
    match insts.get(pos) {
        Some(i)
            if i.opcode == X86Opcode::Jcc
                && matches!(
                    i.operands.first(),
                    Some(X86ISelOperand::CondCode(X86CondCode::L))
                ) =>
        {
            body_target = match i.operands.get(1) {
                Some(X86ISelOperand::Block(t)) => *t,
                _ => return None,
            };
            pos += 1;
        }
        // …or the ISel bool materialization: `Setcc L` into a bool vreg,
        // any number of `Movzx` copies of it, an optional `AndRI x, x, 1`
        // (identity on a 0/1 bool), a `CmpRI x, 0`, and `Jcc NE`.
        _ => {
            let bool_v = match insts.get(pos) {
                Some(i)
                    if i.opcode == X86Opcode::Setcc
                        && matches!(
                            i.operands.get(1),
                            Some(X86ISelOperand::CondCode(X86CondCode::L))
                        ) =>
                {
                    match i.operands.first() {
                        Some(X86ISelOperand::VReg(v)) => *v,
                        _ => return None,
                    }
                }
                _ => return None,
            };
            pos += 1;
            let mut cur = bool_v;
            loop {
                match insts.get(pos) {
                    Some(i)
                        if i.opcode == X86Opcode::Movzx
                            && matches!(
                                i.operands.get(1),
                                Some(X86ISelOperand::VReg(s)) if *s == cur
                            ) =>
                    {
                        cur = match i.operands.first() {
                            Some(X86ISelOperand::VReg(d)) => *d,
                            _ => return None,
                        };
                        pos += 1;
                    }
                    Some(i)
                        if i.opcode == X86Opcode::AndRI
                            && matches!(
                                i.operands.first(),
                                Some(X86ISelOperand::VReg(d)) if *d == cur
                            )
                            && matches!(
                                i.operands.get(1),
                                Some(X86ISelOperand::VReg(s)) if *s == cur
                            )
                            && matches!(i.operands.get(2), Some(X86ISelOperand::Imm(1))) =>
                    {
                        pos += 1;
                    }
                    _ => break,
                }
            }
            match insts.get(pos) {
                Some(i)
                    if i.opcode == X86Opcode::CmpRI
                        && matches!(
                            i.operands.first(),
                            Some(X86ISelOperand::VReg(v)) if *v == cur
                        )
                        && matches!(i.operands.get(1), Some(X86ISelOperand::Imm(0))) =>
                {
                    pos += 1;
                }
                _ => return None,
            }
            body_target = match insts.get(pos) {
                Some(i)
                    if i.opcode == X86Opcode::Jcc
                        && matches!(
                            i.operands.first(),
                            Some(X86ISelOperand::CondCode(X86CondCode::NE))
                        ) =>
                {
                    match i.operands.get(1) {
                        Some(X86ISelOperand::Block(t)) => *t,
                        _ => return None,
                    }
                }
                _ => return None,
            };
            pos += 1;
        }
    }
    // Trailing `Jmp exit`, and nothing after it.
    let exit_target = match insts.get(pos) {
        Some(i) if i.opcode == X86Opcode::Jmp => match i.operands.first() {
            Some(X86ISelOperand::Block(t)) => *t,
            _ => return None,
        },
        _ => return None,
    };
    if insts.len() != pos + 1 {
        return None;
    }
    if !body.contains(&body_target) || body.contains(&exit_target) {
        return None;
    }

    // 2. Operand roles: `cmp_a` is the unit counter, `cmp_b` the runtime bound
    //    (this exact order — `iv <s n`; a reversed compare does not match).
    let iv = canon(func, &defs, cmp_a);
    if !is_counter(func, &defs, iv, body) {
        return None;
    }
    if const_of(func, &defs, cmp_b).is_some() {
        return None; // compile-time N: recognize_fill_loop's territory.
    }
    let n = invariant_gpr(cmp_b)?;
    if !matches!(n.class, RegClass::Gpr64) {
        return None;
    }

    // 3. The header must have exactly the two successors matched above, its
    //    only non-body predecessor must be the preheader, and the preheader
    //    must end with an unconditional `Jmp header` (so the redirect in the
    //    apply step is total).
    if hblock.successors.len() != 2 {
        return None;
    }
    {
        let empty = Vec::new();
        let hpreds = preds.get(&header).unwrap_or(&empty);
        let non_body_preds: Vec<Block> = hpreds
            .iter()
            .copied()
            .filter(|p| !body.contains(p))
            .collect();
        if non_body_preds != vec![preheader] {
            return None;
        }
        let pre = func.blocks.get(&preheader)?;
        match pre.insts.last() {
            Some(i)
                if i.opcode == X86Opcode::Jmp
                    && matches!(
                        i.operands.first(),
                        Some(X86ISelOperand::Block(t)) if *t == header
                    ) => {}
            _ => return None,
        }
    }

    // 4. Walk the body as a linear chain from the header's body successor to
    //    the latch. NO off-chain edges at all (stricter than the trap-tolerant
    //    walks: this loop has no bounds checks to tolerate).
    let mut chain: Vec<Block> = Vec::new();
    let mut visited: HashSet<Block> = HashSet::new();
    let mut cur = body_target;
    loop {
        if !body.contains(&cur) || !visited.insert(cur) {
            return None;
        }
        chain.push(cur);
        let succs = &func.blocks.get(&cur)?.successors;
        if succs.iter().any(|s| !body.contains(s)) {
            return None;
        }
        if cur == latch {
            break;
        }
        cur = unique_in_body_succ(succs, body)?;
    }
    if unique_in_body_succ(&func.blocks.get(&latch)?.successors, body)? != header {
        return None;
    }
    for block_id in body {
        if *block_id != header && !visited.contains(block_id) {
            return None;
        }
    }

    // 5. Scan the chain: exactly ONE `MovMR8` store, ZERO loads, no calls, no
    //    other memory op, every other opcode whitelisted-pure.
    let mut store: Option<(VReg, VReg)> = None; // (addr vreg, src vreg)
    for block_id in &chain {
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            let op = inst.opcode;
            if op == X86Opcode::Call || op == X86Opcode::CallR || op == X86Opcode::CallM {
                return None;
            }
            if is_load_opcode(op) {
                return None;
            } else if is_store_opcode(op) {
                if op != X86Opcode::MovMR8 || store.is_some() {
                    return None;
                }
                let addr = match inst.operands.first() {
                    Some(X86ISelOperand::MemAddr { base, disp: 0 }) => match &**base {
                        X86ISelOperand::VReg(v) => *v,
                        _ => return None,
                    },
                    _ => return None,
                };
                let src = match inst.operands.get(1) {
                    Some(X86ISelOperand::VReg(s)) => *s,
                    _ => return None,
                };
                store = Some((addr, src));
            } else if !is_whitelisted_body_opcode(op) {
                return None;
            }
        }
    }
    let (addr_v, src_v) = store?;

    // 6. The store address must be exactly `base + iv` (`AddRR` of the counter
    //    — possibly through `iv * 1` — and an invariant base), disp 0.
    let addr_c = canon(func, &defs, addr_v);
    let add_inst = defs.def_inst(func, addr_c)?;
    if add_inst.opcode != X86Opcode::AddRR {
        return None;
    }
    let (x, y) = match (add_inst.operands.get(1), add_inst.operands.get(2)) {
        (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => (*x, *y),
        _ => return None,
    };
    // One side is the counter (directly, or via `ImulRR(iv, 1)` in either
    // operand order); the other is the invariant base.
    let is_iv_index = |v: VReg| -> bool {
        let c = canon(func, &defs, v);
        if c == iv {
            return true;
        }
        let Some(inst) = defs.def_inst(func, c) else {
            return false;
        };
        if inst.opcode != X86Opcode::ImulRR {
            return false;
        }
        match (inst.operands.get(1), inst.operands.get(2)) {
            (Some(X86ISelOperand::VReg(a)), Some(X86ISelOperand::VReg(b))) => {
                (canon(func, &defs, *a) == iv && const_of(func, &defs, *b) == Some(1))
                    || (canon(func, &defs, *b) == iv && const_of(func, &defs, *a) == Some(1))
            }
            _ => false,
        }
    };
    let base_cand = if is_iv_index(x) {
        y
    } else if is_iv_index(y) {
        x
    } else {
        return None;
    };
    let base = invariant_gpr(base_cand)?;
    if !matches!(base.class, RegClass::Gpr64) {
        return None;
    }
    if canon(func, &defs, base_cand) == iv {
        return None; // degenerate `iv + iv` — not a fill address.
    }

    // 7. The stored value must be loop-invariant (its low byte is broadcast).
    let src = invariant_gpr(src_v)?;

    Some(RuntimeByteFillPlan {
        iv,
        n,
        base,
        src,
        preheader,
        header,
    })
}

/// A verified-legal saxpy / element-wise FMA map ready to be rewritten to a
/// packed loop plus a scalar remainder. Established by construction in
/// `recognize_saxpy_loop`:
///
/// ```text
/// for i in 0..N { dest[i] = (k * x[i]) (+|-) y[i]; }   // k loop-invariant / const
/// ```
///
/// over local i32 arrays, where — unlike the element-wise recognizer — the
/// destination slot **may equal a source slot** (`dest == x` or `dest == y`),
/// because every classified access is *same-index* (`&slot[iv]`, disp 0).
struct SaxpyPlan {
    /// The loop counter vreg (element index; init 0, +1 per scalar iteration).
    iv: VReg,
    /// Compile-time trip count `N` (from the header `iv <u N` test).
    n_trip: i64,
    /// Base-address vreg of the multiplied source array `x` (`k * x[i]`).
    base_x: VReg,
    /// Base-address vreg of the added source array `y` (`… (+|-) y[i]`).
    base_add: VReg,
    /// Base-address vreg of the destination array (may equal `base_x`/`base_add`).
    base_c: VReg,
    /// The (possibly-coinciding) slot indices for x, the add-source, and dest.
    slot_x: u32,
    slot_add: u32,
    slot_c: u32,
    /// The loop-invariant (or constant) scalar factor `k`, broadcast to `[k;4]`.
    k: FillValue,
    /// Packed combine op emitted after the multiply: `Paddd` (for `+`) or
    /// `Psubd` (for `-`).
    packed_op: X86Opcode,
    /// Operand order for the (order-sensitive) subtract: `true` means the scalar
    /// op was `(k*x) OP y` (mul first); `false` means `y OP (k*x)` (mul second).
    /// For `Paddd` the order is irrelevant but is preserved anyway.
    mul_is_first: bool,
    /// The loop's preheader (its terminator is redirected to the vector loop).
    preheader: Block,
    /// The scalar loop header (the vector loop falls into it for the remainder).
    header: Block,
}

/// Recognizer for the saxpy / element-wise FMA shape:
///
/// ```text
/// for i in 0..N { dest[i] = (k * x[i]) (+|-) y[i]; }   // k loop-invariant / const
/// ```
///
/// (and the commuted `y (+|-) k*x` / `x*k` forms) over local i32 arrays. Returns
/// a legal `SaxpyPlan`, or `None` for anything else.
///
/// # Legality by construction (incl. the `dest == source` relaxation)
///
/// The header / body-chain / trap / unit-stride / in-bounds discipline is
/// **identical** to `recognize_elementwise_loop` (see that function and the
/// module docs). The two additions specific to saxpy are:
///
/// * **`k` is a compile-time constant or a provably loop-invariant runtime GPR
///   value.** Invariance is established exactly as in `recognize_fill_loop`
///   (single-def, def outside the loop body, def dominates the preheader, integer
///   class) and is fail-safe: a value that is recomputed per iteration, IV-
///   dependent, or that we cannot place relative to the loop is rejected and the
///   loop stays scalar. `k` is broadcast to `[k;4]` once per loop entry via the
///   proof-covered scratch-slot mechanism (no `PSHUFD`/`MOVD`), and the packed
///   `PMULLD` computes the low 32 bits per lane — bit-for-bit the scalar i32
///   `wrapping_mul`.
/// * **`dest` may equal a source slot, restricted to *same-index* access.** The
///   element-wise recognizer required three *distinct* slots to rule out
///   aliasing. That is stronger than necessary: the real requirement is that
///   every access to the destination slot is at *exactly* the IV index. This is
///   **guaranteed by construction** here because *every* load and the store is
///   classified only through `elem_addr_slot`, which admits an address **iff**
///   its provenance is `ElemAddr(slot, ELEM_SIZE)` with `disp == 0` — i.e. it is
///   literally `&slot[iv]`. There is no way for an access at a *different* index
///   or a non-zero displacement (`dest[i-1]`, `x[i+1]`, `&slot[iv]+k`) to pass
///   classification: such an address has non-`Iv` index provenance (e.g. `iv-1`
///   is `Unknown`) or a non-zero `disp`, so `elem_addr_slot` returns `None` and
///   the whole recognizer bails (`?`), leaving the loop scalar. Therefore, with
///   *all* accesses pinned to index `iv`, allowing `slot_c == slot_x` or
///   `slot_c == slot_add` introduces **no cross-element dependence**: each packed
///   window `[iv, iv+4)` reads and writes only that window (loads precede the
///   store), disjoint from every other window (unit stride, `iv += 4`), so the
///   packed result is lane-for-lane identical to the scalar loop. A wrong
///   relaxation (admitting a cross-element `dest` access) is impossible to reach
///   because that access would never classify — the fail-safe is *do nothing*.
///
/// Distinct local `StackSlot`s are disjoint frame regions; two accesses to the
/// *same* slot at the *same* index `iv` are the same location. Either way there
/// is no partial overlap, so same-index `dest == source` is sound.
fn recognize_saxpy_loop(
    func: &X86ISelFunction,
    preds: &HashMap<Block, Vec<Block>>,
    // Dominance is no longer consulted for `k`: invariance is decided by
    // `loop_invariant_vreg` (no def inside the loop), which is both weaker and
    // correct for a nested loop whose outer body legitimately re-defines `k`.
    _idom: &HashMap<Block, Block>,
    lp: &LoopInfo,
) -> Option<SaxpyPlan> {
    let header = lp.header;
    let latch = lp.latch;
    let body = &lp.body;
    let preheader = lp.preheader?;

    // No PHI pseudo anywhere in the loop (non-SSA at this stage).
    for block_id in body {
        let block = func.blocks.get(block_id)?;
        if block.insts.iter().any(|i| i.opcode == X86Opcode::Phi) {
            return None;
        }
    }

    let defs = DefIndex::build(func);
    let mut memo: HashMap<VReg, Prov> = HashMap::new();

    // 1. IV + trip count from the header.
    let (iv, n_trip) = recognize_header(func, &defs, header, body)?;
    if n_trip < LANES {
        return None; // no full vector iteration to gain from.
    }

    // 2. Body chain entry.
    let header_succs = &func.blocks.get(&header)?.successors;
    let body_entry = unique_in_body_succ(header_succs, body)?;

    // 3. Walk the body as a linear chain; every off-chain edge must be a pure
    //    `Ud2` trap guarded by an `iv <u N` bounds compare (identical discipline
    //    to the element-wise / fill recognizers).
    let mut chain: Vec<Block> = Vec::new();
    let mut visited: HashSet<Block> = HashSet::new();
    let mut cur = body_entry;
    loop {
        if !body.contains(&cur) || !visited.insert(cur) {
            return None;
        }
        chain.push(cur);
        let succs = &func.blocks.get(&cur)?.successors;
        let mut has_trap_edge = false;
        for s in succs {
            if body.contains(s) {
                continue;
            }
            if !is_pure_trap_block(func, *s) {
                return None;
            }
            has_trap_edge = true;
        }
        if has_trap_edge && !block_has_iv_bound_compare(func, &defs, iv, &mut memo, cur, n_trip) {
            return None;
        }
        if cur == latch {
            break;
        }
        let next = unique_in_body_succ(succs, body)?;
        cur = next;
    }
    // The latch's only in-body successor must be the header (the back-edge).
    if unique_in_body_succ(&func.blocks.get(&latch)?.successors, body)? != header {
        return None;
    }
    // Every body block except the header must be on the chain (nothing hidden).
    for block_id in body {
        if *block_id != header && !visited.contains(block_id) {
            return None;
        }
    }
    // The header must have exactly one exit successor and one body successor, and
    // the preheader must be the header's only non-body pred.
    {
        let hsuccs = &func.blocks.get(&header)?.successors;
        let non_body: Vec<Block> = hsuccs
            .iter()
            .copied()
            .filter(|s| !body.contains(s))
            .collect();
        if non_body.len() != 1 {
            return None;
        }
        let empty = Vec::new();
        let hpreds = preds.get(&header).unwrap_or(&empty);
        let non_body_preds: Vec<Block> = hpreds
            .iter()
            .copied()
            .filter(|p| !body.contains(p))
            .collect();
        if non_body_preds != vec![preheader] {
            return None;
        }
    }

    if std::env::var_os("TCG_TRACE_VECTORIZE_PROV").is_some() {
        eprintln!("x86-vectorize[saxpy]: stage structure-ok");
    }
    // 4. Collect the memory ops in the chain. Each load/store is admitted only if
    //    its address classifies as `&slot[iv]` (`ElemAddr(slot, ELEM_SIZE)`,
    //    disp 0) — this is what pins EVERY access to the same index `iv` and makes
    //    the `dest == source` relaxation safe by construction. i32 only.
    let mut loads: Vec<(VReg, u32)> = Vec::new(); // (canonical dst, slot)
    let mut store: Option<(u32, VReg)> = None; // (slot, canonical stored src)
    for block_id in &chain {
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            let op = inst.opcode;
            if op == X86Opcode::Call || op == X86Opcode::CallR || op == X86Opcode::CallM {
                return None;
            }
            if is_load_opcode(op) {
                if op != X86Opcode::MovRM32 {
                    return None;
                }
                let dst = match inst.operands.first() {
                    Some(X86ISelOperand::VReg(d)) => *d,
                    _ => return None,
                };
                let slot = elem_addr_slot(
                    func,
                    &defs,
                    iv,
                    &mut memo,
                    inst.operands.get(1),
                    ELEM_SIZE as i64,
                )?;
                loads.push((canon(func, &defs, dst), slot));
            } else if is_store_opcode(op) {
                if op != X86Opcode::MovMR32 || store.is_some() {
                    return None;
                }
                let slot = elem_addr_slot(
                    func,
                    &defs,
                    iv,
                    &mut memo,
                    inst.operands.first(),
                    ELEM_SIZE as i64,
                )?;
                let src = match inst.operands.get(1) {
                    Some(X86ISelOperand::VReg(s)) => canon(func, &defs, *s),
                    _ => return None,
                };
                store = Some((slot, src));
            } else if op == X86Opcode::TrapBoundsCheckExact {
                // Inline proof-only bounds-check carrier: admit only when it
                // provably never traps for iv in [0, n_trip) (index==iv,
                // bound>=n_trip). The packed loop omits it (accesses proven
                // in-slot); the scalar remainder retains it.
                if !is_safe_iv_bounds_carrier(func, &defs, iv, &mut memo, inst, n_trip) {
                    return None;
                }
            } else if !is_whitelisted_body_opcode(op) {
                // Closed world: any unclassified opcode is a potential hidden side
                // effect (or trap) — refuse.
                return None;
            }
        }
    }
    let (slot_c, stored_src) = store?;
    // A saxpy has two element loads (the mul source and the add source); a
    // same-array CSE could produce one. More than two means a shape we do not
    // account for.
    if loads.is_empty() || loads.len() > 2 {
        return None;
    }

    let slot_of = |v: VReg| -> Option<u32> { loads.iter().find(|(d, _)| *d == v).map(|(_, s)| *s) };
    let is_mul = |v: VReg| -> bool {
        defs.def_inst(func, v)
            .map(|i| i.opcode == X86Opcode::ImulRR)
            .unwrap_or(false)
    };

    if std::env::var_os("TCG_TRACE_VECTORIZE_PROV").is_some() {
        eprintln!("x86-vectorize[saxpy]: stage loads-collected");
    }
    // 5. The stored value is `top(A, B)` where `top` is a plain i32 `AddRR`/
    //    `SubRR`, exactly one of {A, B} is an `ImulRR` (the `k*x` term) and the
    //    other is a plain loaded source (the `y` term).
    let top = defs.def_inst(func, stored_src)?;
    let packed_op = match top.opcode {
        X86Opcode::AddRR => X86Opcode::Paddd,
        X86Opcode::SubRR => X86Opcode::Psubd,
        _ => return None,
    };
    let (ta, tb) = match (top.operands.get(1), top.operands.get(2)) {
        (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => {
            (canon(func, &defs, *x), canon(func, &defs, *y))
        }
        _ => return None,
    };
    let (mul_term, add_term, mul_is_first) = if is_mul(ta) && slot_of(tb).is_some() {
        (ta, tb, true)
    } else if slot_of(ta).is_some() && is_mul(tb) {
        (tb, ta, false)
    } else {
        return None;
    };
    let slot_add = slot_of(add_term)?;

    if std::env::var_os("TCG_TRACE_VECTORIZE_PROV").is_some() {
        eprintln!("x86-vectorize[saxpy]: stage top-matched");
    }
    // 6. The mul term is `ImulRR(load_x, k)` (either operand order): one operand a
    //    loaded source, the other the scalar factor `k`.
    let mul = defs.def_inst(func, mul_term)?;
    let (ma, mb) = match (mul.operands.get(1), mul.operands.get(2)) {
        (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => {
            (canon(func, &defs, *x), canon(func, &defs, *y))
        }
        _ => return None,
    };
    let (mul_load, k_reg) = if slot_of(ma).is_some() {
        (ma, mb)
    } else if slot_of(mb).is_some() {
        (mb, ma)
    } else {
        return None;
    };
    let slot_x = slot_of(mul_load)?;

    // Closed world over loads: every collected load must be one of the two we
    // consumed (the mul source or the add source) — no stray/dead loads.
    for (v, _) in &loads {
        if *v != mul_load && *v != add_term {
            return None;
        }
    }

    if std::env::var_os("TCG_TRACE_VECTORIZE_PROV").is_some() {
        eprintln!("x86-vectorize[saxpy]: stage mul-matched");
    }
    // 7. `k` must be a compile-time constant OR a provably loop-invariant runtime
    //    GPR value (identical construction + fail-safe as `recognize_fill_loop`).
    let k = if let Some(kc) = const_of(func, &defs, k_reg) {
        FillValue::Const(kc)
    } else {
        // `k` is invariant w.r.t. THIS loop iff no def of it lies inside the
        // loop — see `loop_invariant_vreg`. The former rule demanded a SINGLE
        // def function-wide plus dominance over the preheader, which rejected
        // every invariant whose enclosing loop re-copies it (saxpy's `k` has two
        // outside defs, both `MovRR32`), leaving an 8.75x-of-LLVM loop scalar.
        if !loop_invariant_vreg(func, k_reg, body) {
            return None;
        }
        if !matches!(k_reg.class, RegClass::Gpr32 | RegClass::Gpr64) {
            return None; // broadcast uses covered integer stores
        }
        FillValue::Invariant(k_reg)
    };

    if std::env::var_os("TCG_TRACE_VECTORIZE_PROV").is_some() {
        eprintln!("x86-vectorize[saxpy]: stage k-classified");
    }
    // 8. Each involved slot must hold >= N i32 elements so the packed accesses over
    //    indices [0, floor(N/4)*4) stay strictly in-slot.
    let need_bytes = n_trip.checked_mul(ELEM_SIZE as i64)?;
    for slot in [slot_x, slot_add, slot_c] {
        let info = func.stack_slots.get(slot as usize)?;
        if (info.size as i64) < need_bytes {
            return None;
        }
    }

    // 9. Resolve each slot back to its base-address vreg. Coinciding slots resolve
    //    to the same base vreg (a slot has a unique `Lea` base).
    let base_x = slot_base_vreg(func, &defs, slot_x)?;
    let base_add = slot_base_vreg(func, &defs, slot_add)?;
    let base_c = slot_base_vreg(func, &defs, slot_c)?;

    Some(SaxpyPlan {
        iv,
        n_trip,
        base_x,
        base_add,
        base_c,
        slot_x,
        slot_add,
        slot_c,
        k,
        packed_op,
        mul_is_first,
        preheader,
        header,
    })
}

/// A verified-legal i64 saxpy-ACCUMULATE at a loop-invariant flat offset
/// (matmul's inner loop) ready to be rewritten to a packed loop guarded by
/// runtime bound checks + the unchanged scalar loop. Every field is
/// established by construction in `recognize_saxpyq_loop`.
///
/// # The recognized shape (post-ISel, raw)
///
/// ```text
/// for j in 0..N {                                   // iv <u N, N const
///     c[LC*MC + j] = c[LC*MC + j] + K * x[LX*MX + j];   // all i64
/// }
/// ```
///
/// where `LC`/`LX` are vregs with NO def inside the loop body (checked), `MC`/
/// `MX` compile-time constants, `K` a loop-invariant i64 vreg, and every
/// bounds-check guard in the body compares a classified flat index
/// (`leaf*m + iv`) against a compile-time bound `B` (collected into
/// `obligations`).
///
/// # Legality by construction
///
/// * **Runtime in-bounds, fail-safe.** The packed loop is entered ONLY after
///   per-obligation preheader checks `inv <u B - (N-1)` (with
///   `inv = leaf*m` recomputed by the same wrapping IMUL the scalar body
///   uses). A passing check proves `inv + j < B` for every `j in [0, N)`
///   WITHOUT wraparound, so (a) every elided scalar guard would provably not
///   have fired, and (b) with the compile-time check `B*8 <= slot_size` every
///   packed access stays strictly in-slot. A failing check branches to the
///   UNCHANGED scalar loop — never wrong, never fail-closed.
/// * **No loop-carried dependence.** Every access uses the SAME flat index
///   `inv + j` in iteration `j` (the store's index expression is required to
///   be structurally identical — same canonical leaf, same multiplier, same
///   slot — to the accumulate-load's). Distinct iterations touch distinct
///   elements (`inv + j` is strictly increasing, no wrap after the runtime
///   check), so the only dependence is the read-before-write within one
///   iteration, which the packed body preserves (load c, add, store c).
/// * **Distinct or same-index sources.** The multiply-source slot is either a
///   different stack slot from the destination (disjoint frame regions) or the
///   same slot at the SAME flat index (read-before-write per iteration).
/// * **Exact 64-bit lane math.** The packed multiply is the standard SSE2
///   compose `lo64(k*b) = PMULUDQ(k,b) + ((PMULUDQ(k, b>>32) + PMULUDQ(k>>32,
///   b)) << 32)` — bit-for-bit the scalar wrapping IMUL (all ops mod 2^64) —
///   and PADDQ is the wrapping 64-bit lane add. Every emitted packed op
///   (MOVDQU, PMULUDQ, PSLLQ, PSRLQ, PADDQ) is proof-covered.
struct SaxpyQPlan {
    /// The loop counter vreg (element index; init 0, +1 per scalar iteration).
    iv: VReg,
    /// Compile-time trip count `N` (from the header `iv <u N` test).
    n_trip: i64,
    /// Base-address vreg + slot of the multiply-source array `x`.
    base_x: VReg,
    slot_x: u32,
    /// Base-address vreg + slot of the accumulate destination array `c`.
    base_c: VReg,
    slot_c: u32,
    /// The invariant flat-offset expression of `x`: `leaf_x * mult_x`.
    leaf_x: VReg,
    mult_x: i64,
    /// The invariant flat-offset expression of `c`: `leaf_c * mult_c`.
    leaf_c: VReg,
    mult_c: i64,
    /// The loop-invariant i64 multiplier vreg `K` (single-def, def outside the
    /// body, dominates the preheader).
    k: VReg,
    /// Operand order of the scalar accumulate add (`c + k*x` vs `k*x + c`).
    /// PADDQ commutes so this is order-preserving cosmetics, kept for exactness.
    mul_is_first: bool,
    /// Deduplicated runtime bound obligations `(leaf, mult, bound)`: the
    /// vector preheader checks `leaf*mult <u bound - (n_trip - 1)` for each,
    /// branching to the scalar header on failure.
    obligations: Vec<(VReg, i64, i64)>,
    /// The loop's preheader (its terminator is redirected to the vector CFG).
    preheader: Block,
    /// The scalar loop header (runtime-check failure and the remainder both
    /// enter here).
    header: Block,
}

/// How a body block's bounds-check guard is justified for packed elision.
#[derive(Clone, Copy, PartialEq, Eq)]
enum GuardClass {
    /// `iv <u c` with `c >= n_trip` — statically never fires.
    StaticOk,
    /// `(leaf*mult + iv) <u bound` — never fires IF the runtime obligation
    /// `leaf*mult <u bound - (n_trip-1)` holds (checked in the vector
    /// preheader; failure falls back to the scalar loop).
    Inv(VReg, i64, i64),
}

/// Classify a guard block's bounds compare for the saxpy-Q recognizer.
///
/// Returns the guard classification, or `None` when nothing in the block is a
/// recognizable in-bounds compare (⇒ the caller must reject the loop).
/// In addition to the compare itself this REQUIRES the block's exact
/// guard-diamond terminator shape (stricter than `block_has_iv_bound_compare`):
/// a `Setcc B` materializing the compare, then `Jcc NE -> in-body successor`
/// followed by `Jmp -> off-chain trap block` — pinning the polarity "continue
/// iff the index is in range".
fn classify_guard_compare(
    func: &X86ISelFunction,
    defs: &DefIndex,
    iv: VReg,
    memo: &mut HashMap<VReg, Prov>,
    block_id: Block,
    body: &BTreeSet<Block>,
    n_trip: i64,
) -> Option<GuardClass> {
    let block = func.blocks.get(&block_id)?;
    let n = block.insts.len();
    if n < 2 {
        return None;
    }
    // Terminator shape: Jcc(NE, in-body) then Jmp(off-chain trap).
    let jcc = &block.insts[n - 2];
    let jmp = &block.insts[n - 1];
    if jcc.opcode != X86Opcode::Jcc || jmp.opcode != X86Opcode::Jmp {
        return None;
    }
    match (jcc.operands.first(), jcc.operands.get(1)) {
        (Some(X86ISelOperand::CondCode(X86CondCode::NE)), Some(X86ISelOperand::Block(t)))
            if body.contains(t) => {}
        _ => return None,
    }
    match jmp.operands.first() {
        Some(X86ISelOperand::Block(t)) if !body.contains(t) => {}
        _ => return None,
    }
    // A Setcc(B) must materialize the compare's below-result.
    if !block.insts.iter().any(|i| {
        i.opcode == X86Opcode::Setcc
            && matches!(
                i.operands.get(1),
                Some(X86ISelOperand::CondCode(X86CondCode::B))
            )
    }) {
        return None;
    }
    // Classify the bounds compare itself.
    for inst in &block.insts {
        let (lhs, bound) = match inst.opcode {
            X86Opcode::CmpRR => match (inst.operands.first(), inst.operands.get(1)) {
                (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => {
                    match const_of(func, defs, *y) {
                        Some(c) => (*x, c),
                        None => continue,
                    }
                }
                _ => continue,
            },
            X86Opcode::CmpRI | X86Opcode::CmpRI8 => {
                match (inst.operands.first(), inst.operands.get(1)) {
                    (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::Imm(c))) => (*x, *c),
                    _ => continue,
                }
            }
            _ => continue,
        };
        match prov(func, defs, iv, lhs, memo, 0) {
            Prov::Iv if bound >= n_trip => return Some(GuardClass::StaticOk),
            // The runtime-checkable invariant-offset guard. `bound >= n_trip`
            // (so `bound - (n_trip-1) >= 1`) and non-negative (array bounds
            // are element counts; a negative i64 would alias a huge unsigned
            // value in the check arithmetic) are required here, fail-safe.
            Prov::IvPlusInvMul(leaf, mult) if bound >= n_trip && bound >= 0 => {
                return Some(GuardClass::Inv(leaf, mult, bound));
            }
            _ => continue,
        }
    }
    None
}

/// True if any instruction inside `body` defines `v` (writes it as its
/// destination). Uses the closed-world body-opcode discipline: the caller only
/// invokes this after the whole body has been confirmed to contain whitelisted
/// / recognized opcodes, for which `x86_produces_value(op)` reliably identifies
/// `operands[0]` as the (only) register def.
fn vreg_defined_in_body(func: &X86ISelFunction, body: &BTreeSet<Block>, v: VReg) -> bool {
    for block_id in body {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            if x86_produces_value(inst.opcode)
                && let Some(X86ISelOperand::VReg(d)) = inst.operands.first()
                && *d == v
            {
                return true;
            }
        }
    }
    false
}

/// Recognizer for the i64 read-modify-write saxpy-accumulate shape at
/// loop-invariant flat offsets (see [`SaxpyQPlan`] for the shape and the full
/// legality argument). Returns a legal plan, or `None` for anything else —
/// every rejection leaves the (always-correct) scalar loop in place.
fn recognize_saxpyq_loop(
    func: &X86ISelFunction,
    preds: &HashMap<Block, Vec<Block>>,
    idom: &HashMap<Block, Block>,
    lp: &LoopInfo,
) -> Option<SaxpyQPlan> {
    let header = lp.header;
    let latch = lp.latch;
    let body = &lp.body;
    let preheader = lp.preheader?;

    // No PHI pseudo anywhere in the loop (non-SSA at this stage).
    for block_id in body {
        let block = func.blocks.get(block_id)?;
        if block.insts.iter().any(|i| i.opcode == X86Opcode::Phi) {
            return None;
        }
    }

    let defs = DefIndex::build(func);
    let mut memo: HashMap<VReg, Prov> = HashMap::new();

    // 1. IV + trip count from the header.
    let (iv, n_trip) = recognize_header(func, &defs, header, body)?;
    if n_trip < LANES_Q {
        return None; // no full vector iteration to gain from.
    }

    // 2. Body chain entry.
    let header_succs = &func.blocks.get(&header)?.successors;
    let body_entry = unique_in_body_succ(header_succs, body)?;

    // 3. Walk the body as a linear chain; every off-chain edge must be a pure
    //    `Ud2` trap guarded by a CLASSIFIED bounds compare. Static `iv <u c`
    //    guards elide unconditionally; invariant-offset guards become runtime
    //    obligations checked in the vector preheader.
    let mut obligations: Vec<(VReg, i64, i64)> = Vec::new();
    let mut chain: Vec<Block> = Vec::new();
    let mut visited: HashSet<Block> = HashSet::new();
    let mut cur = body_entry;
    loop {
        if !body.contains(&cur) || !visited.insert(cur) {
            return None;
        }
        chain.push(cur);
        let succs = &func.blocks.get(&cur)?.successors;
        let mut has_trap_edge = false;
        for s in succs {
            if body.contains(s) {
                continue;
            }
            if !is_pure_trap_block(func, *s) {
                return None;
            }
            has_trap_edge = true;
        }
        if has_trap_edge {
            match classify_guard_compare(func, &defs, iv, &mut memo, cur, body, n_trip)? {
                GuardClass::StaticOk => {}
                GuardClass::Inv(leaf, mult, bound) => {
                    // Dedup on (leaf, mult): keep the SMALLEST bound (the
                    // strongest runtime check dominates the others).
                    match obligations
                        .iter_mut()
                        .find(|(l, m, _)| *l == leaf && *m == mult)
                    {
                        Some(entry) => entry.2 = entry.2.min(bound),
                        None => obligations.push((leaf, mult, bound)),
                    }
                }
            }
        }
        if cur == latch {
            break;
        }
        let next = unique_in_body_succ(succs, body)?;
        cur = next;
    }
    // The latch's only in-body successor must be the header (the back-edge).
    if unique_in_body_succ(&func.blocks.get(&latch)?.successors, body)? != header {
        return None;
    }
    // Every body block except the header must be on the chain (nothing hidden).
    for block_id in body {
        if *block_id != header && !visited.contains(block_id) {
            return None;
        }
    }
    // The header must have exactly one exit successor and one body successor,
    // and the preheader must be the header's only non-body pred.
    {
        let hsuccs = &func.blocks.get(&header)?.successors;
        let non_body: Vec<Block> = hsuccs
            .iter()
            .copied()
            .filter(|s| !body.contains(s))
            .collect();
        if non_body.len() != 1 {
            return None;
        }
        let empty = Vec::new();
        let hpreds = preds.get(&header).unwrap_or(&empty);
        let non_body_preds: Vec<Block> = hpreds
            .iter()
            .copied()
            .filter(|p| !body.contains(p))
            .collect();
        if non_body_preds != vec![preheader] {
            return None;
        }
    }

    // 4. Collect the memory ops. Each load/store is admitted only if it is the
    //    64-bit form (`MovRM`/`MovMR`, Gpr64 value) whose plain `[addr + 0]`
    //    address classifies as `&slot[leaf*mult + iv]` with an 8-byte stride
    //    (`ElemAddrInvMul(slot, 8, leaf, mult)`).
    struct QAccess {
        slot: u32,
        leaf: VReg,
        mult: i64,
    }
    let mut loads: Vec<(VReg, QAccess)> = Vec::new(); // (canonical dst, access)
    let mut store: Option<(QAccess, VReg)> = None; // (access, canonical stored src)
    let classify_addr = |func: &X86ISelFunction,
                         defs: &DefIndex,
                         memo: &mut HashMap<VReg, Prov>,
                         mem: Option<&X86ISelOperand>|
     -> Option<QAccess> {
        match mem? {
            X86ISelOperand::MemAddr { base, disp } if *disp == 0 => match base.as_ref() {
                X86ISelOperand::VReg(b) => match prov(func, defs, iv, *b, memo, 0) {
                    Prov::ElemAddrInvMul(slot, scale, leaf, mult)
                        if scale == ELEM_SIZE_Q as i64 =>
                    {
                        Some(QAccess { slot, leaf, mult })
                    }
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    };
    for block_id in &chain {
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            let op = inst.opcode;
            if op == X86Opcode::Call || op == X86Opcode::CallR || op == X86Opcode::CallM {
                return None;
            }
            if is_load_opcode(op) {
                if op != X86Opcode::MovRM {
                    return None;
                }
                let dst = match inst.operands.first() {
                    Some(X86ISelOperand::VReg(d)) if d.class == RegClass::Gpr64 => *d,
                    _ => return None,
                };
                let access = classify_addr(func, &defs, &mut memo, inst.operands.get(1))?;
                loads.push((canon(func, &defs, dst), access));
            } else if is_store_opcode(op) {
                if op != X86Opcode::MovMR || store.is_some() {
                    return None;
                }
                let access = classify_addr(func, &defs, &mut memo, inst.operands.first())?;
                let src = match inst.operands.get(1) {
                    Some(X86ISelOperand::VReg(s)) if s.class == RegClass::Gpr64 => {
                        canon(func, &defs, *s)
                    }
                    _ => return None,
                };
                store = Some((access, src));
            } else if !is_whitelisted_body_opcode(op) {
                // Closed world: any unclassified opcode is a potential hidden
                // side effect (or trap) — refuse.
                return None;
            }
        }
    }
    let (store_access, stored_src) = store?;
    if loads.len() != 2 {
        return None;
    }

    let load_of =
        |v: VReg| -> Option<&QAccess> { loads.iter().find(|(d, _)| *d == v).map(|(_, a)| a) };
    let is_mul = |v: VReg| -> bool {
        defs.def_inst(func, v)
            .map(|i| i.opcode == X86Opcode::ImulRR)
            .unwrap_or(false)
    };

    // 5. The stored value is `AddRR(A, B)` (i64) with exactly one of {A, B} an
    //    `ImulRR` (the `K*x` term) and the other the accumulate-load.
    let top = defs.def_inst(func, stored_src)?;
    if top.opcode != X86Opcode::AddRR {
        return None;
    }
    match top.operands.first() {
        Some(X86ISelOperand::VReg(d)) if d.class == RegClass::Gpr64 => {}
        _ => return None,
    }
    let (ta, tb) = match (top.operands.get(1), top.operands.get(2)) {
        (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => {
            (canon(func, &defs, *x), canon(func, &defs, *y))
        }
        _ => return None,
    };
    let (mul_term, acc_term, mul_is_first) = if is_mul(ta) && load_of(tb).is_some() {
        (ta, tb, true)
    } else if load_of(ta).is_some() && is_mul(tb) {
        (tb, ta, false)
    } else {
        return None;
    };

    // 6. The accumulate term must be the load of EXACTLY the stored element:
    //    same slot, same canonical leaf, same multiplier. This is what makes
    //    the RMW same-index-only and kills any cross-iteration dependence.
    let acc_access = load_of(acc_term)?;
    if acc_access.slot != store_access.slot
        || acc_access.leaf != store_access.leaf
        || acc_access.mult != store_access.mult
    {
        return None;
    }

    // 7. The mul term is `ImulRR(load_x, K)` (either operand order, i64).
    let mul = defs.def_inst(func, mul_term)?;
    match mul.operands.first() {
        Some(X86ISelOperand::VReg(d)) if d.class == RegClass::Gpr64 => {}
        _ => return None,
    }
    let (ma, mb) = match (mul.operands.get(1), mul.operands.get(2)) {
        (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => {
            (canon(func, &defs, *x), canon(func, &defs, *y))
        }
        _ => return None,
    };
    let (mul_load, k_reg) = if load_of(ma).is_some() {
        (ma, mb)
    } else if load_of(mb).is_some() {
        (mb, ma)
    } else {
        return None;
    };
    let x_access = load_of(mul_load)?;

    // Closed world over loads: both collected loads must be consumed (the
    // accumulate term and the mul source) — no stray/dead loads.
    for (v, _) in &loads {
        if *v != mul_load && *v != acc_term {
            return None;
        }
    }

    // 8. The mul source must be a DIFFERENT slot than the destination, or the
    //    same slot at the SAME flat index (read-before-write per iteration).
    if x_access.slot == store_access.slot
        && (x_access.leaf != store_access.leaf || x_access.mult != store_access.mult)
    {
        return None;
    }

    // 9. `K` must be a provably loop-invariant runtime i64: NO def inside the
    //    loop (identical construction + fail-safe as `recognize_saxpy_loop`
    //    step 7). This is the SAME predicate step 10 below already applies to
    //    every access leaf — "no def inside the body ⇒ genuinely invariant
    //    across the whole loop execution" — so `K` is now judged by the rule
    //    this function already trusted for its offsets.
    //
    //    It previously demanded a SINGLE def function-wide plus dominance over
    //    the preheader. Both are stronger than invariance needs and reject the
    //    ordinary nested shape where an outer loop re-copies the scalar; that
    //    same over-conservatism kept `v1_saxpy` scalar at 8.75x of LLVM.
    if k_reg.class != RegClass::Gpr64 {
        return None;
    }
    if !loop_invariant_vreg(func, k_reg, body) {
        return None;
    }

    // 10. Every access leaf (and every obligation leaf) must have NO def inside
    //     the body — the flat offsets and the runtime checks are then genuinely
    //     invariant across the whole loop execution.
    for leaf in [store_access.leaf, x_access.leaf]
        .iter()
        .chain(obligations.iter().map(|(l, _, _)| l))
    {
        if vreg_defined_in_body(func, body, *leaf) {
            return None;
        }
    }
    // The leaves are read by the vector preheader's IMUL recomputation, so each
    // must also be a value that EXISTS at the preheader: conservatively require
    // some def whose block dominates the preheader (multi-def leaves like an
    // outer loop counter qualify through any dominating def — the value read at
    // the preheader is by definition the one the scalar body would read, since
    // no def lies inside the body).
    for leaf in [store_access.leaf, x_access.leaf]
        .iter()
        .chain(obligations.iter().map(|(l, _, _)| l))
    {
        let mut dominated = false;
        for block_id in &func.block_order {
            let Some(block) = func.blocks.get(block_id) else {
                continue;
            };
            for inst in &block.insts {
                if x86_produces_value(inst.opcode)
                    && let Some(X86ISelOperand::VReg(d)) = inst.operands.first()
                    && *d == *leaf
                    && dominates(*block_id, preheader, idom)
                {
                    dominated = true;
                }
            }
        }
        if !dominated {
            return None;
        }
    }

    // 11. Each access must be justified by a matching runtime obligation whose
    //     bound also fits the slot: `bound * 8 <= slot_size` makes every packed
    //     access provably in-slot once the runtime check passes.
    for access in [&store_access, x_access] {
        let (_, _, bound) = obligations
            .iter()
            .find(|(l, m, _)| *l == access.leaf && *m == access.mult)?;
        let info = func.stack_slots.get(access.slot as usize)?;
        let need = bound.checked_mul(ELEM_SIZE_Q as i64)?;
        if (info.size as i64) < need {
            return None;
        }
    }

    // 12. Resolve slot base vregs (unique `Lea r, [StackSlot(k)]` each).
    let base_x = slot_base_vreg(func, &defs, x_access.slot)?;
    let base_c = slot_base_vreg(func, &defs, store_access.slot)?;

    Some(SaxpyQPlan {
        iv,
        n_trip,
        base_x,
        slot_x: x_access.slot,
        base_c,
        slot_c: store_access.slot,
        leaf_x: x_access.leaf,
        mult_x: x_access.mult,
        leaf_c: store_access.leaf,
        mult_c: store_access.mult,
        k: k_reg,
        mul_is_first,
        obligations,
        preheader,
        header,
    })
}

/// Which integer reduction the summed term is.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ReduceKind {
    /// `acc += a[k]` — the summed term is a single loaded element.
    Sum,
    /// `acc += a[k] * b[k]` — the summed term is the i32 product of two loaded
    /// elements (`ImulRR` → packed `Pmulld`, then accumulate).
    Dot,
}

/// A verified-legal integer sum-reduction (`for k { acc = acc (+) f(a[k]…) }`)
/// ready to be rewritten to a packed accumulate loop + a covered horizontal
/// reduce + the unchanged scalar remainder. Every field is established by
/// construction in `recognize_reduction_loop`.
///
/// # Legality by construction (why reordering the additions is exact)
///
/// The scalar loop computes `acc_final = acc_init (+) t[0] (+) t[1] (+) … (+)
/// t[N-1]` where `t[k]` is `a[k]` (Sum) or `a[k]*b[k]` (Dot) and `(+)` is the i32
/// wrapping add `AddRR`. Integer wrapping add over `Z/2^32` is **associative AND
/// commutative**, so *any* regrouping/reordering of the `t[k]` yields a
/// bit-for-bit identical result. The rewrite accumulates into four independent
/// i32 lanes (`vacc[j]` gets `t[j], t[j+4], t[j+8], …`), so after the packed loop
/// `vacc[j] = Σ_{k≡j (mod 4), k<vN} t[k]`. The horizontal reduce sums the four
/// lanes — `vacc[0]+vacc[1]+vacc[2]+vacc[3] = Σ_{k<vN} t[k]` — and folds in the
/// carried `acc` (which still holds `acc_init`, untouched by the packed loop);
/// the unchanged scalar loop then adds `t[vN..N]`. The total is `acc_init (+)
/// Σ_{k<N} t[k]` — identical to the scalar loop. Every packed op (`MOVDQU`,
/// `PMULLD`, `PADDD`) computes the low 32 bits per lane, bit-for-bit the scalar
/// i32 `wrapping_mul`/`wrapping_add`. **This is sound WITHOUT a new proof only
/// because the op is integer add.** A float reduction is rejected (see below):
/// float add is *not* associative, so lane-partials + combine ≠ the sequential
/// sum. The horizontal reduce uses only covered ops — a `MOVDQU` store of the
/// accumulator to a fresh 16-byte scratch slot + four covered `MovRM32` scalar
/// loads + covered `AddRR`s — so there is **no `PHADDD`/`PSHUFD`/`PTEST`**.
struct ReducePlan {
    /// The loop counter vreg (element index; init 0, +1 per scalar iteration).
    iv: VReg,
    /// The loop-carried i32 (Gpr32) scalar accumulator vreg. Read once by the
    /// reduction add and written back each scalar iteration; never stored to
    /// memory mid-loop and used for nothing but the reduction.
    acc: VReg,
    /// Compile-time trip count `N` (from the header `iv <u N` test).
    n_trip: i64,
    /// Sum (`acc += a[k]`) or Dot (`acc += a[k]*b[k]`).
    kind: ReduceKind,
    /// Base-address vreg of the (first) summed array and its slot.
    base_a: VReg,
    slot_a: u32,
    /// Base-address vreg of the second array (Dot only; unused for Sum) + slot.
    base_b: VReg,
    slot_b: u32,
    /// The loop's preheader (its terminator is redirected to the vector loop).
    preheader: Block,
    /// The scalar loop header (the horizontal reduce falls into it for the tail).
    header: Block,
}

/// Recognizer for the integer sum-reduction shape:
///
/// ```text
/// let mut acc = …;                         // any init (folded in; need not be 0)
/// for k in 0..N { acc = acc.wrapping_add(a[k]); }                       // Sum
/// for k in 0..N { acc = acc.wrapping_add(a[k].wrapping_mul(b[k])); }    // Dot
/// ```
///
/// over local i32 arrays, with `acc` a **loop-carried Gpr32 register**
/// accumulator. Returns a legal `ReducePlan`, or `None` for anything else.
///
/// # Legality by construction / fail-safe
///
/// The header / body-chain / trap / unit-stride / in-bounds discipline is
/// **identical** to `recognize_elementwise_loop`. The reduction-specific
/// requirements — every one enforced, any failure ⇒ stay scalar:
///
/// * **The reduction op is the integer wrapping add `AddRR`.** The accumulator's
///   in-body writeback is `MovRR acc, acc_new` with `acc_new = AddRR(acc, term)`.
///   A float sum uses `Addss`/`Addsd` (not `AddRR`) and float loads use
///   `MovssRM`/`MovsdRM` (not `MovRM32`) and a float accumulator is `Fpr128`
///   (not `Gpr32`) — so a float reduction fails at three independent points and
///   stays scalar. Only `+` is admitted (no sub/min/max/xor-as-reduce, which are
///   either non-commutative or not what we prove associative here).
/// * **`acc` is a loop-carried i32 register that never escapes.** It is `Gpr32`,
///   has a def outside the loop body (its init), is written back exactly by the
///   reduction, and — critically — is **read nowhere in the loop except the
///   reduction add** (checked by a full body scan). If `acc` were read by another
///   computation, or stored to memory, the reordered partial sums would be
///   observable and the transform would be wrong; both make the recognizer bail.
/// * **The loop performs ZERO stores.** The accumulator lives in a register; any
///   store disqualifies the loop (it is not a pure register reduction, and a
///   store would reintroduce an aliasing/escape question).
/// * **The summed term is `a[k]` or `a[k]*b[k]` at index `iv`.** Each load is
///   admitted only as `&slot[iv]` (`ElemAddr(slot, ELEM_SIZE)`, disp 0), i32
///   (`MovRM32`). Sum: exactly one load, equal to the term. Dot: exactly two
///   loads, both consumed by the `ImulRR` that is the term. The source slots may
///   coincide (`a[k]*a[k]`) — every access is same-index so there is no
///   cross-element dependence.
/// * **Unit stride, known trip, in-bounds.** Identical to the element-wise
///   recognizer.
fn recognize_reduction_loop(
    func: &X86ISelFunction,
    preds: &HashMap<Block, Vec<Block>>,
    idom: &HashMap<Block, Block>,
    lp: &LoopInfo,
) -> Option<ReducePlan> {
    let header = lp.header;
    let latch = lp.latch;
    let body = &lp.body;
    let preheader = lp.preheader?;
    let _ = idom;

    // No PHI pseudo anywhere in the loop (non-SSA at this stage).
    for block_id in body {
        let block = func.blocks.get(block_id)?;
        if block.insts.iter().any(|i| i.opcode == X86Opcode::Phi) {
            return None;
        }
    }

    let defs = DefIndex::build(func);
    let mut memo: HashMap<VReg, Prov> = HashMap::new();

    // 1. IV + trip count from the header.
    let (iv, n_trip) = recognize_header(func, &defs, header, body)?;
    if n_trip < LANES {
        return None; // no full vector iteration to gain from.
    }

    // 2. Body chain entry.
    let header_succs = &func.blocks.get(&header)?.successors;
    let body_entry = unique_in_body_succ(header_succs, body)?;

    // 3. Walk the body as a linear chain; every off-chain edge must be a pure
    //    `Ud2` trap guarded by an `iv <u N` bounds compare (identical discipline
    //    to the element-wise / fill / saxpy recognizers).
    let mut chain: Vec<Block> = Vec::new();
    let mut visited: HashSet<Block> = HashSet::new();
    let mut cur = body_entry;
    loop {
        if !body.contains(&cur) || !visited.insert(cur) {
            return None;
        }
        chain.push(cur);
        let succs = &func.blocks.get(&cur)?.successors;
        let mut has_trap_edge = false;
        for s in succs {
            if body.contains(s) {
                continue;
            }
            if !is_pure_trap_block(func, *s) {
                return None;
            }
            has_trap_edge = true;
        }
        if has_trap_edge && !block_has_iv_bound_compare(func, &defs, iv, &mut memo, cur, n_trip) {
            return None;
        }
        if cur == latch {
            break;
        }
        let next = unique_in_body_succ(succs, body)?;
        cur = next;
    }
    // The latch's only in-body successor must be the header (the back-edge).
    if unique_in_body_succ(&func.blocks.get(&latch)?.successors, body)? != header {
        return None;
    }
    // Every body block except the header must be on the chain (nothing hidden).
    for block_id in body {
        if *block_id != header && !visited.contains(block_id) {
            return None;
        }
    }
    // The header must have exactly one exit successor and one body successor, and
    // the preheader must be the header's only non-body pred.
    {
        let hsuccs = &func.blocks.get(&header)?.successors;
        let non_body: Vec<Block> = hsuccs
            .iter()
            .copied()
            .filter(|s| !body.contains(s))
            .collect();
        if non_body.len() != 1 {
            return None;
        }
        let empty = Vec::new();
        let hpreds = preds.get(&header).unwrap_or(&empty);
        let non_body_preds: Vec<Block> = hpreds
            .iter()
            .copied()
            .filter(|p| !body.contains(p))
            .collect();
        if non_body_preds != vec![preheader] {
            return None;
        }
    }

    // 4. Collect memory ops in the chain: 1 or 2 i32 loads from `ElemAddr` slots,
    //    and ZERO stores (a register reduction writes no memory in-loop). No call.
    let mut loads: Vec<(VReg, u32)> = Vec::new(); // (canonical dst, slot)
    for block_id in &chain {
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            let op = inst.opcode;
            if op == X86Opcode::Call || op == X86Opcode::CallR || op == X86Opcode::CallM {
                return None;
            }
            if is_load_opcode(op) {
                if op != X86Opcode::MovRM32 {
                    return None; // i32 (Gpr) loads only; a float load ⇒ reject.
                }
                let dst = match inst.operands.first() {
                    Some(X86ISelOperand::VReg(d)) => *d,
                    _ => return None,
                };
                let slot = elem_addr_slot(
                    func,
                    &defs,
                    iv,
                    &mut memo,
                    inst.operands.get(1),
                    ELEM_SIZE as i64,
                )?;
                loads.push((canon(func, &defs, dst), slot));
            } else if is_store_opcode(op) {
                // A register reduction stores nothing mid-loop. Any store means
                // the accumulator (or something) escapes to memory — reject.
                return None;
            } else if op == X86Opcode::TrapBoundsCheckExact {
                // Inline proof-only bounds-check carrier: admit only when it
                // provably never traps for iv in [0, n_trip) (index==iv,
                // bound>=n_trip). The packed loop omits it (accesses proven
                // in-slot); the scalar remainder retains it.
                if !is_safe_iv_bounds_carrier(func, &defs, iv, &mut memo, inst, n_trip) {
                    return None;
                }
            } else if !is_whitelisted_body_opcode(op) {
                return None;
            }
        }
    }
    if loads.is_empty() || loads.len() > 2 {
        return None;
    }

    // 5. Find the single loop-carried accumulator + its reduction add. The
    //    accumulator's back-edge writeback is `MovRR/MovRR32 acc, <copy-of>
    //    acc_new` (in the body), where `acc_new = AddRR(acc, term)` — isel emits
    //    the add's result through one or more `MovRR32` copies before the
    //    writeback, so the writeback source is canonicalized through copies to
    //    reach the add. `acc` must be a Gpr32 (i32) with a def outside the loop
    //    body (its init) and must not be the IV.
    let mut found: Option<(VReg, VReg, (Block, usize))> = None; // (acc, term, add loc)
    for block_id in &chain {
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            if !matches!(inst.opcode, X86Opcode::MovRR | X86Opcode::MovRR32) {
                continue;
            }
            let (acc, raw_src) = match (inst.operands.first(), inst.operands.get(1)) {
                (Some(X86ISelOperand::VReg(d)), Some(X86ISelOperand::VReg(s))) => (*d, *s),
                _ => continue,
            };
            if acc == iv || acc.class != RegClass::Gpr32 {
                continue;
            }
            // Follow copies from the writeback source to the reduction result.
            let acc_new = canon(func, &defs, raw_src);
            // `acc_new` = AddRR(acc, term) | AddRR(term, acc).
            let Some((add_block, add_idx)) = defs.single.get(&acc_new).copied() else {
                continue;
            };
            let add = func.blocks.get(&add_block)?.insts.get(add_idx)?;
            if add.opcode != X86Opcode::AddRR {
                continue;
            }
            let (x, y) = match (add.operands.get(1), add.operands.get(2)) {
                (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => (*x, *y),
                _ => continue,
            };
            let (cx, cy) = (canon(func, &defs, x), canon(func, &defs, y));
            let term = if cx == acc {
                cy
            } else if cy == acc {
                cx
            } else {
                continue; // not a self-accumulation
            };
            // `acc` must be initialized outside the loop body (a genuine
            // loop-carried accumulator, not a transient).
            let has_outside_def = func.block_order.iter().any(|b| {
                !body.contains(b)
                    && func
                        .blocks
                        .get(b)
                        .map(|blk| {
                            blk.insts.iter().any(|i| {
                                x86_produces_value(i.opcode)
                                    && matches!(i.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == acc)
                            })
                        })
                        .unwrap_or(false)
            });
            if !has_outside_def {
                continue;
            }
            if found.is_some() {
                return None; // more than one reduction accumulator — not handled.
            }
            found = Some((acc, term, (add_block, add_idx)));
        }
    }
    let (acc, term, add_loc) = found?;

    // 6. Classify the term: a single loaded element (Sum), or the i32 product of
    //    two loaded elements (Dot). Establish the source slot(s).
    let slot_of = |v: VReg| -> Option<u32> { loads.iter().find(|(d, _)| *d == v).map(|(_, s)| *s) };
    let (kind, slot_a, slot_b) = if let Some(sa) = slot_of(term) {
        // Sum: the term is itself a loaded element. Exactly one load.
        if loads.len() != 1 {
            return None;
        }
        (ReduceKind::Sum, sa, sa)
    } else {
        // Dot: the term is `ImulRR(load_a, load_b)` of two loaded elements.
        let mul = defs.def_inst(func, term)?;
        if mul.opcode != X86Opcode::ImulRR {
            return None;
        }
        let (ma, mb) = match (mul.operands.get(1), mul.operands.get(2)) {
            (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => {
                (canon(func, &defs, *x), canon(func, &defs, *y))
            }
            _ => return None,
        };
        let sa = slot_of(ma)?;
        let sb = slot_of(mb)?;
        if loads.len() != 2 {
            return None; // both loads must feed the product; no stray loads.
        }
        // Closed world: the two collected loads are exactly the mul's operands.
        for (v, _) in &loads {
            if *v != ma && *v != mb {
                return None;
            }
        }
        (ReduceKind::Dot, sa, sb)
    };

    // 7. `acc` must be used ONLY by the reduction add anywhere in the loop body —
    //    otherwise a consumer would observe the reordered partial sums (a
    //    miscompile). Scan every body instruction; the only permitted read of
    //    `acc` is inside the reduction add itself.
    for block_id in body {
        let block = func.blocks.get(block_id)?;
        for (idx, inst) in block.insts.iter().enumerate() {
            if (*block_id, idx) == add_loc {
                continue; // the reduction add is the one allowed reader of `acc`.
            }
            // Operand 0 is a def for value-producing opcodes; every other operand
            // (and any def-slot of a non-producer, e.g. CmpRR) is a read.
            let produces = x86_produces_value(inst.opcode);
            for (opi, op) in inst.operands.iter().enumerate() {
                if produces && opi == 0 {
                    continue; // the def slot is not a read.
                }
                if operand_references_vreg(op, acc) {
                    return None;
                }
            }
        }
    }

    // 8. Each involved slot must hold >= N i32 elements so the packed accesses
    //    over indices [0, floor(N/4)*4) stay strictly in-slot.
    let need_bytes = n_trip.checked_mul(ELEM_SIZE as i64)?;
    let slots: &[u32] = if kind == ReduceKind::Dot && slot_a != slot_b {
        &[slot_a, slot_b]
    } else {
        std::slice::from_ref(&slot_a)
    };
    for slot in slots {
        let info = func.stack_slots.get(*slot as usize)?;
        if (info.size as i64) < need_bytes {
            return None;
        }
    }

    // 9. Resolve each slot back to its base-address vreg.
    let base_a = slot_base_vreg(func, &defs, slot_a)?;
    let base_b = if kind == ReduceKind::Dot {
        slot_base_vreg(func, &defs, slot_b)?
    } else {
        base_a
    };

    Some(ReducePlan {
        iv,
        acc,
        n_trip,
        kind,
        base_a,
        slot_a,
        base_b,
        slot_b,
        preheader,
        header,
    })
}

/// True if `op` reads `v` — directly as a `VReg`, or embedded as the base/index
/// of a memory operand.
fn operand_references_vreg(op: &X86ISelOperand, v: VReg) -> bool {
    match op {
        X86ISelOperand::VReg(x) => *x == v,
        X86ISelOperand::MemAddr { base, .. } => operand_references_vreg(base, v),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            operand_references_vreg(base, v) || operand_references_vreg(index, v)
        }
        _ => false,
    }
}

// ===========================================================================
// Heap-slice i64 sum reduction with a RUNTIME trip count (the `acc += v[k]`
// loop over a `Vec<u64>`/`&[u64]`, k in 0..v.len()).
// ===========================================================================

/// A verified-legal i64 sum-reduction over a **heap slice** with a **runtime**
/// trip count, ready to be rewritten to a packed PADDQ-accumulate loop + a
/// covered horizontal reduce + the unchanged scalar loop as the remainder.
/// Every field is established by construction in `recognize_heap_sumq_loop`.
///
/// # The recognized shape (post-ISel, raw)
///
/// ```text
/// while k < v.len() {            // header: k <u load [P + dlen]  (runtime!)
///     acc = acc.wrapping_add(v[k]);   // guard: k <u load [P + dlen] → Ud2
///     k += 1;                          // element: load [load-of-ptr + k*8]
/// }
/// ```
///
/// where `P` is a stack slot holding the slice/Vec (`[P + dptr]` = data
/// pointer, `[P + dlen]` = length) and the body may additionally re-store the
/// (invariant) pair into a second, distinct stack slot `S` each iteration (the
/// rustc slice-reborrow temp) and re-load the data pointer through it.
///
/// # Legality by construction (all checked; any failure ⇒ stay scalar)
///
/// * **The bound and the guards read the same invariant field.** The header
///   bound and every trap-guard bound are 64-bit loads of the *same* stack-slot
///   field `[slot_len + dlen]`. The only stores in the loop go to a *different*
///   stack slot (distinct slots occupy disjoint frame regions), so that field
///   is invariant: every load of it yields the same value `len0`. The header
///   admits iteration `k` only if `k <u len0`, so each guard's `k <u len0`
///   provably passes — eliding the guards in the packed body cannot lose a
///   trap, and the scalar reference execution performs the element load for
///   every `k in [0, len0)`.
/// * **Packed reads are exactly the scalar reads.** The element address is
///   `ptr0 + 8*k` where `ptr0` is the (equally invariant) `[slot_ptr + dptr]`
///   field value. The packed loop reads `[ptr0 + 8*j, ptr0 + 8*j + 16)` for
///   even `j < vN` with `vN = len0 & !1` — byte-for-byte the union of the
///   scalar loop's iteration-`j`/`j+1` reads. It reads **no byte the scalar
///   loop would not read**, so validity/permissions are inherited from the
///   scalar execution (no slot-size reasoning is needed for a heap base), and
///   MOVDQU has no alignment requirement.
/// * **In-loop stores are invariant and replayed.** Each body store writes a
///   field-load result (an invariant value, see above) to a fixed field of the
///   single store-target slot `S`, fields pairwise disjoint. The stores are
///   therefore idempotent across iterations; the vector preheader replays them
///   ONCE (same sources, same destinations) iff the packed loop is entered
///   (`vN >= 2` ⇒ the scalar loop would have executed ≥ 1 iteration and hence
///   performed the same stores at least once), so post-loop memory is
///   identical in both executions — including when the even-`len0` epilogue
///   runs zero scalar iterations.
/// * **A body load through `S` is a forwarded invariant.** A load of `[S + d]`
///   is admitted only when the SAME iteration previously stored `[S + d]`
///   (store strictly precedes it on the straight-line body chain) and no other
///   store overlaps `[d, d+8)`; its value is then the store's (invariant)
///   source field on every iteration, including the first.
/// * **Exact wrapping-add reduction.** `acc` is a loop-carried Gpr64 register
///   accumulator: written back exactly once per iteration as
///   `acc = AddRR(acc, elem)`, initialized outside the body, read by nothing
///   else inside the body, and never stored (store values must be field
///   loads). i64 wrapping add over `Z/2^64` is associative and commutative, so
///   two lane-partials + a covered horizontal fold reproduce the sequential
///   sum bit-for-bit (same argument as [`ReducePlan`], PADDQ lanes).
/// * **Loop-exit register state matches.** `iv` leaves the loop equal to
///   `len0` in both executions (unit stride from 0, first failing header test
///   at `len0`; the epilogue continues from `vN <= len0`). `acc` leaves with
///   the identical sum. Every OTHER vreg defined in a non-header body block is
///   verified to have **no use outside the loop body** (the packed path may
///   skip the body's final execution when `len0` is even); header-defined
///   vregs are safe unconditionally — the epilogue's final header execution
///   (`k = len0`) recomputes them from the same invariant inputs.
/// * **Runtime gate, fail-safe.** `vN = len0 & !1` is computed at the vector
///   preheader from a fresh load of the same field; `vN == 0` (len0 < 2)
///   branches to the UNCHANGED scalar loop with memory untouched.
///
/// Every emitted packed op (MOVDQU load/store, PADDQ) plus the scalar glue
/// (Lea/MovRM/MovMR/MovRI/AndRI/CmpRR/CmpRI/AddRR/MovRR/LeaSib/Jcc/Jmp) is
/// proof-covered; this pass owns only the legality decision above.
struct HeapSumQPlan {
    /// The loop counter vreg (element index; init 0, +1 per scalar iteration).
    iv: VReg,
    /// The loop-carried i64 (Gpr64) scalar accumulator vreg.
    acc: VReg,
    /// Stack-slot field holding the runtime length (header/guard bound).
    len_slot: u32,
    len_disp: i32,
    /// Stack-slot field holding the slice data pointer (element-load base).
    ptr_slot: u32,
    ptr_disp: i32,
    /// The single store-target slot (the slice-reborrow temp), if the body
    /// stores at all, with the replayed fields:
    /// `(dest disp in slice_slot, source slot, source disp)`.
    slice_slot: Option<u32>,
    stores: Vec<(i32, u32, i32)>,
    /// The loop's preheader (its terminator is redirected to the vector CFG).
    preheader: Block,
    /// The scalar loop header (runtime-gate failure and the remainder enter it).
    header: Block,
}

/// Resolve `v` to a stack-slot base plus a constant byte offset by following
/// the copy-canonicalized `Lea` chain: `Lea r, [StackSlot(s) + d]` resolves to
/// `(s, d)`; `Lea r, [r2 + d]` recurses into `r2` (bounded). Anything else —
/// a pointer parameter, a loaded pointer, arithmetic — is `None` (fail-safe).
fn resolve_slot_disp(
    func: &X86ISelFunction,
    defs: &DefIndex,
    v: VReg,
    depth: u32,
) -> Option<(u32, i64)> {
    if depth > 16 {
        return None;
    }
    let c = canon(func, defs, v);
    let inst = defs.def_inst(func, c)?;
    if inst.opcode != X86Opcode::Lea {
        return None;
    }
    match inst.operands.get(1)? {
        X86ISelOperand::MemAddr { base, disp } => match base.as_ref() {
            X86ISelOperand::StackSlot(s) => Some((*s, *disp as i64)),
            X86ISelOperand::VReg(b) => {
                let (s, d) = resolve_slot_disp(func, defs, *b, depth + 1)?;
                Some((s, d + *disp as i64))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Resolve a memory operand (`MemAddr { base, disp }`) to `(slot, total_disp)`
/// where `base` is a stack-slot address per [`resolve_slot_disp`].
fn resolve_mem_slot_disp(
    func: &X86ISelFunction,
    defs: &DefIndex,
    mem: Option<&X86ISelOperand>,
) -> Option<(u32, i64)> {
    match mem? {
        X86ISelOperand::MemAddr { base, disp } => match base.as_ref() {
            X86ISelOperand::VReg(b) => {
                let (s, d) = resolve_slot_disp(func, defs, *b, 0)?;
                Some((s, d + *disp as i64))
            }
            X86ISelOperand::StackSlot(s) => Some((*s, *disp as i64)),
            _ => None,
        },
        _ => None,
    }
}

/// If `v` canonicalizes to a 64-bit load of a stack-slot field, return the
/// canonical dst plus `(slot, disp)`.
fn slot_field_load(func: &X86ISelFunction, defs: &DefIndex, v: VReg) -> Option<(VReg, u32, i64)> {
    let c = canon(func, defs, v);
    let inst = defs.def_inst(func, c)?;
    if inst.opcode != X86Opcode::MovRM {
        return None;
    }
    let (s, d) = resolve_mem_slot_disp(func, defs, inst.operands.get(1))?;
    Some((c, s, d))
}

/// Pin a block's `<u`-branch discipline and recover the compare operands.
///
/// The block must end `[.., CmpRI(w, 0), Jcc(NE, taken), Jmp(fallthrough)]`,
/// and `w` must chase back (walking the block's instructions in reverse,
/// following only value-preserving `Movzx`/`MovRR`/`AndRI(_,1)` links) to a
/// `Setcc(_, B)` whose **immediately preceding** instruction is the flag-
/// setting `CmpRR(lhs, rhs)`. Returns `(lhs, rhs, taken, fallthrough)` —
/// i.e. the branch takes `taken` iff `lhs <u rhs`. Anything else is `None`.
fn chase_below_branch(
    func: &X86ISelFunction,
    block_id: Block,
) -> Option<(VReg, VReg, Block, Block)> {
    let block = func.blocks.get(&block_id)?;
    let n = block.insts.len();
    if n < 5 {
        return None;
    }
    let jcc = &block.insts[n - 2];
    let jmp = &block.insts[n - 1];
    if jcc.opcode != X86Opcode::Jcc || jmp.opcode != X86Opcode::Jmp {
        return None;
    }
    let taken = match (jcc.operands.first(), jcc.operands.get(1)) {
        (Some(X86ISelOperand::CondCode(X86CondCode::NE)), Some(X86ISelOperand::Block(t))) => *t,
        _ => return None,
    };
    let fallthrough = match jmp.operands.first() {
        Some(X86ISelOperand::Block(t)) => *t,
        _ => return None,
    };
    let cmpri = &block.insts[n - 3];
    if !matches!(cmpri.opcode, X86Opcode::CmpRI | X86Opcode::CmpRI8) {
        return None;
    }
    let mut cur = match (cmpri.operands.first(), cmpri.operands.get(1)) {
        (Some(X86ISelOperand::VReg(w)), Some(X86ISelOperand::Imm(0))) => *w,
        _ => return None,
    };
    let mut i = n - 3;
    while i > 0 {
        i -= 1;
        let inst = &block.insts[i];
        if !x86_produces_value(inst.opcode) {
            continue;
        }
        match inst.operands.first() {
            Some(X86ISelOperand::VReg(d)) if *d == cur => {}
            _ => continue,
        }
        match inst.opcode {
            X86Opcode::Movzx | X86Opcode::MovzxW | X86Opcode::MovRR | X86Opcode::MovRR32 => {
                match inst.operands.get(1) {
                    Some(X86ISelOperand::VReg(s)) => cur = *s,
                    _ => return None,
                }
            }
            X86Opcode::AndRI => match (inst.operands.get(1), inst.operands.get(2)) {
                (Some(X86ISelOperand::VReg(s)), Some(X86ISelOperand::Imm(1))) => cur = *s,
                _ => return None,
            },
            X86Opcode::Setcc => {
                if !matches!(
                    inst.operands.get(1),
                    Some(X86ISelOperand::CondCode(X86CondCode::B))
                ) {
                    return None;
                }
                if i == 0 {
                    return None;
                }
                let prev = &block.insts[i - 1];
                if prev.opcode != X86Opcode::CmpRR {
                    return None;
                }
                return match (prev.operands.first(), prev.operands.get(1)) {
                    (Some(X86ISelOperand::VReg(l)), Some(X86ISelOperand::VReg(r))) => {
                        Some((*l, *r, taken, fallthrough))
                    }
                    _ => None,
                };
            }
            _ => return None,
        }
    }
    None
}

/// If `mem` is `MemAddr { base, disp: 0 }` whose canonical base is
/// `AddRR(x, y)` with exactly one side of provenance `ScaledIv(8)` (the
/// `iv*8` byte offset), return the OTHER side's canonical vreg (the runtime
/// base pointer). This is the raw-isel heap element address `ptr + iv*8`.
fn heap_elem_base(
    func: &X86ISelFunction,
    defs: &DefIndex,
    iv: VReg,
    memo: &mut HashMap<VReg, Prov>,
    mem: Option<&X86ISelOperand>,
) -> Option<VReg> {
    match mem? {
        X86ISelOperand::MemAddr { base, disp } if *disp == 0 => {
            let b = match base.as_ref() {
                X86ISelOperand::VReg(b) => *b,
                _ => return None,
            };
            let c = canon(func, defs, b);
            let inst = defs.def_inst(func, c)?;
            if inst.opcode != X86Opcode::AddRR {
                return None;
            }
            let (x, y) = match (inst.operands.get(1), inst.operands.get(2)) {
                (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => (*x, *y),
                _ => return None,
            };
            let px = prov(func, defs, iv, x, memo, 0);
            let py = prov(func, defs, iv, y, memo, 0);
            if px == Prov::ScaledIv(ELEM_SIZE_Q as i64) {
                return Some(canon(func, defs, y));
            }
            if py == Prov::ScaledIv(ELEM_SIZE_Q as i64) {
                return Some(canon(func, defs, x));
            }
            None
        }
        _ => None,
    }
}

/// Recognizer for the heap-slice i64 sum-reduction shape (see
/// [`HeapSumQPlan`] for the shape and the full legality argument). Returns a
/// legal plan, or `None` for anything else — every rejection leaves the
/// (always-correct) scalar loop in place.
fn recognize_heap_sumq_loop(
    func: &X86ISelFunction,
    preds: &HashMap<Block, Vec<Block>>,
    idom: &HashMap<Block, Block>,
    lp: &LoopInfo,
) -> Option<HeapSumQPlan> {
    let header = lp.header;
    let latch = lp.latch;
    let body = &lp.body;
    let preheader = lp.preheader?;
    let _ = idom;

    // No PHI pseudo anywhere in the loop (non-SSA at this stage).
    for block_id in body {
        let block = func.blocks.get(block_id)?;
        if block.insts.iter().any(|i| i.opcode == X86Opcode::Phi) {
            return None;
        }
    }

    let defs = DefIndex::build(func);
    let mut memo: HashMap<VReg, Prov> = HashMap::new();

    // 1. Header: `iv <u len` with a RUNTIME bound — the pinned CmpRR/Setcc(B)/
    //    Jcc(NE, body)/Jmp(exit) chain, bound = a 64-bit stack-slot field load.
    let (lhs, rhs, t_body, t_exit) = chase_below_branch(func, header)?;
    if !body.contains(&t_body) || body.contains(&t_exit) {
        return None;
    }
    let iv = canon(func, &defs, lhs);
    if iv.class != RegClass::Gpr64 || !is_counter(func, &defs, iv, body) {
        return None;
    }
    // 1b. The IV must enter the loop as EXACTLY zero: exactly ONE def outside
    //     the body, and it is a `MovRR iv, <MovRI 0>` in the preheader itself.
    //     (`is_counter` proves a zero-init EXISTS but not that it is unique;
    //     the packed loop pairs elements [iv, iv+1] from the entry value, so a
    //     second outside def — e.g. an odd entry value — would break the
    //     packed-reads-are-exactly-scalar-reads argument at the tail.)
    {
        let mut outside_defs = 0usize;
        let mut preheader_zero_init = false;
        for block_id in &func.block_order {
            if body.contains(block_id) {
                continue;
            }
            let Some(block) = func.blocks.get(block_id) else {
                continue;
            };
            for inst in &block.insts {
                if x86_produces_value(inst.opcode)
                    && matches!(inst.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == iv)
                {
                    outside_defs += 1;
                    if *block_id == preheader
                        && inst.opcode == X86Opcode::MovRR
                        && let Some(X86ISelOperand::VReg(s)) = inst.operands.get(1)
                        && const_of(func, &defs, *s) == Some(0)
                    {
                        preheader_zero_init = true;
                    }
                }
            }
        }
        if outside_defs != 1 || !preheader_zero_init {
            return None;
        }
    }
    let (_, len_slot, len_disp) = slot_field_load(func, &defs, rhs)?;

    // The header must have exactly one exit successor and one body successor,
    // and the preheader must be the header's only non-body pred.
    {
        let hsuccs = &func.blocks.get(&header)?.successors;
        let non_body: Vec<Block> = hsuccs
            .iter()
            .copied()
            .filter(|s| !body.contains(s))
            .collect();
        if non_body.len() != 1 {
            return None;
        }
        let empty = Vec::new();
        let hpreds = preds.get(&header).unwrap_or(&empty);
        let non_body_preds: Vec<Block> = hpreds
            .iter()
            .copied()
            .filter(|p| !body.contains(p))
            .collect();
        if non_body_preds != vec![preheader] {
            return None;
        }
    }
    // The preheader must reach the header ONLY via its terminating
    // unconditional `Jmp` — the apply rewrites exactly that operand, so any
    // other edge form (e.g. a `Jcc` targeting the header) would desync the
    // successor list from the actual branch target. Fail-safe: reject.
    {
        let pre = func.blocks.get(&preheader)?;
        match pre.insts.last() {
            Some(j)
                if j.opcode == X86Opcode::Jmp
                    && matches!(j.operands.first(), Some(X86ISelOperand::Block(t)) if *t == header) =>
                {}
            _ => return None,
        }
        for inst in &pre.insts {
            if inst.opcode == X86Opcode::Jcc
                && matches!(inst.operands.get(1), Some(X86ISelOperand::Block(t)) if *t == header)
            {
                return None;
            }
        }
    }

    // 2. Walk the body as a linear chain; every off-chain edge must be a pure
    //    `Ud2` trap guarded by the SAME `iv <u [len_slot + len_disp]` compare.
    let header_succs = &func.blocks.get(&header)?.successors;
    let body_entry = unique_in_body_succ(header_succs, body)?;
    let mut chain: Vec<Block> = Vec::new();
    let mut visited: HashSet<Block> = HashSet::new();
    let mut cur = body_entry;
    loop {
        if !body.contains(&cur) || !visited.insert(cur) {
            return None;
        }
        chain.push(cur);
        let succs = &func.blocks.get(&cur)?.successors;
        let mut has_trap_edge = false;
        for s in succs {
            if body.contains(s) {
                continue;
            }
            if !is_pure_trap_block(func, *s) {
                return None;
            }
            has_trap_edge = true;
        }
        if has_trap_edge {
            let (glhs, grhs, gt_taken, gt_fall) = chase_below_branch(func, cur)?;
            if !body.contains(&gt_taken) || body.contains(&gt_fall) {
                return None;
            }
            if canon(func, &defs, glhs) != iv {
                return None;
            }
            let (_, gs, gd) = slot_field_load(func, &defs, grhs)?;
            if gs != len_slot || gd != len_disp {
                return None;
            }
        }
        if cur == latch {
            break;
        }
        let next = unique_in_body_succ(succs, body)?;
        cur = next;
    }
    // The latch's only in-body successor must be the header (the back-edge).
    if unique_in_body_succ(&func.blocks.get(&latch)?.successors, body)? != header {
        return None;
    }
    // Every body block except the header must be on the chain (nothing hidden).
    for block_id in body {
        if *block_id != header && !visited.contains(block_id) {
            return None;
        }
    }

    // 3. Closed-world scan over the header + chain: collect field loads,
    //    the element load, and stores; reject calls and unknown opcodes.
    let mut field_loads: Vec<(VReg, u32, i64, usize)> = Vec::new(); // (dst, slot, disp, pos)
    let mut elem_loads: Vec<(VReg, VReg, usize)> = Vec::new(); // (dst, base, pos)
    let mut raw_stores: Vec<(u32, i64, VReg, usize)> = Vec::new(); // (slot, disp, value, pos)
    let mut pos = 0usize;
    for block_id in std::iter::once(&header).chain(chain.iter()) {
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            pos += 1;
            let op = inst.opcode;
            if op == X86Opcode::Call || op == X86Opcode::CallR || op == X86Opcode::CallM {
                return None;
            }
            if is_load_opcode(op) {
                if op != X86Opcode::MovRM {
                    return None; // 64-bit Gpr loads only.
                }
                let dst = match inst.operands.first() {
                    Some(X86ISelOperand::VReg(d)) if d.class == RegClass::Gpr64 => *d,
                    _ => return None,
                };
                let dc = canon(func, &defs, dst);
                if let Some((s, d)) = resolve_mem_slot_disp(func, &defs, inst.operands.get(1)) {
                    field_loads.push((dc, s, d, pos));
                } else {
                    let base = heap_elem_base(func, &defs, iv, &mut memo, inst.operands.get(1))?;
                    elem_loads.push((dc, base, pos));
                }
            } else if is_store_opcode(op) {
                if op != X86Opcode::MovMR {
                    return None;
                }
                let (s, d) = resolve_mem_slot_disp(func, &defs, inst.operands.first())?;
                let val = match inst.operands.get(1) {
                    Some(X86ISelOperand::VReg(v)) if v.class == RegClass::Gpr64 => {
                        canon(func, &defs, *v)
                    }
                    _ => return None,
                };
                raw_stores.push((s, d, val, pos));
            } else if !is_whitelisted_body_opcode(op) {
                return None;
            }
        }
    }

    // 4. Stores: all to ONE slot, pairwise-disjoint 8-byte fields, each value
    //    the result of a field load from a DIFFERENT (hence invariant) slot.
    let mut slice_slot: Option<u32> = None;
    let mut stores: Vec<(i32, u32, i32)> = Vec::new(); // (dest disp, src slot, src disp)
    let mut store_ranges: Vec<(i64, usize)> = Vec::new(); // (dest disp, pos)
    for (s, d, val, spos) in &raw_stores {
        match slice_slot {
            None => slice_slot = Some(*s),
            Some(ss) if ss == *s => {}
            _ => return None, // stores to more than one slot — refuse.
        }
        if store_ranges.iter().any(|(d2, _)| (d2 - d).abs() < 8) {
            return None; // overlapping/duplicate store fields — refuse.
        }
        let &(_, fs, fd, _) = field_loads.iter().find(|(dst, ..)| dst == val)?;
        if Some(fs) == slice_slot {
            return None; // chained through the store-target slot — refuse.
        }
        stores.push((i32::try_from(*d).ok()?, fs, i32::try_from(fd).ok()?));
        store_ranges.push((*d, *spos));
    }
    // A store overlapping `[disp, disp+8)` of `slot`?
    let store_overlaps = |slot: u32, disp: i64| -> bool {
        slice_slot == Some(slot) && store_ranges.iter().any(|(d, _)| (d - disp).abs() < 8)
    };
    // The len field must be invariant (no store may overlap it).
    if store_overlaps(len_slot, len_disp) {
        return None;
    }

    // 5. Exactly one element load; resolve its base to an invariant
    //    stack-slot field, forwarding through a preceding same-iteration
    //    store of the slice temp when needed.
    if elem_loads.len() != 1 {
        return None;
    }
    let (elem_dst, elem_base, elem_pos) = elem_loads[0];
    let &(_, bs, bd, bpos) = field_loads.iter().find(|(dst, ..)| *dst == elem_base)?;
    let (ptr_slot, ptr_disp) = if Some(bs) == slice_slot {
        // Forwarded reload: [slice_slot + bd] must match a store exactly, and
        // that store must precede the reload on the straight-line chain.
        let overlapping: Vec<&(i64, usize)> = store_ranges
            .iter()
            .filter(|(d, _)| (d - bd).abs() < 8)
            .collect();
        if overlapping.len() != 1 || *overlapping[0] != (bd, overlapping[0].1) {
            return None;
        }
        if overlapping[0].1 >= bpos {
            return None; // load precedes the store — value would be stale.
        }
        let &(_, fs, fd) = stores.iter().find(|(d, ..)| i64::from(*d) == bd)?;
        (fs, i64::from(fd))
    } else {
        if store_overlaps(bs, bd) {
            return None;
        }
        (bs, bd)
    };
    if elem_pos <= bpos {
        return None; // the element load must consume the resolved base.
    }
    if store_overlaps(ptr_slot, ptr_disp) {
        return None; // the pointer field itself must be invariant.
    }

    // 6. Find the single loop-carried Gpr64 accumulator + its reduction add
    //    `acc = AddRR(acc, elem)` (identical discipline to `ReducePlan` step 5,
    //    at 64-bit width).
    let mut found: Option<(VReg, (Block, usize))> = None; // (acc, add loc)
    for block_id in &chain {
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            if !matches!(inst.opcode, X86Opcode::MovRR | X86Opcode::MovRR32) {
                continue;
            }
            let (acc, raw_src) = match (inst.operands.first(), inst.operands.get(1)) {
                (Some(X86ISelOperand::VReg(d)), Some(X86ISelOperand::VReg(s))) => (*d, *s),
                _ => continue,
            };
            if acc == iv || acc.class != RegClass::Gpr64 {
                continue;
            }
            let acc_new = canon(func, &defs, raw_src);
            let Some((add_block, add_idx)) = defs.single.get(&acc_new).copied() else {
                continue;
            };
            let add = func.blocks.get(&add_block)?.insts.get(add_idx)?;
            if add.opcode != X86Opcode::AddRR {
                continue;
            }
            let (x, y) = match (add.operands.get(1), add.operands.get(2)) {
                (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => (*x, *y),
                _ => continue,
            };
            let (cx, cy) = (canon(func, &defs, x), canon(func, &defs, y));
            let term = if cx == acc {
                cy
            } else if cy == acc {
                cx
            } else {
                continue; // not a self-accumulation.
            };
            if term != elem_dst {
                continue; // the summed term must be THE element load.
            }
            // `acc` must be initialized outside the loop body.
            let has_outside_def = func.block_order.iter().any(|b| {
                !body.contains(b)
                    && func
                        .blocks
                        .get(b)
                        .map(|blk| {
                            blk.insts.iter().any(|i| {
                                x86_produces_value(i.opcode)
                                    && matches!(i.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == acc)
                            })
                        })
                        .unwrap_or(false)
            });
            if !has_outside_def {
                continue;
            }
            if found.is_some() {
                return None; // more than one reduction accumulator — refuse.
            }
            found = Some((acc, (add_block, add_idx)));
        }
    }
    let (acc, add_loc) = found?;

    // 7. `acc` must be read ONLY by the reduction add anywhere in the body.
    for block_id in body {
        let block = func.blocks.get(block_id)?;
        for (idx, inst) in block.insts.iter().enumerate() {
            if (*block_id, idx) == add_loc {
                continue;
            }
            let produces = x86_produces_value(inst.opcode);
            for (opi, op) in inst.operands.iter().enumerate() {
                if produces && opi == 0 {
                    continue;
                }
                if operand_references_vreg(op, acc) {
                    return None;
                }
            }
        }
    }

    // 8. `acc` and `iv` must each have exactly ONE in-body def (the writeback):
    //    a second def would break the loop-carried argument.
    for carried in [acc, iv] {
        let mut n_defs = 0usize;
        for block_id in body {
            let block = func.blocks.get(block_id)?;
            for inst in &block.insts {
                if x86_produces_value(inst.opcode)
                    && matches!(inst.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == carried)
                {
                    n_defs += 1;
                }
            }
        }
        if n_defs != 1 {
            return None;
        }
    }

    // 9. No vreg defined ANYWHERE in the loop body (other than `acc`/`iv`)
    //    may be used outside the loop body. The packed path may skip the
    //    body's final execution entirely (even `len0`), so a non-header body
    //    def could be stale at the exit; header defs are conservatively
    //    included too (their recomputation-equality would additionally
    //    require proving they derive only from invariant inputs). `acc` and
    //    `iv` are exempt because their exit values are proven identical
    //    (exact fold-in; unit stride exits at `len0` on both paths).
    let mut inner_defs: HashSet<VReg> = HashSet::new();
    for block_id in body {
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            if x86_produces_value(inst.opcode)
                && let Some(X86ISelOperand::VReg(d)) = inst.operands.first()
            {
                inner_defs.insert(*d);
            }
        }
    }
    inner_defs.remove(&acc);
    inner_defs.remove(&iv);
    for block_id in &func.block_order {
        if body.contains(block_id) {
            continue;
        }
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            let produces = x86_produces_value(inst.opcode);
            for (opi, op) in inst.operands.iter().enumerate() {
                if produces && opi == 0 {
                    continue;
                }
                if inner_defs.iter().any(|v| operand_references_vreg(op, *v)) {
                    return None;
                }
            }
        }
    }

    let _ = elem_pos;
    Some(HeapSumQPlan {
        iv,
        acc,
        len_slot,
        len_disp: i32::try_from(len_disp).ok()?,
        ptr_slot,
        ptr_disp: i32::try_from(ptr_disp).ok()?,
        slice_slot,
        stores,
        preheader,
        header,
    })
}

/// If `mem` is a `MemAddr { base, disp: 0 }` whose base has provenance
/// `ElemAddr(slot, scale)` with `scale == elem_size`, return `slot`. This is the
/// `&slot[iv]` address form for an `elem_size`-byte element. The scale must match
/// the memory op's width exactly: a mismatched scale means the index is *not*
/// stepping one `elem_size` element per `iv`, so it is rejected (fail-safe).
fn elem_addr_slot(
    func: &X86ISelFunction,
    defs: &DefIndex,
    iv: VReg,
    memo: &mut HashMap<VReg, Prov>,
    mem: Option<&X86ISelOperand>,
    elem_size: i64,
) -> Option<u32> {
    let out = match mem {
        Some(X86ISelOperand::MemAddr { base, disp }) if *disp == 0 => match base.as_ref() {
            X86ISelOperand::VReg(b) => match prov(func, defs, iv, *b, memo, 0) {
                Prov::ElemAddr(s, scale) if scale == elem_size => Some(s),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    };
    // DIAGNOSTIC (`TCG_TRACE_VECTORIZE_PROV`): every recognizer classifies its
    // accesses HERE, so a `None` here is the single choke point through which
    // essentially every silent decline passes. Printing the provenance actually
    // computed — rather than only the fact of a rejection — names the defect
    // directly: a `SlotBase`/`ScaledIv` that never formed, a scale that
    // disagrees with the element width, or a non-zero displacement.
    //
    // Added because the vectorizable cluster sat at 4.6x of LLVM while the
    // recognizers that cover it existed and simply declined without a word.
    if std::env::var_os("TCG_TRACE_VECTORIZE_PROV").is_some()
        && let Some(slot) = out
    {
        eprintln!("x86-vectorize[prov]: ACCEPT slot={slot} elem_size={elem_size}");
    }
    if out.is_none() && std::env::var_os("TCG_TRACE_VECTORIZE_PROV").is_some() {
        match mem {
            Some(X86ISelOperand::MemAddr { base, disp }) => match base.as_ref() {
                X86ISelOperand::VReg(b) => eprintln!(
                    "x86-vectorize[prov]: reject addr base={:?} disp={} elem_size={} prov={:?}",
                    b,
                    disp,
                    elem_size,
                    prov(func, defs, iv, *b, memo, 0)
                ),
                other => eprintln!(
                    "x86-vectorize[prov]: reject addr non-vreg base={other:?} disp={disp}"
                ),
            },
            other => eprintln!("x86-vectorize[prov]: reject non-MemAddr operand {other:?}"),
        }
    }
    out
}

/// Is `v` loop-invariant with respect to the loop whose blocks are `body`?
///
/// True iff `v` has at least one def in the function and **no def inside the
/// loop**. Multiple defs OUTSIDE the loop are fine, and that is the whole point:
/// requiring a single def function-wide is much stronger than invariance needs,
/// and it is what kept `v1_saxpy` scalar at 8.75x of LLVM. Its `k` (`bb(3i32)`)
/// has two defs — both plain `MovRR32` copies, both outside the inner loop —
/// because the enclosing repetition loop re-copies the same value each time
/// round.
///
/// # Why "no def inside the loop" is sufficient
///
/// Each recognizer that consults this has already established that the loop's
/// only non-body predecessor is its preheader, and each emits the broadcast into
/// a vector preheader placed **on that preheader -> loop edge**. So the
/// broadcast reads `v` at loop entry, and with no def inside the loop `v` cannot
/// change while the loop runs: every scalar iteration would read exactly the
/// value the broadcast captured. Which of the outside defs produced that value,
/// and whether any single one of them dominates the preheader, is irrelevant —
/// for a NESTED loop (saxpy's case) the value is legitimately redefined by the
/// outer loop between entries, and the broadcast re-executes each time.
///
/// Fail-safe: a value with no def at all (function-entry live-in) returns false,
/// so the loop stays scalar rather than being reasoned about.
fn loop_invariant_vreg(func: &X86ISelFunction, v: VReg, body: &BTreeSet<Block>) -> bool {
    let mut any_def = false;
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            if !x86_produces_value(inst.opcode) {
                continue;
            }
            if matches!(inst.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == v) {
                any_def = true;
                if body.contains(block_id) {
                    return false; // recomputed inside the loop
                }
            }
        }
    }
    any_def
}

/// Find the single-def vreg that holds `Lea r, [StackSlot(slot)]` (the base
/// address of a distinct local allocation). This is the array's base pointer.
fn slot_base_vreg(func: &X86ISelFunction, defs: &DefIndex, slot: u32) -> Option<VReg> {
    let mut found: Option<VReg> = None;
    for block_id in &func.block_order {
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            if inst.opcode != X86Opcode::Lea {
                continue;
            }
            if let (Some(X86ISelOperand::VReg(d)), Some(X86ISelOperand::MemAddr { base, disp })) =
                (inst.operands.first(), inst.operands.get(1))
                && *disp == 0
                && let X86ISelOperand::StackSlot(s) = base.as_ref()
                && *s == slot
            {
                // Must be single-def and unique for this slot.
                if defs.def_inst(func, *d).is_none() || found.is_some() {
                    return None;
                }
                found = Some(*d);
            }
        }
    }
    found
}

// ===========================================================================
// Transform
// ===========================================================================

/// Rewrite: insert a packed vector loop in front of the scalar loop that runs
/// `floor(N/4)` iterations (4 i32 lanes each) sharing the same counter `iv`,
/// then fall into the *unchanged* scalar loop header for the `N % 4` remainder.
///
/// CFG before: `preheader -[jmp]-> header`.
/// CFG after:  `preheader -[jmp]-> VH`;  `VH: iv<vN ? VB : header`;
///             `VB: packed body; iv += 4; -> VH`.
///
/// The scalar loop is untouched; it simply enters with `iv = vN`.
fn apply_plan(func: &mut X86ISelFunction, plan: &VecPlan) {
    let vn = (plan.n_trip / LANES) * LANES;

    // Fresh block ids.
    let vh = Block(next_block_id(func));
    let vb = Block(next_block_id_after(func, vh));

    // Fresh vregs.
    let bound = new_gpr64(func);
    let pa = new_gpr64(func);
    let pb = new_gpr64(func);
    let pc = new_gpr64(func);
    let four = new_gpr64(func);
    let niv = new_gpr64(func);
    let xa = new_fpr128(func);
    let xb = new_fpr128(func);
    let xsum = new_fpr128(func);

    let iv = plan.iv;

    // Vector header VH: iv <u vN ? VB : header.
    let vh_insts = vec![
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![X86ISelOperand::VReg(bound), X86ISelOperand::Imm(vn)],
        ),
        X86ISelInst::new(
            X86Opcode::CmpRR,
            vec![X86ISelOperand::VReg(iv), X86ISelOperand::VReg(bound)],
        ),
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(vb),
            ],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(plan.header)]),
    ];

    // Vector body VB: packed load/op/store over 4 i32 lanes at &slot[iv], iv+=4.
    let sib = |base: VReg, index: VReg| X86ISelOperand::SibMemAddr {
        base: Box::new(X86ISelOperand::VReg(base)),
        index: Box::new(X86ISelOperand::VReg(index)),
        scale: ELEM_SIZE,
        disp: 0,
    };
    let mem = |base: VReg| X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::VReg(base)),
        disp: 0,
    };
    let vb_insts = vec![
        // pa = &lhs[iv]; xa = [pa]
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![X86ISelOperand::VReg(pa), sib(plan.base_lhs, iv)],
        ),
        X86ISelInst::new(X86Opcode::MovdquRM, vec![X86ISelOperand::VReg(xa), mem(pa)]),
        // pb = &rhs[iv]; xb = [pb]
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![X86ISelOperand::VReg(pb), sib(plan.base_rhs, iv)],
        ),
        X86ISelInst::new(X86Opcode::MovdquRM, vec![X86ISelOperand::VReg(xb), mem(pb)]),
        // xsum = xa OP xb  (three-address; downstream two-addresses it)
        X86ISelInst::new(
            plan.packed_op,
            vec![
                X86ISelOperand::VReg(xsum),
                X86ISelOperand::VReg(xa),
                X86ISelOperand::VReg(xb),
            ],
        ),
        // pc = &c[iv]; [pc] = xsum
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![X86ISelOperand::VReg(pc), sib(plan.base_c, iv)],
        ),
        X86ISelInst::new(
            X86Opcode::MovdquMR,
            vec![mem(pc), X86ISelOperand::VReg(xsum)],
        ),
        // iv += 4
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![X86ISelOperand::VReg(four), X86ISelOperand::Imm(LANES)],
        ),
        X86ISelInst::new(
            X86Opcode::AddRR,
            vec![
                X86ISelOperand::VReg(niv),
                X86ISelOperand::VReg(iv),
                X86ISelOperand::VReg(four),
            ],
        ),
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![X86ISelOperand::VReg(iv), X86ISelOperand::VReg(niv)],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(vh)]),
    ];

    // Install the two new blocks.
    func.blocks.insert(
        vh,
        X86ISelBlock {
            insts: vh_insts,
            successors: vec![vb, plan.header],
        },
    );
    func.blocks.insert(
        vb,
        X86ISelBlock {
            insts: vb_insts,
            successors: vec![vh],
        },
    );

    // Redirect the preheader's terminator from `header` to `VH`.
    if let Some(pre) = func.blocks.get_mut(&plan.preheader) {
        for inst in pre.insts.iter_mut() {
            if inst.opcode == X86Opcode::Jmp
                && let Some(X86ISelOperand::Block(t)) = inst.operands.first_mut()
                && *t == plan.header
            {
                *t = vh;
            }
        }
        pre.successors = pre
            .successors
            .iter()
            .map(|s| if *s == plan.header { vh } else { *s })
            .collect();
    }

    // Place VH, VB right after the preheader in the layout order.
    if let Some(pos) = func.block_order.iter().position(|b| *b == plan.preheader) {
        func.block_order.insert(pos + 1, vh);
        func.block_order.insert(pos + 2, vb);
    } else {
        func.block_order.push(vh);
        func.block_order.push(vb);
    }
}

/// Rewrite a fill (`for i in 0..N { a[i] = v }`, `v` const or loop-invariant) to
/// a packed-store loop plus the unchanged scalar remainder.
///
/// The 16-byte broadcast `[v; lanes]` (`lanes = 16 / elem_size`) is built **once**
/// into a fresh scratch stack slot with `lanes` covered width-matched integer
/// stores (`MovMR8`/`MovMR16`/`MovMR32`) and loaded into an XMM with a covered
/// `MOVDQU` load — no broadcast/`PSHUFD`/`MOVD`, so the transform stays entirely
/// within the proof-covered op set. The scratch build lives in a fresh "vector
/// preheader" `VP` that runs **once per loop entry** — so a loop-invariant `v`
/// that differs across *outer* iterations is re-broadcast correctly each entry.
///
/// CFG before: `preheader -[jmp]-> header`.
/// CFG after:  `preheader -[jmp]-> VP`;  `VP: build [v;lanes]; -> VH`;
///             `VH: iv<vN ? VB : header`;  `VB: MOVDQU [&a[iv]]=xmm; iv+=lanes; -> VH`.
///
/// The scalar loop is untouched; it enters with `iv = vN` for the `N % lanes` tail.
fn apply_fill_plan(func: &mut X86ISelFunction, plan: &FillPlan) {
    let elem_size = plan.elem_size as i64;
    let lanes = 16 / elem_size; // 16 (u8) / 8 (u16) / 4 (u32)
    let vn = (plan.n_trip / lanes) * lanes;

    // The covered scalar store opcode matching the element width; a `MOVDQU`
    // fills all `lanes` of the scratch with `lanes` of these stores.
    let store_op = match plan.elem_size {
        1 => X86Opcode::MovMR8,
        2 => X86Opcode::MovMR16,
        _ => X86Opcode::MovMR32, // elem_size == 4 (the recognizer admits only 1/2/4)
    };

    // A fresh, distinct 16-byte scratch slot holds the packed broadcast. Being a
    // brand-new slot, it provably overlaps nothing else; being written and read
    // only here (build then load), the load observes exactly `[v; lanes]`.
    let scratch_slot = func.stack_slots.len() as u32;
    func.stack_slots.push(StackSlotInfo::new(16, 16));

    // Fresh block ids (next_block_id == max+1, so base, base+1, base+2 are all
    // fresh and distinct).
    let base = next_block_id(func);
    let vp = Block(base);
    let vh = Block(base + 1);
    let vb = Block(base + 2);

    // Fresh vregs.
    let rs = new_gpr64(func); // scratch slot base address
    let rk = new_gpr32(func); // the low-`elem_size`-byte value v (or constant K)
    let xconst = new_fpr128(func); // [v; lanes]
    let bound = new_gpr64(func);
    let pc = new_gpr64(func);
    let step = new_gpr64(func);
    let niv = new_gpr64(func);

    let iv = plan.iv;

    let scratch_mem = |disp: i32| X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::VReg(rs)),
        disp,
    };

    // Vector preheader VP: materialize v into `rk`, splat it across the scratch
    // slot with `lanes` width-matched integer stores, then load [v; lanes] once.
    let mut vp_insts = vec![
        // rs = &scratch
        X86ISelInst::new(
            X86Opcode::Lea,
            vec![
                X86ISelOperand::VReg(rs),
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::StackSlot(scratch_slot)),
                    disp: 0,
                },
            ],
        ),
        // rk = v: a constant immediate, or a copy of the loop-invariant vreg.
        // For `Invariant(v)`, `MovRR32` copies v's low 32 bits (which include the
        // low `elem_size` bytes actually stored); v is proven loop-invariant, so
        // this reads the same value the scalar store would on every iteration.
        match plan.fill_value {
            FillValue::Const(k) => X86ISelInst::new(
                X86Opcode::MovRI,
                vec![X86ISelOperand::VReg(rk), X86ISelOperand::Imm(k)],
            ),
            FillValue::Invariant(v) => X86ISelInst::new(
                X86Opcode::MovRR32,
                vec![X86ISelOperand::VReg(rk), X86ISelOperand::VReg(v)],
            ),
        },
    ];
    // scratch[0], scratch[elem_size], ... = low `elem_size` bytes of rk (`lanes`
    // stores, exactly filling the 16-byte scratch).
    for lane in 0..lanes {
        vp_insts.push(X86ISelInst::new(
            store_op,
            vec![
                scratch_mem((lane * elem_size) as i32),
                X86ISelOperand::VReg(rk),
            ],
        ));
    }
    // xconst = [v; lanes]
    vp_insts.push(X86ISelInst::new(
        X86Opcode::MovdquRM,
        vec![X86ISelOperand::VReg(xconst), scratch_mem(0)],
    ));
    vp_insts.push(X86ISelInst::new(
        X86Opcode::Jmp,
        vec![X86ISelOperand::Block(vh)],
    ));

    // Vector header VH: iv <u vN ? VB : header.
    let vh_insts = vec![
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![X86ISelOperand::VReg(bound), X86ISelOperand::Imm(vn)],
        ),
        X86ISelInst::new(
            X86Opcode::CmpRR,
            vec![X86ISelOperand::VReg(iv), X86ISelOperand::VReg(bound)],
        ),
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(vb),
            ],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(plan.header)]),
    ];

    // Vector body VB: packed store of [v; lanes] to &a[iv], iv += lanes. The SIB
    // scale is the element size, so `&a[iv]` steps one element per `iv`; the
    // 16-byte MOVDQU writes exactly `lanes` contiguous elements a[iv..iv+lanes].
    let sib = |base: VReg, index: VReg| X86ISelOperand::SibMemAddr {
        base: Box::new(X86ISelOperand::VReg(base)),
        index: Box::new(X86ISelOperand::VReg(index)),
        scale: plan.elem_size,
        disp: 0,
    };
    let mem = |base: VReg| X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::VReg(base)),
        disp: 0,
    };
    let vb_insts = vec![
        // pc = &a[iv]; [pc] = xconst
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![X86ISelOperand::VReg(pc), sib(plan.base_c, iv)],
        ),
        X86ISelInst::new(
            X86Opcode::MovdquMR,
            vec![mem(pc), X86ISelOperand::VReg(xconst)],
        ),
        // iv += lanes
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![X86ISelOperand::VReg(step), X86ISelOperand::Imm(lanes)],
        ),
        X86ISelInst::new(
            X86Opcode::AddRR,
            vec![
                X86ISelOperand::VReg(niv),
                X86ISelOperand::VReg(iv),
                X86ISelOperand::VReg(step),
            ],
        ),
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![X86ISelOperand::VReg(iv), X86ISelOperand::VReg(niv)],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(vh)]),
    ];

    // Install the three new blocks.
    func.blocks.insert(
        vp,
        X86ISelBlock {
            insts: vp_insts,
            successors: vec![vh],
        },
    );
    func.blocks.insert(
        vh,
        X86ISelBlock {
            insts: vh_insts,
            successors: vec![vb, plan.header],
        },
    );
    func.blocks.insert(
        vb,
        X86ISelBlock {
            insts: vb_insts,
            successors: vec![vh],
        },
    );

    // Redirect the preheader's terminator from `header` to `VP`.
    if let Some(pre) = func.blocks.get_mut(&plan.preheader) {
        for inst in pre.insts.iter_mut() {
            if inst.opcode == X86Opcode::Jmp
                && let Some(X86ISelOperand::Block(t)) = inst.operands.first_mut()
                && *t == plan.header
            {
                *t = vp;
            }
        }
        pre.successors = pre
            .successors
            .iter()
            .map(|s| if *s == plan.header { vp } else { *s })
            .collect();
    }

    // Place VP, VH, VB right after the preheader in the layout order.
    if let Some(pos) = func.block_order.iter().position(|b| *b == plan.preheader) {
        func.block_order.insert(pos + 1, vp);
        func.block_order.insert(pos + 2, vh);
        func.block_order.insert(pos + 3, vb);
    } else {
        func.block_order.push(vp);
        func.block_order.push(vh);
        func.block_order.push(vb);
    }
}

/// Rewrite a RUNTIME-count invariant-pointer byte fill to a guarded packed
/// loop plus the unchanged scalar remainder (see `recognize_runtime_byte_fill_loop`
/// for the full legality argument).
///
/// CFG before: `preheader -[jmp]-> header`.
/// CFG after:  `preheader -[jmp]-> VG`;
///             `VG: n <s 16 ? header : VP`   (guard: no wrap in `n - 15`, and
///                                            at least one full packed iteration)
///             `VP: build [v;16]; bound = n - 15; -> VH`;
///             `VH: iv <s bound ? VB : header`;
///             `VB: MOVDQU [base+iv] = [v;16]; iv += 16; -> VH`.
///
/// `iv <s bound = n - 15` ⟺ `iv <= n - 16` ⟺ `iv + 16 <= n`: every byte the
/// packed store writes is at offset `< n`, i.e. an address the scalar loop
/// itself writes (same value). The scalar loop is untouched; it enters with the
/// partially-advanced `iv` and fills the `< 16`-byte tail. All emitted opcodes
/// (`Lea`/`MovRR32`/`MovMR8`/`MovdquRM`/`MovdquMR`/`MovRI`/`CmpRI`/`CmpRR`/
/// `AddRR`/`MovRR`/`Jcc`/`Jmp`) are the exact proof-covered shapes
/// `apply_fill_plan` already emits.
fn apply_runtime_byte_fill_plan(func: &mut X86ISelFunction, plan: &RuntimeByteFillPlan) {
    const LANES_B: i64 = 16;

    // A fresh, distinct 16-byte scratch slot holds the packed broadcast (brand
    // new ⇒ provably overlaps nothing; written then read only here).
    let scratch_slot = func.stack_slots.len() as u32;
    func.stack_slots.push(StackSlotInfo::new(16, 16));

    // Fresh block ids.
    let first = next_block_id(func);
    let vg = Block(first);
    let vp = Block(first + 1);
    let vh = Block(first + 2);
    let vb = Block(first + 3);

    // Fresh vregs.
    let rs = new_gpr64(func); // scratch slot base address
    let rk = new_gpr32(func); // the low-byte fill value
    let xconst = new_fpr128(func); // [v; 16]
    let mneg = new_gpr64(func); // -15
    let bound = new_gpr64(func); // n - 15
    let pc = new_gpr64(func); // &base[iv]
    let step = new_gpr64(func); // 16
    let niv = new_gpr64(func); // iv + 16

    let iv = plan.iv;

    let scratch_mem = |disp: i32| X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::VReg(rs)),
        disp,
    };

    // Guard VG: `n <s 16` -> scalar header (flags are dead past either target:
    // the strictly-matched header re-compares before any consumer).
    let vg_insts = vec![
        X86ISelInst::new(
            X86Opcode::CmpRI,
            vec![X86ISelOperand::VReg(plan.n), X86ISelOperand::Imm(LANES_B)],
        ),
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::L),
                X86ISelOperand::Block(plan.header),
            ],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(vp)]),
    ];

    // Vector preheader VP: broadcast the invariant value's low byte across the
    // scratch slot (16 covered `MovMR8` stores + one covered `MOVDQU` load —
    // the same mechanism as `apply_fill_plan`), and compute `bound = n - 15`
    // (no wrap: VG proved `n >= 16`).
    let mut vp_insts = vec![
        X86ISelInst::new(
            X86Opcode::Lea,
            vec![
                X86ISelOperand::VReg(rs),
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::StackSlot(scratch_slot)),
                    disp: 0,
                },
            ],
        ),
        X86ISelInst::new(
            X86Opcode::MovRR32,
            vec![X86ISelOperand::VReg(rk), X86ISelOperand::VReg(plan.src)],
        ),
    ];
    for lane in 0..LANES_B {
        vp_insts.push(X86ISelInst::new(
            X86Opcode::MovMR8,
            vec![scratch_mem(lane as i32), X86ISelOperand::VReg(rk)],
        ));
    }
    vp_insts.push(X86ISelInst::new(
        X86Opcode::MovdquRM,
        vec![X86ISelOperand::VReg(xconst), scratch_mem(0)],
    ));
    vp_insts.push(X86ISelInst::new(
        X86Opcode::MovRI,
        vec![
            X86ISelOperand::VReg(mneg),
            X86ISelOperand::Imm(-(LANES_B - 1)),
        ],
    ));
    vp_insts.push(X86ISelInst::new(
        X86Opcode::AddRR,
        vec![
            X86ISelOperand::VReg(bound),
            X86ISelOperand::VReg(plan.n),
            X86ISelOperand::VReg(mneg),
        ],
    ));
    vp_insts.push(X86ISelInst::new(
        X86Opcode::Jmp,
        vec![X86ISelOperand::Block(vh)],
    ));

    // Vector header VH: `iv <s bound` ? VB : scalar header.
    let vh_insts = vec![
        X86ISelInst::new(
            X86Opcode::CmpRR,
            vec![X86ISelOperand::VReg(iv), X86ISelOperand::VReg(bound)],
        ),
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::L),
                X86ISelOperand::Block(vb),
            ],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(plan.header)]),
    ];

    // Vector body VB: `pc = base + iv` (SIB scale 1), packed 16-byte store,
    // `iv += 16`.
    let vb_insts = vec![
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![
                X86ISelOperand::VReg(pc),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(X86ISelOperand::VReg(plan.base)),
                    index: Box::new(X86ISelOperand::VReg(iv)),
                    scale: 1,
                    disp: 0,
                },
            ],
        ),
        X86ISelInst::new(
            X86Opcode::MovdquMR,
            vec![
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::VReg(pc)),
                    disp: 0,
                },
                X86ISelOperand::VReg(xconst),
            ],
        ),
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![X86ISelOperand::VReg(step), X86ISelOperand::Imm(LANES_B)],
        ),
        X86ISelInst::new(
            X86Opcode::AddRR,
            vec![
                X86ISelOperand::VReg(niv),
                X86ISelOperand::VReg(iv),
                X86ISelOperand::VReg(step),
            ],
        ),
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![X86ISelOperand::VReg(iv), X86ISelOperand::VReg(niv)],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(vh)]),
    ];

    // Install the four new blocks.
    func.blocks.insert(
        vg,
        X86ISelBlock {
            insts: vg_insts,
            successors: vec![vp, plan.header],
        },
    );
    func.blocks.insert(
        vp,
        X86ISelBlock {
            insts: vp_insts,
            successors: vec![vh],
        },
    );
    func.blocks.insert(
        vh,
        X86ISelBlock {
            insts: vh_insts,
            successors: vec![vb, plan.header],
        },
    );
    func.blocks.insert(
        vb,
        X86ISelBlock {
            insts: vb_insts,
            successors: vec![vh],
        },
    );

    // Redirect the preheader's terminator from `header` to `VG` (the recognizer
    // proved the preheader ends with exactly `Jmp header`).
    if let Some(pre) = func.blocks.get_mut(&plan.preheader) {
        for inst in pre.insts.iter_mut() {
            if inst.opcode == X86Opcode::Jmp
                && let Some(X86ISelOperand::Block(t)) = inst.operands.first_mut()
                && *t == plan.header
            {
                *t = vg;
            }
        }
        pre.successors = pre
            .successors
            .iter()
            .map(|s| if *s == plan.header { vg } else { *s })
            .collect();
    }

    // Place VG, VP, VH, VB right after the preheader in the layout order.
    if let Some(pos) = func.block_order.iter().position(|b| *b == plan.preheader) {
        func.block_order.insert(pos + 1, vg);
        func.block_order.insert(pos + 2, vp);
        func.block_order.insert(pos + 3, vh);
        func.block_order.insert(pos + 4, vb);
    } else {
        func.block_order.push(vg);
        func.block_order.push(vp);
        func.block_order.push(vh);
        func.block_order.push(vb);
    }
}

/// Rewrite a saxpy / element-wise FMA (`dest[i] = (k*x[i]) (+|-) y[i]`) to a
/// packed loop plus the unchanged scalar remainder.
///
/// The 16-byte broadcast `[k;4]` is built **once per loop entry** into a fresh
/// scratch stack slot with four covered `MovMR32` stores + one covered `MOVDQU`
/// load (no `PSHUFD`/`MOVD`), exactly as `apply_fill_plan` broadcasts a fill
/// value. The packed body then, per iteration: `MOVDQU`-loads `x[iv..iv+4]`,
/// `PMULLD`s it by the broadcast `[k;4]` (packed low-dword multiply = i32
/// wrapping mul per lane), `MOVDQU`-loads `y[iv..iv+4]`, `PADDD`/`PSUBD`s them in
/// the scalar operand order, and `MOVDQU`-stores the result to `dest[iv..iv+4]`.
/// All four packed ops are proof-covered. The loads precede the store, so a
/// `dest` slot that coincides with a source is read before it is overwritten.
///
/// CFG before: `preheader -[jmp]-> header`.
/// CFG after:  `preheader -[jmp]-> VP`;  `VP: build [k;4]; -> VH`;
///             `VH: iv<vN ? VB : header`;  `VB: packed FMA; iv+=4; -> VH`.
///
/// The scalar loop is untouched; it enters with `iv = vN` for the `N % 4` tail.
fn apply_saxpy_plan(func: &mut X86ISelFunction, plan: &SaxpyPlan) {
    let vn = (plan.n_trip / LANES) * LANES;

    // A fresh, distinct 16-byte scratch slot holds the packed `[k;4]` broadcast.
    let scratch_slot = func.stack_slots.len() as u32;
    func.stack_slots.push(StackSlotInfo::new(16, 16));

    // Fresh block ids (all fresh and distinct).
    let base = next_block_id(func);
    let vp = Block(base);
    let vh = Block(base + 1);
    let vb = Block(base + 2);
    let vhu = Block(base + 3);
    let vbu = Block(base + 4);

    // UNROLLED TIER. The single-chunk body spends 5 of its ~16 instructions on
    // loop overhead and recomputes THREE base addresses per chunk; LLVM unrolls
    // this loop 4x and reaches every element through `disp(%rbp,%rdx,4)`.
    // Emitting `UNROLL` chunks per iteration amortizes both: ONE address triple
    // and ONE increment+branch serve all four chunks, which reach their data
    // through constant displacements.
    //
    // Runs while `iv + UNROLL*LANES <= vn`, i.e. `iv < vn - UNROLL*LANES + 1`;
    // the existing single-chunk loop then drains the 0..UNROLL-1 remaining
    // chunks and the scalar loop the `n % LANES` tail. Verified by exhaustion
    // over `n in [1,4200)`: the two vector tiers together cover exactly
    // `[0, vn)` with no gap, no overlap and no access past `vn`, and leave `iv`
    // exactly on `vn` for the scalar tail. Skipped when there is not even one
    // unrolled iteration to run.
    const UNROLL: i64 = 4;
    const CHUNK_BYTES: i64 = LANES * ELEM_SIZE as i64;
    let unrolled = vn >= LANES * UNROLL && vec_unroll_enabled();

    // Fresh vregs.
    let rs = new_gpr64(func); // scratch slot base address
    let rk = new_gpr32(func); // the low-32-bit value k (or constant K)
    let kvec = new_fpr128(func); // [k; 4]
    let bound = new_gpr64(func);
    let px = new_gpr64(func);
    let py = new_gpr64(func);
    let pc = new_gpr64(func);
    let xx = new_fpr128(func); // x[iv..iv+4]
    let xm = new_fpr128(func); // k * x
    let xy = new_fpr128(func); // y[iv..iv+4]
    let xs = new_fpr128(func); // result
    let four = new_gpr64(func);
    let niv = new_gpr64(func);
    // One value set per unrolled chunk. Each chunk's values die before the next
    // chunk's are defined, so peak XMM pressure stays ~4 live plus `kvec`.
    let ux: Vec<[VReg; 4]> = (0..UNROLL)
        .map(|_| {
            [
                new_fpr128(func),
                new_fpr128(func),
                new_fpr128(func),
                new_fpr128(func),
            ]
        })
        .collect();
    let bound_u = new_gpr64(func);
    let upx = new_gpr64(func);
    let upy = new_gpr64(func);
    let upc = new_gpr64(func);
    let ustep = new_gpr64(func);
    let univ = new_gpr64(func);

    let iv = plan.iv;

    let scratch_mem = |disp: i32| X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::VReg(rs)),
        disp,
    };

    // Vector preheader VP: materialize k into `rk`, splat it across the scratch
    // slot with four covered i32 stores, then load [k;4] once.
    let mut vp_insts = vec![
        X86ISelInst::new(
            X86Opcode::Lea,
            vec![
                X86ISelOperand::VReg(rs),
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::StackSlot(scratch_slot)),
                    disp: 0,
                },
            ],
        ),
        // rk = k: a constant immediate, or a copy of the loop-invariant vreg's
        // low 32 bits (which include the i32 the scalar multiply reads).
        match plan.k {
            FillValue::Const(k) => X86ISelInst::new(
                X86Opcode::MovRI,
                vec![X86ISelOperand::VReg(rk), X86ISelOperand::Imm(k)],
            ),
            FillValue::Invariant(v) => X86ISelInst::new(
                X86Opcode::MovRR32,
                vec![X86ISelOperand::VReg(rk), X86ISelOperand::VReg(v)],
            ),
        },
    ];
    for lane in 0..LANES {
        vp_insts.push(X86ISelInst::new(
            X86Opcode::MovMR32,
            vec![
                scratch_mem((lane * ELEM_SIZE as i64) as i32),
                X86ISelOperand::VReg(rk),
            ],
        ));
    }
    vp_insts.push(X86ISelInst::new(
        X86Opcode::MovdquRM,
        vec![X86ISelOperand::VReg(kvec), scratch_mem(0)],
    ));
    vp_insts.push(X86ISelInst::new(
        X86Opcode::Jmp,
        vec![X86ISelOperand::Block(if unrolled { vhu } else { vh })],
    ));

    // Vector header VH: iv <u vN ? VB : header.
    let vh_insts = vec![
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![X86ISelOperand::VReg(bound), X86ISelOperand::Imm(vn)],
        ),
        X86ISelInst::new(
            X86Opcode::CmpRR,
            vec![X86ISelOperand::VReg(iv), X86ISelOperand::VReg(bound)],
        ),
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(vb),
            ],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(plan.header)]),
    ];

    // Vector body VB: packed FMA over 4 i32 lanes at index iv, iv += 4.
    let sib = |base: VReg, index: VReg| X86ISelOperand::SibMemAddr {
        base: Box::new(X86ISelOperand::VReg(base)),
        index: Box::new(X86ISelOperand::VReg(index)),
        scale: ELEM_SIZE,
        disp: 0,
    };
    let mem = |base: VReg| X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::VReg(base)),
        disp: 0,
    };
    // Preserve the scalar operand order for the (order-sensitive) subtract.
    let (op1, op2) = if plan.mul_is_first {
        (xm, xy)
    } else {
        (xy, xm)
    };
    let vb_insts = vec![
        // px = &x[iv]; xx = [px]
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![X86ISelOperand::VReg(px), sib(plan.base_x, iv)],
        ),
        X86ISelInst::new(X86Opcode::MovdquRM, vec![X86ISelOperand::VReg(xx), mem(px)]),
        // xm = xx * kvec  (packed low-dword multiply = i32 wrapping mul per lane)
        X86ISelInst::new(
            X86Opcode::Pmulld,
            vec![
                X86ISelOperand::VReg(xm),
                X86ISelOperand::VReg(xx),
                X86ISelOperand::VReg(kvec),
            ],
        ),
        // py = &y[iv]; xy = [py]
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![X86ISelOperand::VReg(py), sib(plan.base_add, iv)],
        ),
        X86ISelInst::new(X86Opcode::MovdquRM, vec![X86ISelOperand::VReg(xy), mem(py)]),
        // xs = op1 (Paddd|Psubd) op2  (three-address; downstream two-addresses it)
        X86ISelInst::new(
            plan.packed_op,
            vec![
                X86ISelOperand::VReg(xs),
                X86ISelOperand::VReg(op1),
                X86ISelOperand::VReg(op2),
            ],
        ),
        // pc = &dest[iv]; [pc] = xs
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![X86ISelOperand::VReg(pc), sib(plan.base_c, iv)],
        ),
        X86ISelInst::new(X86Opcode::MovdquMR, vec![mem(pc), X86ISelOperand::VReg(xs)]),
        // iv += 4
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![X86ISelOperand::VReg(four), X86ISelOperand::Imm(LANES)],
        ),
        X86ISelInst::new(
            X86Opcode::AddRR,
            vec![
                X86ISelOperand::VReg(niv),
                X86ISelOperand::VReg(iv),
                X86ISelOperand::VReg(four),
            ],
        ),
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![X86ISelOperand::VReg(iv), X86ISelOperand::VReg(niv)],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(vh)]),
    ];

    // Install the three new blocks.
    func.blocks.insert(
        vp,
        X86ISelBlock {
            insts: vp_insts,
            successors: vec![if unrolled { vhu } else { vh }],
        },
    );
    // Unrolled header VHU: iv <u vN - UNROLL*LANES + 1 ? VBU : VH.
    let vhu_insts = vec![
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![
                X86ISelOperand::VReg(bound_u),
                X86ISelOperand::Imm(vn - LANES * UNROLL + 1),
            ],
        ),
        X86ISelInst::new(
            X86Opcode::CmpRR,
            vec![X86ISelOperand::VReg(iv), X86ISelOperand::VReg(bound_u)],
        ),
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(vbu),
            ],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(vh)]),
    ];

    // Unrolled body VBU: ONE address triple, then UNROLL chunks reached by
    // constant displacement, then a single `iv += UNROLL*LANES`.
    let umem = |base: VReg, j: i64| X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::VReg(base)),
        disp: (j * CHUNK_BYTES) as i32,
    };
    let mut vbu_insts = vec![
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![X86ISelOperand::VReg(upx), sib(plan.base_x, iv)],
        ),
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![X86ISelOperand::VReg(upy), sib(plan.base_add, iv)],
        ),
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![X86ISelOperand::VReg(upc), sib(plan.base_c, iv)],
        ),
    ];
    for (j, regs) in ux.iter().enumerate() {
        let (cxx, cxm, cxy, cxs) = (regs[0], regs[1], regs[2], regs[3]);
        let (u1, u2) = if plan.mul_is_first {
            (cxm, cxy)
        } else {
            (cxy, cxm)
        };
        vbu_insts.extend([
            X86ISelInst::new(
                X86Opcode::MovdquRM,
                vec![X86ISelOperand::VReg(cxx), umem(upx, j as i64)],
            ),
            X86ISelInst::new(
                X86Opcode::Pmulld,
                vec![
                    X86ISelOperand::VReg(cxm),
                    X86ISelOperand::VReg(cxx),
                    X86ISelOperand::VReg(kvec),
                ],
            ),
            X86ISelInst::new(
                X86Opcode::MovdquRM,
                vec![X86ISelOperand::VReg(cxy), umem(upy, j as i64)],
            ),
            X86ISelInst::new(
                plan.packed_op,
                vec![
                    X86ISelOperand::VReg(cxs),
                    X86ISelOperand::VReg(u1),
                    X86ISelOperand::VReg(u2),
                ],
            ),
            X86ISelInst::new(
                X86Opcode::MovdquMR,
                vec![umem(upc, j as i64), X86ISelOperand::VReg(cxs)],
            ),
        ]);
    }
    vbu_insts.extend([
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![
                X86ISelOperand::VReg(ustep),
                X86ISelOperand::Imm(LANES * UNROLL),
            ],
        ),
        X86ISelInst::new(
            X86Opcode::AddRR,
            vec![
                X86ISelOperand::VReg(univ),
                X86ISelOperand::VReg(iv),
                X86ISelOperand::VReg(ustep),
            ],
        ),
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![X86ISelOperand::VReg(iv), X86ISelOperand::VReg(univ)],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(vhu)]),
    ]);

    if unrolled {
        func.blocks.insert(
            vhu,
            X86ISelBlock {
                insts: vhu_insts,
                successors: vec![vbu, vh],
            },
        );
        func.blocks.insert(
            vbu,
            X86ISelBlock {
                insts: vbu_insts,
                successors: vec![vhu],
            },
        );
    }
    func.blocks.insert(
        vh,
        X86ISelBlock {
            insts: vh_insts,
            successors: vec![vb, plan.header],
        },
    );
    func.blocks.insert(
        vb,
        X86ISelBlock {
            insts: vb_insts,
            successors: vec![vh],
        },
    );

    // Redirect the preheader's terminator from `header` to `VP`.
    if let Some(pre) = func.blocks.get_mut(&plan.preheader) {
        for inst in pre.insts.iter_mut() {
            if inst.opcode == X86Opcode::Jmp
                && let Some(X86ISelOperand::Block(t)) = inst.operands.first_mut()
                && *t == plan.header
            {
                *t = vp;
            }
        }
        pre.successors = pre
            .successors
            .iter()
            .map(|s| if *s == plan.header { vp } else { *s })
            .collect();
    }

    // Place VP, VH, VB right after the preheader in the layout order.
    let mut placed = vec![vp];
    if unrolled {
        placed.extend([vhu, vbu]);
    }
    placed.extend([vh, vb]);
    if let Some(pos) = func.block_order.iter().position(|b| *b == plan.preheader) {
        for (off, blk) in placed.into_iter().enumerate() {
            func.block_order.insert(pos + 1 + off, blk);
        }
    } else {
        func.block_order.extend(placed);
    }
}

/// Rewrite a recognized i64 saxpy-accumulate loop (see [`SaxpyQPlan`]) to:
///
/// ```text
/// preheader -[jmp]-> VP0                       // was: preheader -> header
/// VP0: rs = &scratch;
///      [rs+0]=K; [rs+8]=K;  xk  = MOVDQU [rs]  // broadcast [K; 2]
///      kh = K >> 32;
///      [rs+0]=kh; [rs+8]=kh; xkh = MOVDQU [rs] // broadcast [K>>32; 2]
///      inv_i = leaf_i * mult_i   (per obligation, wrapping IMUL — the exact
///                                 computation the scalar body performs)
///      -> VC0
/// VC_i: inv_i <u bound_i-(N-1) ? next : header // runtime checks, fail-safe
/// VPB:  pbx = &x[inv_x]; pbc = &c[inv_c]; -> VBU (or VBT / header)
///
/// // group(px,pc,d) = one 2-lane packed body `d` elements past [px]/[pc]:
/// //   xb   = MOVDQU [px + d*8]
/// //   t1   = PMULUDQ(xk, xb)                  // k_lo·b_lo  (64-bit products)
/// //   xbh  = PSRLQ(xb, 32)                    // b_hi
/// //   t2   = PMULUDQ(xk, xbh)                 // k_lo·b_hi
/// //   t3   = PMULUDQ(xkh, xb)                 // k_hi·b_lo
/// //   t5   = PSLLQ(t2 + t3, 32)
/// //   prod = PADDQ(t1, t5)                    // = lo64(K·b) per lane, exact
/// //   xc   = MOVDQU [pc + d*8]
/// //   xs   = PADDQ(xc, prod)                  // (operand order per plan)
/// //   MOVDQU [pc + d*8] = xs
///
/// VBU:  px = &pbx[iv]; pc = &pbc[iv];          // 2x-UNROLLED, BOTTOM-TEST
///       group(px,pc,0); group(px,pc,2);        // two independent chains (ILP)
///       iv += 4;  iv <u vn4 ? VBU : VBT/header  // 1 branch / 4 elements
/// VBT:  px = &pbx[iv]; pc = &pbc[iv];          // single trailing 2-lane group
///       group(px,pc,0); iv += 2; -> header      // only when vn is 2 (mod 4)
/// ```
///
/// `vn = (N/2)*2` is the packed element count and `vn4 = (vn/4)*4` the
/// unrolled portion; VBU is emitted only when `vn4 >= 4` (so its bottom-test
/// is legal by construction — at least one full iteration), and VBT only when
/// `vn - vn4 == 2`. When neither holds (`vn == 0`, impossible since
/// `N >= LANES_Q`) VPB jumps straight to the scalar header. The scalar loop is
/// untouched; the runtime-check failure path and the `N % 2` scalar remainder
/// both enter it with the correct `iv`.
///
/// The K broadcast stays a scratch-slot store/`MOVDQU`-reload: a register-form
/// `MOVQ` + `PUNPCKLQDQ` broadcast would be one fewer round-trip, but
/// `PUNPCKLQDQ` (a shuffle/pack op) has no single-instruction lowering proof
/// (deliberately omitted from `packed_to_proof_query`), so it would fail-close
/// the whole function at proof promotion.
///
/// ⚑ "The broadcast runs once per invocation" — this block previously said
/// that, and it is WRONG. VP0 is the preheader of the INNERMOST (j) loop, so it
/// re-runs for every (i,k) pair. Deriving `[K>>32;2]` in-register with one
/// `PSRLQ` instead of a second scratch round-trip measured **1.09-1.11x on
/// p4_matmul** (paired, interleaved, best/p25/median agreeing) — a
/// once-per-invocation sequence could not possibly pay that. The remaining
/// `[K;2]` broadcast still goes through the scratch slot only because
/// PUNPCKLQDQ is unproven.
///
/// Exactness of the multiply compose, per 64-bit lane (all mod 2^64):
/// `K·b = K_lo·b_lo + 2^32·((K_lo·b_hi + K_hi·b_lo) mod 2^32)`, and
/// `PSLLQ(t2+t3, 32) = 2^32·((t2+t3) mod 2^32)` — bit-for-bit the scalar
/// wrapping IMUL. Unrolling is correctness-preserving: the two groups touch
/// disjoint 16-byte spans of `c` (indices `iv..iv+2` and `iv+2..iv+4`), so
/// even under the `c[f] += k*c[f]` aliasing case each group keeps its own
/// per-iteration read-before-write.
fn apply_saxpyq_plan(func: &mut X86ISelFunction, plan: &SaxpyQPlan) {
    // Packed element count (multiple of LANES_Q=2), and the unrolled-by-2
    // portion (a multiple of 2*LANES_Q = 4). The packed remainder `vn - vn4`
    // is 0 or 2 — a single trailing 2-lane group. Everything is a compile-time
    // constant: the vectorized region is fully straight-line except for the
    // unrolled bottom-test loop, which is emitted ONLY when `vn4 >= 4` so it is
    // entered with at least one full iteration (bottom-test legal by
    // construction — no separate small-`vn` entry guard is needed).
    let vn = (plan.n_trip / LANES_Q) * LANES_Q;
    let unroll = 2i64;
    let group = LANES_Q * unroll; // 4 elements per unrolled iteration
    let vn4 = (vn / group) * group;
    let has_unrolled = vn4 >= group;
    let has_tail = vn > vn4; // 0 or 1 trailing 2-lane group

    // Fresh block ids: VP0, one check block per obligation, VPB, then the
    // vectorized blocks (unrolled loop body VBU, packed tail VBT) as needed.
    // Block ids MUST be contiguous (x86 regalloc replay requires it), so VBU/VBT
    // ids are assigned only for the blocks actually emitted — no gaps.
    let n_checks = plan.obligations.len() as u32;
    let base = next_block_id(func);
    let vp0 = Block(base);
    let check_block = |i: u32| Block(base + 1 + i);
    let vpb = Block(base + 1 + n_checks);
    let mut next_vec_id = base + 2 + n_checks;
    let vbu = Block(next_vec_id); // unrolled bottom-test loop body
    if has_unrolled {
        next_vec_id += 1;
    }
    let vbt = Block(next_vec_id); // single-group packed tail
    // (When !has_unrolled, `vbu` and `vbt` share the id; `vbu` is never emitted,
    //  so no collision — the id is used exactly once, by VBT.)

    // A fresh, distinct 16-byte scratch slot for the two K broadcasts. The
    // register-form broadcast (MOVQ + PUNPCKLQDQ) would be one fewer round-trip
    // but PUNPCKLQDQ has NO single-instruction lowering proof (it is a
    // shuffle/pack op, deliberately omitted from `packed_to_proof_query`), so it
    // would fail-close the whole function at proof promotion. The store/reload
    // path uses only proof-covered MovMR + MovdquRM. The broadcast is once per
    // invocation; the per-iteration win comes from the unroll + bottom-test.
    let scratch_slot = func.stack_slots.len() as u32;
    func.stack_slots.push(StackSlotInfo::new(16, 16));

    // Fresh vregs for the preamble / broadcasts / base pointers.
    let rs = new_gpr64(func); // scratch slot base address
    let kh = new_gpr64(func); // K >> 32
    let xk = new_fpr128(func); // [K; 2]
    let xkh = new_fpr128(func); // [K>>32; 2]
    let pbx = new_gpr64(func); // &x[inv_x]
    let pbc = new_gpr64(func); // &c[inv_c]

    let iv = plan.iv;

    let vr = |v: VReg| X86ISelOperand::VReg(v);
    let scratch_mem = |disp: i32| X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::VReg(rs)),
        disp,
    };
    let sib = |base: VReg, index: VReg| X86ISelOperand::SibMemAddr {
        base: Box::new(X86ISelOperand::VReg(base)),
        index: Box::new(X86ISelOperand::VReg(index)),
        scale: ELEM_SIZE_Q,
        disp: 0,
    };
    // A `[base + disp]` memory operand for the packed loads/stores. Only
    // MovRMSib/MovMRSib/LeaSib may carry a SIB operand, so the group address
    // `pbx + iv*8` is first materialized into a GPR by LeaSib and the per-group
    // 2-element offset (0 or 2 elements = 0/16 bytes) is folded into this plain
    // displacement — a covered MovdquRM/MovdquMR `[reg+disp]` operand form.
    let mem_disp = |base: VReg, disp_elems: i64| X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::VReg(base)),
        disp: (disp_elems * ELEM_SIZE_Q as i64) as i32,
    };

    // VP0: broadcast [K;2] and [K>>32;2] via a scratch-slot store/reload (only
    // proof-covered ops: Lea + MovMR + MovdquRM), then materialize the invariant
    // offsets. NOTE: VP0 is the INNERMOST loop's preheader — it runs once per
    // (i,k), not once per invocation.
    let mut vp0_insts = vec![X86ISelInst::new(
        X86Opcode::Lea,
        vec![
            vr(rs),
            X86ISelOperand::MemAddr {
                base: Box::new(X86ISelOperand::StackSlot(scratch_slot)),
                disp: 0,
            },
        ],
    )];
    for disp in [0, ELEM_SIZE_Q as i32] {
        vp0_insts.push(X86ISelInst::new(
            X86Opcode::MovMR,
            vec![scratch_mem(disp), vr(plan.k)],
        ));
    }
    vp0_insts.push(X86ISelInst::new(
        X86Opcode::MovdquRM,
        vec![vr(xk), scratch_mem(0)],
    ));
    // xkh = [K>>32; 2], derived IN-REGISTER from the [K;2] broadcast above.
    //
    // `xk` already holds two 64-bit lanes each equal to K, so a single
    // logical 64-bit lane shift produces [K>>32; 2] exactly — the same value
    // the scalar `ShrRI kh, K, 32` computes, since both shifts are LOGICAL.
    //
    // ⚑ This replaces a SECOND scratch round-trip (ShrRI + two 8-byte MovMR +
    // one 16-byte MovdquRM). That round-trip stored 8+8 bytes and immediately
    // reloaded them as ONE 16-byte load, which is a guaranteed store-to-load
    // forwarding STALL on this microarchitecture: the load's span is not
    // covered by any single preceding store.
    //
    // ⚑ NO NEW PERIMETER SURFACE. `Psrlq` is already emitted by this very pass
    // (the per-lane `xbh` derivation below), is proof-bound as
    // "V2I64 Ushr uniform immediate -> PSRLQ" and routed through
    // `packed_to_proof_query`. This is NOT the `PUNPCKLQDQ` case described
    // above: that opcode is deliberately omitted from the proof query and would
    // fail-close the function, which is why the [K;2] broadcast itself still
    // goes through the scratch slot.
    //
    // Kill switch `TCG_NO_X86_SAXPYQ_PSRLQ` restores the store/reload so the
    // effect can be A/B'd inside ONE dylib.
    if std::env::var_os("TCG_NO_X86_SAXPYQ_PSRLQ").is_some() {
        vp0_insts.push(X86ISelInst::new(
            X86Opcode::ShrRI,
            vec![vr(kh), vr(plan.k), X86ISelOperand::Imm(32)],
        ));
        for disp in [0, ELEM_SIZE_Q as i32] {
            vp0_insts.push(X86ISelInst::new(
                X86Opcode::MovMR,
                vec![scratch_mem(disp), vr(kh)],
            ));
        }
        vp0_insts.push(X86ISelInst::new(
            X86Opcode::MovdquRM,
            vec![vr(xkh), scratch_mem(0)],
        ));
    } else {
        vp0_insts.push(X86ISelInst::new(
            X86Opcode::Psrlq,
            vec![vr(xkh), vr(xk), X86ISelOperand::Imm(32)],
        ));
    }
    // inv_i = leaf_i * mult_i per obligation — the same wrapping IMUL the scalar
    // body computes, evaluated once at the preheader (every leaf is def-free
    // inside the body, so the value is identical).
    let mut inv_of: Vec<((VReg, i64), VReg)> = Vec::new();
    for (leaf, mult, _) in &plan.obligations {
        let m = new_gpr64(func);
        let inv = new_gpr64(func);
        vp0_insts.push(X86ISelInst::new(
            X86Opcode::MovRI,
            vec![vr(m), X86ISelOperand::Imm(*mult)],
        ));
        vp0_insts.push(X86ISelInst::new(
            X86Opcode::ImulRR,
            vec![vr(inv), vr(*leaf), vr(m)],
        ));
        inv_of.push(((*leaf, *mult), inv));
    }
    let first_check = if n_checks > 0 { check_block(0) } else { vpb };
    vp0_insts.push(X86ISelInst::new(
        X86Opcode::Jmp,
        vec![X86ISelOperand::Block(first_check)],
    ));
    func.blocks.insert(
        vp0,
        X86ISelBlock {
            insts: vp0_insts,
            successors: vec![first_check],
        },
    );

    // VC_i: inv_i <u bound_i - (N-1) ? next : scalar header. A failing check
    // means some elided guard COULD fire (or an access could leave the slot):
    // run the unchanged scalar loop instead. `bound >= n_trip` was verified at
    // recognition, so the check constant is >= 1 and the comparison is a real
    // unsigned range test with no wraparound.
    for (i, ((leaf, mult), inv)) in inv_of.iter().enumerate() {
        let (_, _, ob_bound) = plan
            .obligations
            .iter()
            .find(|(l, m, _)| l == leaf && m == mult)
            .expect("obligation for materialized invariant");
        let check_const = ob_bound - (plan.n_trip - 1);
        let next = if (i as u32) + 1 < n_checks {
            check_block(i as u32 + 1)
        } else {
            vpb
        };
        let limit = new_gpr64(func);
        let insts = vec![
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![vr(limit), X86ISelOperand::Imm(check_const)],
            ),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vr(*inv), vr(limit)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(next),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(plan.header)]),
        ];
        func.blocks.insert(
            check_block(i as u32),
            X86ISelBlock {
                insts,
                successors: vec![next, plan.header],
            },
        );
    }

    // VPB: fold the invariant offsets into the two base pointers, then jump to
    // the first vectorized block (the unrolled loop if present, else the tail,
    // else — vn == 0, impossible since n_trip >= LANES_Q — the scalar header).
    let inv_for = |leaf: VReg, mult: i64| -> VReg {
        inv_of
            .iter()
            .find(|((l, m), _)| *l == leaf && *m == mult)
            .map(|(_, inv)| *inv)
            .expect("access invariant was materialized (obligation-matched)")
    };
    let inv_x = inv_for(plan.leaf_x, plan.mult_x);
    let inv_c = inv_for(plan.leaf_c, plan.mult_c);
    let first_vec = if has_unrolled {
        vbu
    } else if has_tail {
        vbt
    } else {
        plan.header
    };
    let vpb_insts = vec![
        X86ISelInst::new(X86Opcode::LeaSib, vec![vr(pbx), sib(plan.base_x, inv_x)]),
        X86ISelInst::new(X86Opcode::LeaSib, vec![vr(pbc), sib(plan.base_c, inv_c)]),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(first_vec)]),
    ];
    func.blocks.insert(
        vpb,
        X86ISelBlock {
            insts: vpb_insts,
            successors: vec![first_vec],
        },
    );

    // Emit one 2-lane packed group `disp_elems` elements past `[px]`/`[pc]`
    // (the group's x/c base pointers, already `pbx + iv*8` / `pbc + iv*8`).
    // Reads x, multiplies by the broadcast K (PMULUDQ compose — exact per-lane
    // lo64(K*b), identical to the scalar wrapping IMUL), accumulates onto c,
    // stores back. Returns the instruction stream; every temp is fresh so two
    // groups in the same block form independent chains (ILP). PADDQ operand
    // order preserves the scalar `mul_is_first` choice.
    let emit_group =
        |func: &mut X86ISelFunction, px: VReg, pc: VReg, disp_elems: i64| -> Vec<X86ISelInst> {
            let xb = new_fpr128(func);
            let t1 = new_fpr128(func);
            let xbh = new_fpr128(func);
            let t2 = new_fpr128(func);
            let t3 = new_fpr128(func);
            let t4 = new_fpr128(func);
            let t5 = new_fpr128(func);
            let prod = new_fpr128(func);
            let xc = new_fpr128(func);
            let xs = new_fpr128(func);
            let (op1, op2) = if plan.mul_is_first {
                (prod, xc)
            } else {
                (xc, prod)
            };
            vec![
                // xb = x[.. + disp ..+2]
                X86ISelInst::new(X86Opcode::MovdquRM, vec![vr(xb), mem_disp(px, disp_elems)]),
                // prod = lo64(K * xb) per lane (PMULUDQ compose; see fn docs).
                X86ISelInst::new(X86Opcode::Pmuludq, vec![vr(t1), vr(xk), vr(xb)]),
                X86ISelInst::new(
                    X86Opcode::Psrlq,
                    vec![vr(xbh), vr(xb), X86ISelOperand::Imm(32)],
                ),
                X86ISelInst::new(X86Opcode::Pmuludq, vec![vr(t2), vr(xk), vr(xbh)]),
                X86ISelInst::new(X86Opcode::Pmuludq, vec![vr(t3), vr(xkh), vr(xb)]),
                X86ISelInst::new(X86Opcode::Paddq, vec![vr(t4), vr(t2), vr(t3)]),
                X86ISelInst::new(
                    X86Opcode::Psllq,
                    vec![vr(t5), vr(t4), X86ISelOperand::Imm(32)],
                ),
                X86ISelInst::new(X86Opcode::Paddq, vec![vr(prod), vr(t1), vr(t5)]),
                // xs = c[.. + disp ..+2] + prod (scalar operand order kept).
                X86ISelInst::new(X86Opcode::MovdquRM, vec![vr(xc), mem_disp(pc, disp_elems)]),
                X86ISelInst::new(X86Opcode::Paddq, vec![vr(xs), vr(op1), vr(op2)]),
                X86ISelInst::new(X86Opcode::MovdquMR, vec![mem_disp(pc, disp_elems), vr(xs)]),
            ]
        };

    // Advance `iv` by `step` elements: iv = iv + step (fresh imm + add + copy).
    let emit_iv_advance = |func: &mut X86ISelFunction, step: i64| -> Vec<X86ISelInst> {
        let s = new_gpr64(func);
        let niv = new_gpr64(func);
        vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vr(s), X86ISelOperand::Imm(step)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vr(niv), vr(iv), vr(s)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vr(iv), vr(niv)]),
        ]
    };

    // VBU: the unrolled-by-2 BOTTOM-TEST loop over [0, vn4). Two independent
    // 2-lane chains per iteration (group at iv+0 and iv+2 elements), iv += 4,
    // then `iv <u vn4 ? VBU : next`. Entered unconditionally from VPB because
    // vn4 >= 4 guarantees a full first iteration (bottom-test legal by
    // construction). `iv` enters as 0 (the preheader initialization).
    if has_unrolled {
        let after_unroll = if has_tail { vbt } else { plan.header };
        let bound4 = new_gpr64(func);
        let px = new_gpr64(func);
        let pc = new_gpr64(func);
        let mut insts = vec![
            // px = pbx + iv*8, pc = pbc + iv*8 (shared by both unrolled groups).
            X86ISelInst::new(X86Opcode::LeaSib, vec![vr(px), sib(pbx, iv)]),
            X86ISelInst::new(X86Opcode::LeaSib, vec![vr(pc), sib(pbc, iv)]),
        ];
        // Group 0 at iv+0, group 1 at iv+2 elements — independent chains (ILP).
        insts.extend(emit_group(func, px, pc, 0));
        insts.extend(emit_group(func, px, pc, LANES_Q));
        insts.extend(emit_iv_advance(func, group));
        insts.push(X86ISelInst::new(
            X86Opcode::MovRI,
            vec![vr(bound4), X86ISelOperand::Imm(vn4)],
        ));
        insts.push(X86ISelInst::new(X86Opcode::CmpRR, vec![vr(iv), vr(bound4)]));
        insts.push(X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(vbu),
            ],
        ));
        insts.push(X86ISelInst::new(
            X86Opcode::Jmp,
            vec![X86ISelOperand::Block(after_unroll)],
        ));
        func.blocks.insert(
            vbu,
            X86ISelBlock {
                insts,
                successors: vec![vbu, after_unroll],
            },
        );
    }

    // VBT: the single trailing 2-lane group (packed remainder vn - vn4 == 2).
    // Straight-line: one group at `iv`, iv += 2, then fall to the scalar header
    // (which finishes the N % 2 scalar tail from iv == vn).
    if has_tail {
        let px = new_gpr64(func);
        let pc = new_gpr64(func);
        let mut insts = vec![
            X86ISelInst::new(X86Opcode::LeaSib, vec![vr(px), sib(pbx, iv)]),
            X86ISelInst::new(X86Opcode::LeaSib, vec![vr(pc), sib(pbc, iv)]),
        ];
        insts.extend(emit_group(func, px, pc, 0));
        insts.extend(emit_iv_advance(func, LANES_Q));
        insts.push(X86ISelInst::new(
            X86Opcode::Jmp,
            vec![X86ISelOperand::Block(plan.header)],
        ));
        func.blocks.insert(
            vbt,
            X86ISelBlock {
                insts,
                successors: vec![plan.header],
            },
        );
    }

    // Redirect the preheader's terminator from `header` to `VP0`.
    if let Some(pre) = func.blocks.get_mut(&plan.preheader) {
        for inst in pre.insts.iter_mut() {
            if inst.opcode == X86Opcode::Jmp
                && let Some(X86ISelOperand::Block(t)) = inst.operands.first_mut()
                && *t == plan.header
            {
                *t = vp0;
            }
        }
        pre.successors = pre
            .successors
            .iter()
            .map(|s| if *s == plan.header { vp0 } else { *s })
            .collect();
    }

    // Place the new blocks right after the preheader in the layout order.
    let mut new_order: Vec<Block> = vec![vp0];
    for i in 0..n_checks {
        new_order.push(check_block(i));
    }
    new_order.push(vpb);
    if has_unrolled {
        new_order.push(vbu);
    }
    if has_tail {
        new_order.push(vbt);
    }
    if let Some(pos) = func.block_order.iter().position(|b| *b == plan.preheader) {
        for (offset, b) in new_order.into_iter().enumerate() {
            func.block_order.insert(pos + 1 + offset, b);
        }
    } else {
        func.block_order.extend(new_order);
    }
}

/// Rewrite an integer sum-reduction (`for k { acc = acc + a[k] }` or
/// `for k { acc = acc + a[k]*b[k] }`) to a packed **accumulate** loop, a covered
/// **horizontal reduce**, and the unchanged scalar remainder.
///
/// The packed body keeps four independent i32 lane-partials in a loop-carried
/// XMM accumulator `vacc` (initialized to `[0;4]` once, via a fresh 16-byte
/// scratch slot zeroed with four covered `MovMR32` stores + one covered `MOVDQU`
/// load). Per iteration it `MOVDQU`-loads `a[iv..iv+4]` (and, for Dot,
/// `b[iv..iv+4]` and `PMULLD`s them), then `PADDD`s the term into `vacc`. After
/// the packed loop the horizontal-reduce block `VR` `MOVDQU`-stores `vacc` back
/// to the scratch slot and reads the four lanes with covered `MovRM32` loads,
/// sums them with covered `AddRR`s, folds in the carried scalar `acc` (which
/// still holds its pre-loop value), and writes the partial sum back into `acc`.
/// The unchanged scalar loop then adds the `N % 4` tail. Every emitted op is
/// proof-covered — there is **no `PHADDD`/`PSHUFD`/`PTEST`**.
///
/// CFG before: `preheader -[jmp]-> header`.
/// CFG after:  `preheader -[jmp]-> VP`;  `VP: vacc = [0;4]; -> VH`;
///             `VH: iv<vN ? VB : VR`;  `VB: vacc += term(iv); iv+=4; -> VH`;
///             `VR: acc += hsum(vacc); -> header`.
fn apply_reduction_plan(func: &mut X86ISelFunction, plan: &ReducePlan) {
    let vn = (plan.n_trip / LANES) * LANES;

    // A fresh, distinct 16-byte scratch slot: first zeroed to seed `[0;4]`, then
    // reused to spill `vacc` for the covered horizontal reduce. Being brand-new
    // it provably overlaps nothing else.
    let scratch_slot = func.stack_slots.len() as u32;
    func.stack_slots.push(StackSlotInfo::new(16, 16));

    // Fresh block ids (base .. base+3 are all fresh and distinct).
    let base = next_block_id(func);
    let vp = Block(base);
    let vh = Block(base + 1);
    let vb = Block(base + 2);
    let vr = Block(base + 3);

    // Fresh vregs.
    let rs = new_gpr64(func); // scratch slot base address
    let rz = new_gpr32(func); // constant 0 (seed the [0;4] accumulator)
    let vacc = new_fpr128(func); // loop-carried packed lane-partials
    let bound = new_gpr64(func);
    let pa = new_gpr64(func);
    let xa = new_fpr128(func);
    let pb = new_gpr64(func); // Dot only
    let xb = new_fpr128(func); // Dot only
    let xm = new_fpr128(func); // Dot only (a[iv..]*b[iv..])
    let four = new_gpr64(func);
    let niv = new_gpr64(func);
    // Horizontal reduce scalars.
    let s0 = new_gpr32(func);
    let s1 = new_gpr32(func);
    let s2 = new_gpr32(func);
    let s3 = new_gpr32(func);
    let t01 = new_gpr32(func);
    let t23 = new_gpr32(func);
    let tsum = new_gpr32(func);
    let accf = new_gpr32(func);

    let iv = plan.iv;
    let acc = plan.acc;

    let scratch_mem = |disp: i32| X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::VReg(rs)),
        disp,
    };

    // Vector preheader VP: zero the scratch slot and load `[0;4]` into `vacc`.
    let mut vp_insts = vec![
        X86ISelInst::new(
            X86Opcode::Lea,
            vec![
                X86ISelOperand::VReg(rs),
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::StackSlot(scratch_slot)),
                    disp: 0,
                },
            ],
        ),
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![X86ISelOperand::VReg(rz), X86ISelOperand::Imm(0)],
        ),
    ];
    for lane in 0..LANES {
        vp_insts.push(X86ISelInst::new(
            X86Opcode::MovMR32,
            vec![
                scratch_mem((lane * ELEM_SIZE as i64) as i32),
                X86ISelOperand::VReg(rz),
            ],
        ));
    }
    vp_insts.push(X86ISelInst::new(
        X86Opcode::MovdquRM,
        vec![X86ISelOperand::VReg(vacc), scratch_mem(0)],
    ));
    vp_insts.push(X86ISelInst::new(
        X86Opcode::Jmp,
        vec![X86ISelOperand::Block(vh)],
    ));

    // Vector header VH: iv <u vN ? VB : VR.
    let vh_insts = vec![
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![X86ISelOperand::VReg(bound), X86ISelOperand::Imm(vn)],
        ),
        X86ISelInst::new(
            X86Opcode::CmpRR,
            vec![X86ISelOperand::VReg(iv), X86ISelOperand::VReg(bound)],
        ),
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(vb),
            ],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(vr)]),
    ];

    // Vector body VB: accumulate the packed term into `vacc`, iv += 4.
    let sib = |base: VReg, index: VReg| X86ISelOperand::SibMemAddr {
        base: Box::new(X86ISelOperand::VReg(base)),
        index: Box::new(X86ISelOperand::VReg(index)),
        scale: ELEM_SIZE,
        disp: 0,
    };
    let mem = |base: VReg| X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::VReg(base)),
        disp: 0,
    };
    let mut vb_insts = vec![
        // pa = &a[iv]; xa = [pa]
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![X86ISelOperand::VReg(pa), sib(plan.base_a, iv)],
        ),
        X86ISelInst::new(X86Opcode::MovdquRM, vec![X86ISelOperand::VReg(xa), mem(pa)]),
    ];
    let term_vec = match plan.kind {
        ReduceKind::Sum => xa,
        ReduceKind::Dot => {
            // pb = &b[iv]; xb = [pb]; xm = xa * xb (packed low-dword i32 mul).
            vb_insts.push(X86ISelInst::new(
                X86Opcode::LeaSib,
                vec![X86ISelOperand::VReg(pb), sib(plan.base_b, iv)],
            ));
            vb_insts.push(X86ISelInst::new(
                X86Opcode::MovdquRM,
                vec![X86ISelOperand::VReg(xb), mem(pb)],
            ));
            vb_insts.push(X86ISelInst::new(
                X86Opcode::Pmulld,
                vec![
                    X86ISelOperand::VReg(xm),
                    X86ISelOperand::VReg(xa),
                    X86ISelOperand::VReg(xb),
                ],
            ));
            xm
        }
    };
    // vacc = vacc + term  (dst == first source: loop-carried accumulate; the
    // two-address fixup emits `paddd vacc, term` with no extra copy).
    vb_insts.push(X86ISelInst::new(
        X86Opcode::Paddd,
        vec![
            X86ISelOperand::VReg(vacc),
            X86ISelOperand::VReg(vacc),
            X86ISelOperand::VReg(term_vec),
        ],
    ));
    // iv += 4
    vb_insts.push(X86ISelInst::new(
        X86Opcode::MovRI,
        vec![X86ISelOperand::VReg(four), X86ISelOperand::Imm(LANES)],
    ));
    vb_insts.push(X86ISelInst::new(
        X86Opcode::AddRR,
        vec![
            X86ISelOperand::VReg(niv),
            X86ISelOperand::VReg(iv),
            X86ISelOperand::VReg(four),
        ],
    ));
    vb_insts.push(X86ISelInst::new(
        X86Opcode::MovRR,
        vec![X86ISelOperand::VReg(iv), X86ISelOperand::VReg(niv)],
    ));
    vb_insts.push(X86ISelInst::new(
        X86Opcode::Jmp,
        vec![X86ISelOperand::Block(vh)],
    ));

    // Horizontal reduce VR: spill vacc to the scratch slot, sum the four lanes
    // with covered scalar loads + adds, fold in the carried `acc`, write back.
    let vr_insts = vec![
        X86ISelInst::new(
            X86Opcode::MovdquMR,
            vec![scratch_mem(0), X86ISelOperand::VReg(vacc)],
        ),
        X86ISelInst::new(
            X86Opcode::MovRM32,
            vec![X86ISelOperand::VReg(s0), scratch_mem(0)],
        ),
        X86ISelInst::new(
            X86Opcode::MovRM32,
            vec![X86ISelOperand::VReg(s1), scratch_mem(4)],
        ),
        X86ISelInst::new(
            X86Opcode::MovRM32,
            vec![X86ISelOperand::VReg(s2), scratch_mem(8)],
        ),
        X86ISelInst::new(
            X86Opcode::MovRM32,
            vec![X86ISelOperand::VReg(s3), scratch_mem(12)],
        ),
        X86ISelInst::new(
            X86Opcode::AddRR,
            vec![
                X86ISelOperand::VReg(t01),
                X86ISelOperand::VReg(s0),
                X86ISelOperand::VReg(s1),
            ],
        ),
        X86ISelInst::new(
            X86Opcode::AddRR,
            vec![
                X86ISelOperand::VReg(t23),
                X86ISelOperand::VReg(s2),
                X86ISelOperand::VReg(s3),
            ],
        ),
        X86ISelInst::new(
            X86Opcode::AddRR,
            vec![
                X86ISelOperand::VReg(tsum),
                X86ISelOperand::VReg(t01),
                X86ISelOperand::VReg(t23),
            ],
        ),
        // accf = acc + hsum  (fold the carried accumulator, which still holds its
        // pre-loop value — the packed loop never touched `acc`).
        X86ISelInst::new(
            X86Opcode::AddRR,
            vec![
                X86ISelOperand::VReg(accf),
                X86ISelOperand::VReg(acc),
                X86ISelOperand::VReg(tsum),
            ],
        ),
        // acc = accf  (writeback into the loop-carried Gpr32 accumulator vreg —
        // MovRR32 to match its i32 width — so the scalar remainder continues from
        // the vector partial sum).
        X86ISelInst::new(
            X86Opcode::MovRR32,
            vec![X86ISelOperand::VReg(acc), X86ISelOperand::VReg(accf)],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(plan.header)]),
    ];

    // Install the four new blocks.
    func.blocks.insert(
        vp,
        X86ISelBlock {
            insts: vp_insts,
            successors: vec![vh],
        },
    );
    func.blocks.insert(
        vh,
        X86ISelBlock {
            insts: vh_insts,
            successors: vec![vb, vr],
        },
    );
    func.blocks.insert(
        vb,
        X86ISelBlock {
            insts: vb_insts,
            successors: vec![vh],
        },
    );
    func.blocks.insert(
        vr,
        X86ISelBlock {
            insts: vr_insts,
            successors: vec![plan.header],
        },
    );

    // Redirect the preheader's terminator from `header` to `VP`.
    if let Some(pre) = func.blocks.get_mut(&plan.preheader) {
        for inst in pre.insts.iter_mut() {
            if inst.opcode == X86Opcode::Jmp
                && let Some(X86ISelOperand::Block(t)) = inst.operands.first_mut()
                && *t == plan.header
            {
                *t = vp;
            }
        }
        pre.successors = pre
            .successors
            .iter()
            .map(|s| if *s == plan.header { vp } else { *s })
            .collect();
    }

    // Place VP, VH, VB, VR right after the preheader in the layout order.
    if let Some(pos) = func.block_order.iter().position(|b| *b == plan.preheader) {
        func.block_order.insert(pos + 1, vp);
        func.block_order.insert(pos + 2, vh);
        func.block_order.insert(pos + 3, vb);
        func.block_order.insert(pos + 4, vr);
    } else {
        func.block_order.push(vp);
        func.block_order.push(vh);
        func.block_order.push(vb);
        func.block_order.push(vr);
    }
}

// ===========================================================================
// Byte-array sum reduction with WIDENING to a Gpr64 accumulator
// (`for k in 0..N { acc += a[k] as u64 }` over a local `[u8; N]`), lowered to a
// PSADBW byte-sum-accumulate loop (16 bytes/iter) + covered horizontal reduce +
// the unchanged scalar loop as the remainder. Opt-in behind `TCG_X86_BYTE_SUM`.
// ===========================================================================

/// SSE2 lanes for a 128-bit packed byte operation (PSADBW consumes 16 bytes).
const LANES_B: i64 = 16;
/// Byte size of the u8 element type this slice handles.
const ELEM_SIZE_B: u8 = 1;

/// A verified-legal widening byte sum-reduction, ready to be rewritten to a
/// PSADBW-accumulate loop + a covered horizontal reduce + the unchanged scalar
/// loop as the remainder. Every field is established by construction in
/// [`recognize_byte_sum_reduction_loop`].
///
/// # The recognized shape (post-ISel, raw)
///
/// ```text
/// let mut acc: u64 = …;                 // any init (need not be 0)
/// for k in 0..N { acc = acc.wrapping_add(a[k] as u64); }   // a: [u8; N], N const
/// ```
///
/// Body per iteration: `MovRM8 dst32, [&a[k]]` (byte load, addr = `base + k`,
/// stride 1) → `Movzx dst64, dst32` (zero-extend to Gpr64) → `AddRR acc, acc,
/// dst64`. The accumulator `acc` is a loop-carried Gpr64 register read ONLY by
/// the reduction add and initialized outside the loop.
///
/// # Legality by construction (identical discipline to [`ReducePlan`])
///
/// * **Exact reordering.** u64 wrapping-add is associative and commutative, so
///   the PSADBW lane-partials summed in any order equal the sequential sum. Each
///   PSADBW lane sum is ≤ 8·255 = 2040 < 2^16 and, accumulated over ≤ N/16
///   iterations, stays far below 2^64 — no lane overflow, and the final fold is
///   an exact u64 sum. `acc` is read by nothing but the reduction add (full body
///   scan), so no consumer observes a reordered partial sum.
/// * **Packed reads are exactly the scalar reads.** The 16-byte MOVDQU chunks
///   cover indices `[0, floor(N/16)·16)` — byte-for-byte the union of those
///   scalar iterations' 1-byte reads; MOVDQU needs no alignment. The slot holds
///   ≥ N bytes, so every packed read is strictly in-slot.
/// * **Zero stores, unit stride, known trip, in-bounds.** Same trap-guarded
///   bounds discipline as the i32 reduction recognizer; any store/call bails.
/// * **The scalar loop is UNCHANGED** and runs the `N % 16` remainder from
///   `iv = vN` with `acc` pre-loaded with the vector partial.
struct ByteSumPlan {
    iv: VReg,
    acc: VReg,
    n_trip: i64,
    base: VReg,
    slot: u32,
    preheader: Block,
    header: Block,
    /// The reduction sums `popcount(a[i])` rather than `a[i]` itself — the
    /// `acc += (a[i] as uN).count_ones()` shape. The packed form is the same
    /// PSADBW accumulate with a per-byte SWAR population count folded in ahead
    /// of the SAD (see [`swar_popcount_insts`]).
    popcount: bool,
}

/// Kill switch for the UNROLLED saxpy vector body (DEFAULT-ON; opt out with
/// `TCG_NO_X86_VEC_UNROLL`). Exists so the unrolled and single-chunk bodies can
/// be A/B'd against each other inside ONE dylib — the only comparison that
/// means anything here; a cross-sweep delta is not evidence.
///
/// ⚑ It has already earned that keep. The same unrolled-tier pattern was
/// applied to the runtime byte-FILL loop on the assumption that a fill, having
/// no loads, is the cheapest thing to unroll. Emission was exactly as intended
/// (10 instructions per 64 bytes, down from ~24), and the paired A/B this
/// switch enabled measured `v2_memfill` at **2.685x -> 5.234x of LLVM — two
/// times SLOWER**. That change was reverted. Do not re-apply unrolling to the
/// fill tier without measuring it the same way; the instruction count improves
/// and the program gets worse.
fn vec_unroll_enabled() -> bool {
    crate::env_lock::var_os("TCG_NO_X86_VEC_UNROLL").is_none()
}

/// Kill switch for the byte-sum PSADBW reduction tier (DEFAULT-ON; opt out with
/// `TCG_NO_X86_BYTE_SUM`). Flipped default-on once `Psadbw` became a PROVEN,
/// coverage-covered opcode (the `PsadbwByteSad` reconstruction: `encode_psadbw`
/// verified equal to the independent `encode_trust_ir_byte_sad`; coverage gate
/// accepts 160/189 denominator rows, with the 29 named RED rows pinned as
/// explicit debt), so the emitted `PSADBW` survives proofs-ON. Validated by a
/// byte-sum differential fuzz (30 programs across lengths + non-multiple-of-16
/// tails) + the 18-bench suite, all checksum-identical to LLVM O3; the
/// recognizer fires only on genuinely memory-backed byte-array sum loops and
/// falls back to the scalar loop everywhere else. `TCG_X86_BYTE_SUM` is still
/// accepted as a (now-redundant) force-on for A/B scripts.
fn byte_sum_enabled() -> bool {
    crate::env_lock::var_os("TCG_NO_X86_BYTE_SUM").is_none()
}

/// Does `v` provably hold the zero-extended byte loaded into `load`?
///
/// Walks back through copies and through masks that cannot change the low byte.
/// The mask step is load-bearing: rustc keeps the `as u32` truncation in
/// `(a[i] as u32).count_ones()`, so the chain the backend actually sees is
///
/// ```text
///   MovRM8 b ; Movzx z, b ; MovRI k, 0xffff_ffff ; AndRR m, z, k ; Popcnt p, m
/// ```
///
/// `z` is already in `[0, 255]`, so ANDing it with any constant whose eight low
/// bits are all set is the identity — and therefore leaves both the value and
/// its population count untouched. Any other mask, or any other opcode, ends
/// the walk with `false`.
fn traces_to_zero_extended_byte(
    func: &X86ISelFunction,
    defs: &DefIndex,
    v: VReg,
    load: VReg,
) -> bool {
    // A constant operand whose low byte is all ones (`k & 0xff == 0xff`).
    let low_byte_preserving_const = |r: VReg| -> bool {
        let Some(d) = defs.def_inst(func, canon(func, defs, r)) else {
            return false;
        };
        d.opcode == X86Opcode::MovRI
            && matches!(d.operands.get(1), Some(X86ISelOperand::Imm(k)) if k & 0xff == 0xff)
    };

    let mut cur = v;
    for _ in 0..8 {
        let c = canon(func, defs, cur);
        let Some(def) = defs.def_inst(func, c) else {
            return false;
        };
        match def.opcode {
            X86Opcode::Movzx => {
                return matches!(def.operands.get(1),
                    Some(X86ISelOperand::VReg(s)) if canon(func, defs, *s) == load);
            }
            X86Opcode::AndRR => {
                let (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) =
                    (def.operands.get(1), def.operands.get(2))
                else {
                    return false;
                };
                if low_byte_preserving_const(*y) {
                    cur = *x;
                } else if low_byte_preserving_const(*x) {
                    cur = *y;
                } else {
                    return false;
                }
            }
            X86Opcode::AndRI => {
                let (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::Imm(k))) =
                    (def.operands.get(1), def.operands.get(2))
                else {
                    return false;
                };
                if k & 0xff != 0xff {
                    return false;
                }
                cur = *x;
            }
            _ => return false,
        }
    }
    false
}

/// Recognizer for the widening byte sum-reduction shape (see [`ByteSumPlan`]).
/// Returns a legal plan, or `None` for anything else. Structurally a
/// byte-width clone of [`recognize_reduction_loop`]: the load is a `MovRM8`
/// (stride-1 `&a[iv]`) widened by a `Movzx` to Gpr64, and the accumulator is
/// Gpr64.
fn recognize_byte_sum_reduction_loop(
    func: &X86ISelFunction,
    preds: &HashMap<Block, Vec<Block>>,
    idom: &HashMap<Block, Block>,
    lp: &LoopInfo,
) -> Option<ByteSumPlan> {
    if !byte_sum_enabled() {
        return None;
    }
    let header = lp.header;
    let latch = lp.latch;
    let body = &lp.body;
    let preheader = lp.preheader?;
    let _ = idom;

    for block_id in body {
        let block = func.blocks.get(block_id)?;
        if block.insts.iter().any(|i| i.opcode == X86Opcode::Phi) {
            return None;
        }
    }

    let defs = DefIndex::build(func);
    let mut memo: HashMap<VReg, Prov> = HashMap::new();

    // 1. IV + trip count from the header. Need a full 16-byte vector iteration.
    let (iv, n_trip) = recognize_header(func, &defs, header, body)?;
    if n_trip < LANES_B {
        return None;
    }

    // 2-3. Linear body chain with trap-guarded off-chain edges (identical
    //      discipline to the i32 reduction recognizer).
    let header_succs = &func.blocks.get(&header)?.successors;
    let body_entry = unique_in_body_succ(header_succs, body)?;
    let mut chain: Vec<Block> = Vec::new();
    let mut visited: HashSet<Block> = HashSet::new();
    let mut cur = body_entry;
    loop {
        if !body.contains(&cur) || !visited.insert(cur) {
            return None;
        }
        chain.push(cur);
        let succs = &func.blocks.get(&cur)?.successors;
        let mut has_trap_edge = false;
        for s in succs {
            if body.contains(s) {
                continue;
            }
            if !is_pure_trap_block(func, *s) {
                return None;
            }
            has_trap_edge = true;
        }
        if has_trap_edge && !block_has_iv_bound_compare(func, &defs, iv, &mut memo, cur, n_trip) {
            return None;
        }
        if cur == latch {
            break;
        }
        cur = unique_in_body_succ(succs, body)?;
    }
    if unique_in_body_succ(&func.blocks.get(&latch)?.successors, body)? != header {
        return None;
    }
    for block_id in body {
        if *block_id != header && !visited.contains(block_id) {
            return None;
        }
    }
    {
        let hsuccs = &func.blocks.get(&header)?.successors;
        let non_body: Vec<Block> = hsuccs
            .iter()
            .copied()
            .filter(|s| !body.contains(s))
            .collect();
        if non_body.len() != 1 {
            return None;
        }
        let empty = Vec::new();
        let hpreds = preds.get(&header).unwrap_or(&empty);
        let non_body_preds: Vec<Block> = hpreds
            .iter()
            .copied()
            .filter(|p| !body.contains(p))
            .collect();
        if non_body_preds != vec![preheader] {
            return None;
        }
    }

    // 4. Collect memory ops: exactly ONE `MovRM8` byte load from `&slot[iv]`
    //    (stride-1 ElemAddr), widened by exactly ONE `Movzx dst64, dst32`.
    //    ZERO stores, no call. Only byte-sum-relevant opcodes in the body.
    let mut byte_load: Option<(VReg, u32)> = None; // (dst32, slot)
    let mut popcnt: Option<(VReg, VReg)> = None; // (dst, src) of the lone POPCNT
    for block_id in &chain {
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            let op = inst.opcode;
            if op == X86Opcode::Call || op == X86Opcode::CallR || op == X86Opcode::CallM {
                return None;
            }
            if is_load_opcode(op) {
                if op != X86Opcode::MovRM8 {
                    return None; // only a byte load is admitted.
                }
                let dst = match inst.operands.first() {
                    Some(X86ISelOperand::VReg(d)) => *d,
                    _ => return None,
                };
                let slot = elem_addr_slot(
                    func,
                    &defs,
                    iv,
                    &mut memo,
                    inst.operands.get(1),
                    ELEM_SIZE_B as i64,
                )?;
                if byte_load.is_some() {
                    return None; // more than one load — not a plain byte sum.
                }
                byte_load = Some((dst, slot));
            } else if is_store_opcode(op) {
                return None;
            } else if op == X86Opcode::TrapBoundsCheckExact {
                // Inline proof-only bounds-check carrier. Admit it only when it
                // provably never traps for iv in [0, n_trip) — index==iv and
                // bound>=n_trip. The packed loop omits it (accesses proven
                // in-slot below); the scalar remainder keeps it.
                if !is_safe_iv_bounds_carrier(func, &defs, iv, &mut memo, inst, n_trip) {
                    return None;
                }
            } else if op == X86Opcode::Popcnt {
                // Admitted ONLY as the `count_ones()` step of a popcount-sum,
                // and only ever one of them: step 5b requires this exact
                // instruction to sit between the zero-extended byte and the
                // accumulator, so a second POPCNT (or one off the reduction
                // chain) has no packed image and must bail.
                if popcnt.is_some() {
                    return None;
                }
                let (Some(X86ISelOperand::VReg(d)), Some(X86ISelOperand::VReg(s))) =
                    (inst.operands.first(), inst.operands.get(1))
                else {
                    return None;
                };
                popcnt = Some((*d, *s));
            } else if op != X86Opcode::Movzx && !is_whitelisted_body_opcode(op) {
                return None;
            }
        }
    }
    let (load_dst, slot) = byte_load?;

    // 5. Find the widening `Movzx wide64, load_dst` (Gpr64 zero-extend).
    let mut widened: Option<VReg> = None;
    for block_id in &chain {
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            if inst.opcode != X86Opcode::Movzx {
                continue;
            }
            if let (Some(X86ISelOperand::VReg(d)), Some(X86ISelOperand::VReg(s))) =
                (inst.operands.first(), inst.operands.get(1))
                && canon(func, &defs, *s) == canon(func, &defs, load_dst)
                && d.class == RegClass::Gpr64
            {
                if widened.is_some() {
                    return None;
                }
                widened = Some(*d);
            }
        }
    }
    // 5b. Pick the reduction term. A direct Gpr64 widening of the loaded byte
    //     is the plain byte sum. Failing that, admit exactly one further
    //     shape — a POPCOUNT sum:
    //
    //         MovRM8 b, [&a[iv]] ; Movzx z, b ; Popcnt p, z ; acc += p
    //
    //     The `Movzx` is load-bearing: it is what makes every bit above the
    //     loaded byte provably zero, so `popcount(z) == popcount(a[iv])` and
    //     the packed image may treat the chunk as 16 independent bytes. A loop
    //     carrying BOTH shapes is not claimed by this recognizer.
    let (wide, popcount) = match (widened, popcnt) {
        (Some(_), Some(_)) => return None,
        (Some(w), None) => (canon(func, &defs, w), false),
        (None, Some((pd, ps))) => {
            if pd.class != RegClass::Gpr64 {
                return None;
            }
            let load = canon(func, &defs, load_dst);
            if !traces_to_zero_extended_byte(func, &defs, ps, load) {
                return None;
            }
            (canon(func, &defs, pd), true)
        }
        (None, None) => return None,
    };

    // 6. Find the loop-carried Gpr64 accumulator whose back-edge writeback is
    //    `MovRR acc, acc_new` with `acc_new = AddRR(acc, wide)`. `acc` must have
    //    a def outside the body (its init) and not be the IV.
    let mut found: Option<(VReg, (Block, usize))> = None; // (acc, add loc)
    for block_id in &chain {
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            if inst.opcode != X86Opcode::MovRR {
                continue;
            }
            let (acc, raw_src) = match (inst.operands.first(), inst.operands.get(1)) {
                (Some(X86ISelOperand::VReg(d)), Some(X86ISelOperand::VReg(s))) => (*d, *s),
                _ => continue,
            };
            if acc == iv || acc.class != RegClass::Gpr64 {
                continue;
            }
            let acc_new = canon(func, &defs, raw_src);
            let Some((add_block, add_idx)) = defs.single.get(&acc_new).copied() else {
                continue;
            };
            let add = func.blocks.get(&add_block)?.insts.get(add_idx)?;
            if add.opcode != X86Opcode::AddRR {
                continue;
            }
            let (x, y) = match (add.operands.get(1), add.operands.get(2)) {
                (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => (*x, *y),
                _ => continue,
            };
            let (cx, cy) = (canon(func, &defs, x), canon(func, &defs, y));
            // term must be the widened byte; the other addend must be `acc`.
            let term_ok = (cx == acc && cy == wide) || (cy == acc && cx == wide);
            if !term_ok {
                continue;
            }
            let has_outside_def = func.block_order.iter().any(|b| {
                !body.contains(b)
                    && func
                        .blocks
                        .get(b)
                        .map(|blk| {
                            blk.insts.iter().any(|i| {
                                x86_produces_value(i.opcode)
                                    && matches!(i.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == acc)
                            })
                        })
                        .unwrap_or(false)
            });
            if !has_outside_def {
                continue;
            }
            if found.is_some() {
                return None;
            }
            found = Some((acc, (add_block, add_idx)));
        }
    }
    let (acc, add_loc) = found?;

    // 7. `acc` is read ONLY by the reduction add anywhere in the loop body.
    for block_id in body {
        let block = func.blocks.get(block_id)?;
        for (idx, inst) in block.insts.iter().enumerate() {
            if (*block_id, idx) == add_loc {
                continue;
            }
            let produces = x86_produces_value(inst.opcode);
            for (opi, op) in inst.operands.iter().enumerate() {
                if produces && opi == 0 {
                    continue;
                }
                if operand_references_vreg(op, acc) {
                    return None;
                }
            }
        }
    }

    // 8. The slot must hold >= N bytes so every packed access stays in-slot.
    let info = func.stack_slots.get(slot as usize)?;
    if (info.size as i64) < n_trip {
        return None;
    }

    // 9. Resolve the slot to its base-address vreg.
    let base = slot_base_vreg(func, &defs, slot)?;

    Some(ByteSumPlan {
        iv,
        acc,
        n_trip,
        base,
        slot,
        preheader,
        header,
        popcount,
    })
}

/// Per-byte SWAR population count of `x`: on return `tmp[8]` holds, in each of
/// its 16 bytes, the number of set bits in the corresponding byte of `x`.
/// `masks` are the broadcast constants `[0x55555555, 0x33333333, 0x0f0f0f0f]`.
///
/// The classic three-step reduction, applied to every byte at once:
///
/// ```text
///   v -= (v >> 1) & 0x55                  // 16 x 2-bit pair counts
///   v  = (v & 0x33) + ((v >> 2) & 0x33)   // 8 x 4-bit nibble counts
///   v  = (v + (v >> 4)) & 0x0f            // 4 x 8-bit byte counts
/// ```
///
/// **Why PSRLD is exact here even though it shifts 32-bit lanes, not bytes.**
/// Each shift also drags bits down across a byte boundary; every one of those
/// bits is then discarded:
///
/// * `>> 1` moves bit 8 into bit 7, and `0x55 = 0b0101_0101` clears bit 7.
/// * `>> 2` moves bits 8-9 into bits 6-7, and `0x33 = 0b0011_0011` clears both.
/// * `>> 4` moves bits 8-11 into bits 4-7 — the HIGH nibble — while the sum
///   being formed lives in the LOW nibble. That sum is at most `4 + 4 = 8`, so
///   it cannot carry out of the low nibble, and the final `& 0x0f` discards the
///   high nibble outright.
///
/// PSUBB/PADDB are byte-wise, so no borrow or carry crosses a byte either.
/// Consequently no lane-crossing shuffle is needed, and the sequence uses only
/// opcodes the perimeter already proves: PSRLD, PAND, PSUBB, PADDB.
fn swar_popcount_insts(x: VReg, masks: &[VReg; 3], tmp: &[VReg; 10]) -> Vec<X86ISelInst> {
    let vr = X86ISelOperand::VReg;
    let imm = X86ISelOperand::Imm;
    let (m55, m33, m0f) = (masks[0], masks[1], masks[2]);
    vec![
        // step 1: v -= (v >> 1) & 0x55
        X86ISelInst::new(X86Opcode::Psrld, vec![vr(tmp[0]), vr(x), imm(1)]),
        X86ISelInst::new(X86Opcode::Pand, vec![vr(tmp[1]), vr(tmp[0]), vr(m55)]),
        X86ISelInst::new(X86Opcode::Psubb, vec![vr(tmp[2]), vr(x), vr(tmp[1])]),
        // step 2: v = (v & 0x33) + ((v >> 2) & 0x33)
        X86ISelInst::new(X86Opcode::Pand, vec![vr(tmp[3]), vr(tmp[2]), vr(m33)]),
        X86ISelInst::new(X86Opcode::Psrld, vec![vr(tmp[4]), vr(tmp[2]), imm(2)]),
        X86ISelInst::new(X86Opcode::Pand, vec![vr(tmp[5]), vr(tmp[4]), vr(m33)]),
        X86ISelInst::new(X86Opcode::Paddb, vec![vr(tmp[6]), vr(tmp[3]), vr(tmp[5])]),
        // step 3: v = (v + (v >> 4)) & 0x0f
        X86ISelInst::new(X86Opcode::Psrld, vec![vr(tmp[7]), vr(tmp[6]), imm(4)]),
        X86ISelInst::new(X86Opcode::Paddb, vec![vr(tmp[8]), vr(tmp[6]), vr(tmp[7])]),
        X86ISelInst::new(X86Opcode::Pand, vec![vr(tmp[9]), vr(tmp[8]), vr(m0f)]),
    ]
}

/// Rewrite a widening byte sum-reduction to a PSADBW-accumulate loop (16
/// bytes/iter), a covered horizontal reduce of the two u64 lane-partials, and
/// the unchanged scalar loop as the `N % 16` remainder. CFG mirrors
/// [`apply_reduction_plan`]: `preheader -> VP -> VH -> {VB -> VH | VR ->
/// header}`.
fn apply_byte_sum_plan(func: &mut X86ISelFunction, plan: &ByteSumPlan) {
    let _ = plan.slot;
    let vn = (plan.n_trip / LANES_B) * LANES_B;

    // Fresh 16-byte scratch slot: zeroed to seed the [0;2] accumulator and the
    // PSADBW zero operand, then reused to spill `vacc` for the horizontal reduce.
    let scratch_slot = func.stack_slots.len() as u32;
    func.stack_slots.push(StackSlotInfo::new(16, 16));

    let base_id = next_block_id(func);
    let vp = Block(base_id);
    let vh = Block(base_id + 1);
    let vb = Block(base_id + 2);
    let vrb = Block(base_id + 3);

    let rs = new_gpr64(func); // scratch slot base
    let rz = new_gpr32(func); // constant 0
    let vacc = new_fpr128(func); // loop-carried packed u64 lane-partials
    let xzero = new_fpr128(func); // all-zero operand for PSADBW
    let bound = new_gpr64(func);
    let pe = new_gpr64(func); // &a[iv]
    let xchunk = new_fpr128(func); // 16 raw bytes
    let xsad = new_fpr128(func); // per-chunk two-lane byte sums
    let sixteen = new_gpr64(func);
    let niv = new_gpr64(func);
    let s0 = new_gpr64(func);
    let s1 = new_gpr64(func);
    let t01 = new_gpr64(func);
    let accf = new_gpr64(func);

    // Popcount tier only: three loop-invariant broadcast SWAR masks, the GPRs
    // that seed them through the scratch slot, and the in-loop reduction
    // temporaries. Left unused (so never emitted) for a plain byte sum.
    let masks = [new_fpr128(func), new_fpr128(func), new_fpr128(func)];
    let mask_seeds = [new_gpr32(func), new_gpr32(func), new_gpr32(func)];
    let pc_tmp: [VReg; 10] = std::array::from_fn(|_| new_fpr128(func));

    let iv = plan.iv;
    let acc = plan.acc;
    let vr = |v: VReg| X86ISelOperand::VReg(v);
    let scratch_mem = |disp: i32| X86ISelOperand::MemAddr {
        base: Box::new(vr(rs)),
        disp,
    };

    // VP: zero the scratch slot; seed vacc = [0;2] and xzero = 0 from it.
    let mut vp_insts = vec![
        X86ISelInst::new(
            X86Opcode::Lea,
            vec![
                vr(rs),
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::StackSlot(scratch_slot)),
                    disp: 0,
                },
            ],
        ),
        X86ISelInst::new(X86Opcode::MovRI, vec![vr(rz), X86ISelOperand::Imm(0)]),
    ];
    for lane in 0..(16 / ELEM_SIZE as i64) {
        vp_insts.push(X86ISelInst::new(
            X86Opcode::MovMR32,
            vec![scratch_mem((lane * ELEM_SIZE as i64) as i32), vr(rz)],
        ));
    }
    vp_insts.push(X86ISelInst::new(
        X86Opcode::MovdquRM,
        vec![vr(vacc), scratch_mem(0)],
    ));
    vp_insts.push(X86ISelInst::new(
        X86Opcode::MovdquRM,
        vec![vr(xzero), scratch_mem(0)],
    ));
    // Popcount tier: broadcast each 32-bit SWAR mask to all four lanes through
    // the same scratch slot, once, outside the loop. VR rewrites the slot from
    // `vacc` before reading it back, so the reuse is safe.
    if plan.popcount {
        for ((mask, seed), pattern) in
            masks
                .iter()
                .zip(mask_seeds.iter())
                .zip([0x5555_5555_i64, 0x3333_3333, 0x0f0f_0f0f])
        {
            vp_insts.push(X86ISelInst::new(
                X86Opcode::MovRI,
                vec![vr(*seed), X86ISelOperand::Imm(pattern)],
            ));
            for lane in 0..(16 / ELEM_SIZE as i64) {
                vp_insts.push(X86ISelInst::new(
                    X86Opcode::MovMR32,
                    vec![scratch_mem((lane * ELEM_SIZE as i64) as i32), vr(*seed)],
                ));
            }
            vp_insts.push(X86ISelInst::new(
                X86Opcode::MovdquRM,
                vec![vr(*mask), scratch_mem(0)],
            ));
        }
    }
    vp_insts.push(X86ISelInst::new(
        X86Opcode::Jmp,
        vec![X86ISelOperand::Block(vh)],
    ));

    // VH: iv <u vN ? VB : VR.
    let vh_insts = vec![
        X86ISelInst::new(X86Opcode::MovRI, vec![vr(bound), X86ISelOperand::Imm(vn)]),
        X86ISelInst::new(X86Opcode::CmpRR, vec![vr(iv), vr(bound)]),
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(vb),
            ],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(vrb)]),
    ];

    // VB: pe = &a[iv]; xchunk = [pe]; xsad = SAD(bytes, 0); vacc += xsad; iv += 16.
    let mut vb_insts = vec![
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![
                vr(pe),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(vr(plan.base)),
                    index: Box::new(vr(iv)),
                    scale: ELEM_SIZE_B,
                    disp: 0,
                },
            ],
        ),
        X86ISelInst::new(
            X86Opcode::MovdquRM,
            vec![
                vr(xchunk),
                X86ISelOperand::MemAddr {
                    base: Box::new(vr(pe)),
                    disp: 0,
                },
            ],
        ),
    ];
    // A popcount sum reduces each byte to its own population count first; SAD
    // then sums those exactly as it sums raw bytes.
    let sad_src = if plan.popcount {
        vb_insts.extend(swar_popcount_insts(xchunk, &masks, &pc_tmp));
        pc_tmp[9]
    } else {
        xchunk
    };
    vb_insts.extend([
        X86ISelInst::new(X86Opcode::Psadbw, vec![vr(xsad), vr(sad_src), vr(xzero)]),
        X86ISelInst::new(X86Opcode::Paddq, vec![vr(vacc), vr(vacc), vr(xsad)]),
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![vr(sixteen), X86ISelOperand::Imm(LANES_B)],
        ),
        X86ISelInst::new(X86Opcode::AddRR, vec![vr(niv), vr(iv), vr(sixteen)]),
        X86ISelInst::new(X86Opcode::MovRR, vec![vr(iv), vr(niv)]),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(vh)]),
    ]);

    // VR: horizontal reduce the two u64 lanes, fold into the carried `acc`.
    let vr_insts = vec![
        X86ISelInst::new(X86Opcode::MovdquMR, vec![scratch_mem(0), vr(vacc)]),
        X86ISelInst::new(X86Opcode::MovRM, vec![vr(s0), scratch_mem(0)]),
        X86ISelInst::new(
            X86Opcode::MovRM,
            vec![vr(s1), scratch_mem(ELEM_SIZE_Q as i32)],
        ),
        X86ISelInst::new(X86Opcode::AddRR, vec![vr(t01), vr(s0), vr(s1)]),
        X86ISelInst::new(X86Opcode::AddRR, vec![vr(accf), vr(acc), vr(t01)]),
        X86ISelInst::new(X86Opcode::MovRR, vec![vr(acc), vr(accf)]),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(plan.header)]),
    ];

    func.blocks.insert(
        vp,
        X86ISelBlock {
            insts: vp_insts,
            successors: vec![vh],
        },
    );
    func.blocks.insert(
        vh,
        X86ISelBlock {
            insts: vh_insts,
            successors: vec![vb, vrb],
        },
    );
    func.blocks.insert(
        vb,
        X86ISelBlock {
            insts: vb_insts,
            successors: vec![vh],
        },
    );
    func.blocks.insert(
        vrb,
        X86ISelBlock {
            insts: vr_insts,
            successors: vec![plan.header],
        },
    );

    if let Some(pre) = func.blocks.get_mut(&plan.preheader) {
        for inst in pre.insts.iter_mut() {
            if inst.opcode == X86Opcode::Jmp
                && let Some(X86ISelOperand::Block(t)) = inst.operands.first_mut()
                && *t == plan.header
            {
                *t = vp;
            }
        }
        pre.successors = pre
            .successors
            .iter()
            .map(|s| if *s == plan.header { vp } else { *s })
            .collect();
    }

    if let Some(pos) = func.block_order.iter().position(|b| *b == plan.preheader) {
        func.block_order.insert(pos + 1, vp);
        func.block_order.insert(pos + 2, vh);
        func.block_order.insert(pos + 3, vb);
        func.block_order.insert(pos + 4, vrb);
    } else {
        func.block_order.push(vp);
        func.block_order.push(vh);
        func.block_order.push(vb);
        func.block_order.push(vrb);
    }
}

// ===========================================================================
// Kernighan popcount idiom -> constant-time SWAR (a scalar loop-idiom win)
// `let mut c=0; while x != 0 { x &= x-1; c += 1; }`  ==>  `c += popcount(x)`
// via the branch-free 5-step SWAR sequence (the same one `u64::count_ones()`
// lowers to). BOTH LLVM and tcg otherwise compile the manual loop AS a
// data-dependent ~popcount(x)-iteration loop, so replacing it with the constant
// SWAR is a WIN (beats LLVM). Opt-in behind `TCG_X86_POPCOUNT_IDIOM`.
// ===========================================================================

/// Kill switch for the Kernighan-popcount SWAR idiom tier (DEFAULT-ON; opt out
/// with `TCG_NO_X86_POPCOUNT_IDIOM`). Emits only already-PROVEN scalar ops
/// (MovRI/ShrRI/AndRR/SubRR/AddRR/ImulRR/MovRR32), so it needs NO new proof and
/// survives proofs-ON. Default-on because BOTH compilers otherwise compile the
/// manual Kernighan loop as a ~popcount(x)-iteration data-dependent loop, so the
/// constant SWAR is a WIN (b09_popcount 1.69x->1.07x behind LLVM, -37%).
/// Validated: 18-bench + edge-case differential all checksum-identical to LLVM;
/// the recognizer fires only on the exact `x&=x-1`/`c+=1`/`x!=0` idiom.
/// `TCG_X86_POPCOUNT_IDIOM` is still accepted as a (redundant) force-on.
fn popcount_idiom_enabled() -> bool {
    crate::env_lock::var_os("TCG_NO_X86_POPCOUNT_IDIOM").is_none()
}

/// A recognized Kernighan-popcount loop, ready to be rewritten to the
/// straight-line SWAR popcount. The raw post-ISel shape is a 2-block loop:
/// `header` tests `x == 0` (→ `exit`) else enters `latch`, which does the
/// clear-lowest-set-bit `x &= x-1` + `c += 1` and branches back to `header`.
/// `x` is the loop-carried Gpr64 value; `c` the loop-carried Gpr32 counter.
struct PopcountPlan {
    latch: Block,
    exit: Block,
    x: VReg,
    c: VReg,
}

/// Recognizer for the Kernighan popcount idiom (see [`PopcountPlan`]). The loop
/// is a DATA-DEPENDENT single-block self-loop (no IV / trip count), so this does
/// custom copy-based loop-carried matching rather than `recognize_header`. Fails
/// closed on anything but the exact shape.
fn recognize_kernighan_popcount_loop(
    func: &X86ISelFunction,
    lp: &LoopInfo,
) -> Option<PopcountPlan> {
    if !popcount_idiom_enabled() {
        return None;
    }
    // Raw shape: a 2-block loop. `header` tests x (→ exit or latch); `latch` does
    // the body and branches back to `header` only.
    if lp.body.len() != 2 || lp.header == lp.latch {
        return None;
    }
    let header = lp.header;
    let latch = lp.latch;
    if !lp.body.contains(&header) || !lp.body.contains(&latch) {
        return None;
    }
    let _preheader = lp.preheader?;
    let hblock = func.blocks.get(&header)?;
    let lblock = func.blocks.get(&latch)?;
    if lblock.successors.as_slice() != [header] {
        return None; // latch's only successor is the back-edge to the header
    }
    if hblock.successors.len() != 2 || !hblock.successors.contains(&latch) {
        return None;
    }
    let exit = *hblock.successors.iter().find(|&&s| s != latch)?;

    // Fail closed on any op outside the exact Kernighan body vocabulary — no
    // memory, no calls, no other arithmetic that could carry a hidden value. The
    // constant `1` may be register-materialized (`MovRI r,1` + `SubRR`/`AddRR`)
    // or an immediate (`SubRI`/`AddRI`), so both forms are admitted.
    for blk in [hblock, lblock] {
        for inst in &blk.insts {
            if !matches!(
                inst.opcode,
                X86Opcode::MovRR
                    | X86Opcode::MovRR32
                    | X86Opcode::MovRI
                    | X86Opcode::SubRI
                    | X86Opcode::SubRR
                    | X86Opcode::AndRR
                    | X86Opcode::AndRI
                    | X86Opcode::AddRI
                    | X86Opcode::AddRR
                    | X86Opcode::TestRR
                    | X86Opcode::CmpRI
                    | X86Opcode::CmpRR
                    | X86Opcode::Jcc
                    | X86Opcode::Jmp
            ) {
                return None;
            }
        }
    }

    let defs = DefIndex::build(func);
    // Is `v` a register-materialized (or trivially the immediate) constant 1?
    let is_one = |v: VReg| -> bool {
        defs.def_inst(func, v).is_some_and(|d| {
            d.opcode == X86Opcode::MovRI
                && matches!(d.operands.get(1), Some(X86ISelOperand::Imm(1)))
        })
    };
    // Does `v`'s def compute `base - 1` (SubRI base,1 | SubRR base,one)? Returns
    // the canonical `base`.
    let sub_one_base = |v: VReg| -> Option<VReg> {
        let d = defs.def_inst(func, v)?;
        match d.opcode {
            X86Opcode::SubRI => match d.operands.as_slice() {
                [_, X86ISelOperand::VReg(b), X86ISelOperand::Imm(1)] => {
                    Some(canon(func, &defs, *b))
                }
                _ => None,
            },
            X86Opcode::SubRR => match d.operands.as_slice() {
                [_, X86ISelOperand::VReg(b), X86ISelOperand::VReg(one)] if is_one(*one) => {
                    Some(canon(func, &defs, *b))
                }
                _ => None,
            },
            _ => None,
        }
    };

    // Kernighan core in the LATCH: `AndRR d, p, q` with {p,q}={x, x-1}, and x
    // loop-carried (redefined by `MovRR x, <=d>`).
    let mut x_carried: Option<VReg> = None;
    for inst in &lblock.insts {
        if inst.opcode != X86Opcode::AndRR {
            continue;
        }
        let [
            X86ISelOperand::VReg(d),
            X86ISelOperand::VReg(a),
            X86ISelOperand::VReg(b),
        ] = inst.operands.as_slice()
        else {
            continue;
        };
        let (ca, cb) = (canon(func, &defs, *a), canon(func, &defs, *b));
        let and_res = canon(func, &defs, *d);
        for (x_side, sub_side) in [(ca, cb), (cb, ca)] {
            if sub_one_base(sub_side) != Some(x_side) {
                continue;
            }
            let carried_back = lblock.insts.iter().any(|i| {
                i.opcode == X86Opcode::MovRR
                    && matches!(i.operands.first(), Some(X86ISelOperand::VReg(dd)) if canon(func, &defs, *dd) == x_side)
                    && matches!(i.operands.get(1), Some(X86ISelOperand::VReg(ss)) if canon(func, &defs, *ss) == and_res)
            });
            if carried_back && x_side.class == RegClass::Gpr64 {
                x_carried = Some(x_side);
            }
        }
    }
    let x = x_carried?;

    // Counter in the LATCH: `AddRI cn,c,1 | AddRR cn,c,one` with c loop-carried
    // (redefined by `MovRR32 c, <=cn>`), Gpr32.
    let mut c_carried: Option<VReg> = None;
    for inst in &lblock.insts {
        let (c_op, add_res) = match (inst.opcode, inst.operands.as_slice()) {
            (
                X86Opcode::AddRI,
                [
                    X86ISelOperand::VReg(cn),
                    X86ISelOperand::VReg(c),
                    X86ISelOperand::Imm(1),
                ],
            ) => (*c, *cn),
            (
                X86Opcode::AddRR,
                [
                    X86ISelOperand::VReg(cn),
                    X86ISelOperand::VReg(c),
                    X86ISelOperand::VReg(one),
                ],
            ) if is_one(*one) => (*c, *cn),
            _ => continue,
        };
        let cc = canon(func, &defs, c_op);
        let add_res = canon(func, &defs, add_res);
        if cc.class != RegClass::Gpr32 {
            continue;
        }
        let carried_back = lblock.insts.iter().any(|i| {
            matches!(i.opcode, X86Opcode::MovRR32 | X86Opcode::MovRR)
                && matches!(i.operands.first(), Some(X86ISelOperand::VReg(dd)) if canon(func, &defs, *dd) == cc)
                && matches!(i.operands.get(1), Some(X86ISelOperand::VReg(ss)) if canon(func, &defs, *ss) == add_res)
        });
        if carried_back {
            c_carried = Some(cc);
        }
    }
    let c = c_carried?;

    // The HEADER must test `x` for zero (loop runs while x != 0): `CmpRI x,0` or
    // `TestRR x,x` (matched through copies via canon).
    let tests_x = hblock.insts.iter().any(|i| {
        (i.opcode == X86Opcode::TestRR
            && matches!(i.operands.first(), Some(X86ISelOperand::VReg(v)) if canon(func, &defs, *v) == x)
            && matches!(i.operands.get(1), Some(X86ISelOperand::VReg(v)) if canon(func, &defs, *v) == x))
            || (i.opcode == X86Opcode::CmpRI
                && matches!(i.operands.first(), Some(X86ISelOperand::VReg(v)) if canon(func, &defs, *v) == x)
                && matches!(i.operands.get(1), Some(X86ISelOperand::Imm(0))))
    });
    if !tests_x {
        return None;
    }

    Some(PopcountPlan { latch, exit, x, c })
}

/// Rewrite a recognized Kernighan-popcount loop to the branch-free SWAR
/// popcount. Since this runs pre-regalloc we rebuild the LATCH block straight-line
/// (`c = c + popcount(x); jmp exit`) and drop its back-edge — the loop no longer
/// iterates. The header guard (`x != 0 ? latch : exit`) still routes `x == 0`
/// straight to the exit with the counter unchanged; entering the latch means
/// x != 0, and SWAR of any x (incl. the guaranteed-nonzero case) yields its true
/// popcount, so `c += popcount(x_entry)` is exact for the single visit.
fn apply_popcount_swar(func: &mut X86ISelFunction, plan: &PopcountPlan) {
    let x = plan.x;
    let c = plan.c;
    let g64 = |func: &mut X86ISelFunction| new_gpr64(func);
    let vr = |v: VReg| X86ISelOperand::VReg(v);
    let imm = |k: i64| X86ISelOperand::Imm(k);

    // Fresh temporaries for the SWAR chain + the mask materializations.
    let s1 = g64(func);
    let m55 = g64(func);
    let a1 = g64(func);
    let t1 = g64(func);
    let m33 = g64(func);
    let lo = g64(func);
    let s2 = g64(func);
    let hi = g64(func);
    let t2 = g64(func);
    let s3 = g64(func);
    let sum = g64(func);
    let m0f = g64(func);
    let t3 = g64(func);
    let m01 = g64(func);
    let prod = g64(func);
    let cnt64 = g64(func);
    let cnt32 = new_gpr32(func);
    let c_new = new_gpr32(func);

    let insts = vec![
        // s1 = x >> 1 ; a1 = s1 & 0x5555… ; t1 = x - a1
        X86ISelInst::new(X86Opcode::ShrRI, vec![vr(s1), vr(x), imm(1)]),
        X86ISelInst::new(X86Opcode::MovRI, vec![vr(m55), imm(0x5555_5555_5555_5555)]),
        X86ISelInst::new(X86Opcode::AndRR, vec![vr(a1), vr(s1), vr(m55)]),
        X86ISelInst::new(X86Opcode::SubRR, vec![vr(t1), vr(x), vr(a1)]),
        // t2 = (t1 & 0x3333…) + ((t1 >> 2) & 0x3333…)
        X86ISelInst::new(X86Opcode::MovRI, vec![vr(m33), imm(0x3333_3333_3333_3333)]),
        X86ISelInst::new(X86Opcode::AndRR, vec![vr(lo), vr(t1), vr(m33)]),
        X86ISelInst::new(X86Opcode::ShrRI, vec![vr(s2), vr(t1), imm(2)]),
        X86ISelInst::new(X86Opcode::AndRR, vec![vr(hi), vr(s2), vr(m33)]),
        X86ISelInst::new(X86Opcode::AddRR, vec![vr(t2), vr(lo), vr(hi)]),
        // t3 = (t2 + (t2 >> 4)) & 0x0f0f…
        X86ISelInst::new(X86Opcode::ShrRI, vec![vr(s3), vr(t2), imm(4)]),
        X86ISelInst::new(X86Opcode::AddRR, vec![vr(sum), vr(t2), vr(s3)]),
        X86ISelInst::new(X86Opcode::MovRI, vec![vr(m0f), imm(0x0f0f_0f0f_0f0f_0f0f)]),
        X86ISelInst::new(X86Opcode::AndRR, vec![vr(t3), vr(sum), vr(m0f)]),
        // cnt = (t3 * 0x0101…) >> 56   (sum of bytes into the top byte)
        X86ISelInst::new(X86Opcode::MovRI, vec![vr(m01), imm(0x0101_0101_0101_0101)]),
        X86ISelInst::new(X86Opcode::ImulRR, vec![vr(prod), vr(t3), vr(m01)]),
        X86ISelInst::new(X86Opcode::ShrRI, vec![vr(cnt64), vr(prod), imm(56)]),
        // c = c + (cnt as i32)  (popcount is 0..=64, fits; MovRR32 truncates)
        X86ISelInst::new(X86Opcode::MovRR32, vec![vr(cnt32), vr(cnt64)]),
        X86ISelInst::new(X86Opcode::AddRR, vec![vr(c_new), vr(c), vr(cnt32)]),
        X86ISelInst::new(X86Opcode::MovRR32, vec![vr(c), vr(c_new)]),
        // Set x = 0 to match the eliminated loop's exit invariant (the original
        // loop exits only when x == 0). The SWAR above already consumed x's entry
        // value, so this makes the latch→exit path agree with the header→exit
        // (x == 0) path for any post-loop consumer of x.
        X86ISelInst::new(X86Opcode::MovRI, vec![vr(x), imm(0)]),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(plan.exit)]),
    ];

    if let Some(block) = func.blocks.get_mut(&plan.latch) {
        block.insts = insts;
        block.successors = vec![plan.exit];
    }
}

// ===========================================================================
// Bit-reversal idiom -> constant-time SWAR bit-reverse (scalar loop-idiom win)
// `let mut r=0; for _ in 0..64 { r=(r<<1)|(x&1); x>>=1 }`  ==>  `r = x.reverse_bits()`
// via the branch-free swap-adjacent-bits/pairs/nibbles/bytes/words SWAR. Both
// compilers otherwise LOOP it 64 serial iterations. Opt-in behind
// `TCG_X86_BITREV_IDIOM`.
// ===========================================================================

/// Kill switch for the bit-reversal SWAR idiom tier (DEFAULT-ON; opt out with
/// `TCG_NO_X86_BITREV_IDIOM`). Emits only already-PROVEN scalar ops (avoids
/// `Bswap`, which is FailClosedAllowlisted — uses the mask-shift byte/word
/// swaps), so it needs NO new proof and survives proofs-ON. Default-on because
/// BOTH compilers otherwise compile the manual reversal as a 64-iteration serial
/// loop, so the constant SWAR is a decisive WIN (b09_popcount goes to 0.25x =
/// the bridge is ~4x FASTER than LLVM). Validated: 18-bench + a `reverse_bits()`
/// oracle fuzz all checksum-identical to LLVM; the recognizer fires only on the
/// exact `for _ in 0..64 { r=(r<<1)|(x&1); x>>=1 }` idiom (trip bound == 64).
/// `TCG_X86_BITREV_IDIOM` is still accepted as a (redundant) force-on.
fn bitrev_idiom_enabled() -> bool {
    crate::env_lock::var_os("TCG_NO_X86_BITREV_IDIOM").is_none()
}

/// A recognized 64-bit bit-reversal loop, ready to be rewritten to the SWAR
/// bit-reverse. Raw shape: a 2-block loop; `header` tests the trip counter
/// `i < 64` (→ `latch` while below, else `exit`); `latch` does
/// `r = (r<<1)|(x&1); x >>= 1; i += 1` and branches back. `r` is the loop-carried
/// Gpr64 result, `x` the loop-carried Gpr64 input, `i` the Gpr32 trip counter.
/// Rewrite a byte-equality count to a PCMPEQB/PSADBW-accumulate loop (16
/// bytes/iteration) plus the unchanged scalar loop as the remainder. CFG
/// mirrors [`apply_byte_sum_plan`]: `preheader -> VP -> VH -> {VB -> VH | VR ->
/// header}`.
fn apply_byte_eq_count_plan(func: &mut X86ISelFunction, plan: &ByteEqCountPlan) {
    let _ = plan.slot;

    // 16-byte scratch slot: zero seed for `vacc`/`xzero`, the K splat, and the
    // spill target for the final horizontal reduce.
    let scratch_slot = func.stack_slots.len() as u32;
    func.stack_slots.push(StackSlotInfo::new(16, 16));

    let base_id = next_block_id(func);
    let vp = Block(base_id);
    let vh = Block(base_id + 1);
    let vb = Block(base_id + 2);
    let vrb = Block(base_id + 3);

    let rs = new_gpr64(func);
    let rz = new_gpr32(func);
    let rk = new_gpr32(func);
    let vacc = new_fpr128(func);
    let xzero = new_fpr128(func);
    let xk = new_fpr128(func);
    let xchunk = new_fpr128(func);
    let xeq = new_fpr128(func);
    let xone = new_fpr128(func);
    let xsad = new_fpr128(func);
    let limit = new_gpr64(func);
    let pe = new_gpr64(func);
    let sixteen = new_gpr64(func);
    let niv = new_gpr64(func);
    let s0 = new_gpr64(func);
    let s1 = new_gpr64(func);
    let t01 = new_gpr64(func);
    let accf = new_gpr64(func);

    let iv = plan.iv;
    let acc = plan.acc;
    let vr = X86ISelOperand::VReg;
    let scratch_mem = |disp: i32| X86ISelOperand::MemAddr {
        base: Box::new(vr(rs)),
        disp,
    };

    // VP: zero the slot; seed vacc/xzero from it, then splat K through it.
    let mut vp_insts = vec![
        X86ISelInst::new(
            X86Opcode::Lea,
            vec![
                vr(rs),
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::StackSlot(scratch_slot)),
                    disp: 0,
                },
            ],
        ),
        X86ISelInst::new(X86Opcode::MovRI, vec![vr(rz), X86ISelOperand::Imm(0)]),
    ];
    for lane in 0..(16 / ELEM_SIZE as i64) {
        vp_insts.push(X86ISelInst::new(
            X86Opcode::MovMR32,
            vec![scratch_mem((lane * ELEM_SIZE as i64) as i32), vr(rz)],
        ));
    }
    vp_insts.push(X86ISelInst::new(
        X86Opcode::MovdquRM,
        vec![vr(vacc), scratch_mem(0)],
    ));
    vp_insts.push(X86ISelInst::new(
        X86Opcode::MovdquRM,
        vec![vr(xzero), scratch_mem(0)],
    ));
    // `K * 0x01010101` replicates the byte across all four lanes.
    vp_insts.push(X86ISelInst::new(
        X86Opcode::MovRI,
        vec![
            vr(rk),
            X86ISelOperand::Imm(plan.k.wrapping_mul(0x0101_0101)),
        ],
    ));
    for lane in 0..(16 / ELEM_SIZE as i64) {
        vp_insts.push(X86ISelInst::new(
            X86Opcode::MovMR32,
            vec![scratch_mem((lane * ELEM_SIZE as i64) as i32), vr(rk)],
        ));
    }
    vp_insts.push(X86ISelInst::new(
        X86Opcode::MovdquRM,
        vec![vr(xk), scratch_mem(0)],
    ));
    vp_insts.push(X86ISelInst::new(
        X86Opcode::Jmp,
        vec![X86ISelOperand::Block(vh)],
    ));

    // VH: `iv <u bound - 15` — i.e. `iv + 16 <= bound`, which holds for ANY
    // start, unlike the `(n/16)*16` bound the zero-init tiers use.
    let vh_insts = vec![
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![vr(limit), X86ISelOperand::Imm(plan.bound - LANES_B + 1)],
        ),
        X86ISelInst::new(X86Opcode::CmpRR, vec![vr(iv), vr(limit)]),
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(vb),
            ],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(vrb)]),
    ];

    // VB: count matching bytes in one 16-byte chunk.
    let vb_insts = vec![
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![
                vr(pe),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(vr(plan.base)),
                    index: Box::new(vr(iv)),
                    scale: ELEM_SIZE_B,
                    disp: 0,
                },
            ],
        ),
        X86ISelInst::new(
            X86Opcode::MovdquRM,
            vec![
                vr(xchunk),
                X86ISelOperand::MemAddr {
                    base: Box::new(vr(pe)),
                    disp: 0,
                },
            ],
        ),
        X86ISelInst::new(X86Opcode::Pcmpeqb, vec![vr(xeq), vr(xchunk), vr(xk)]),
        X86ISelInst::new(X86Opcode::Psubb, vec![vr(xone), vr(xzero), vr(xeq)]),
        X86ISelInst::new(X86Opcode::Psadbw, vec![vr(xsad), vr(xone), vr(xzero)]),
        X86ISelInst::new(X86Opcode::Paddq, vec![vr(vacc), vr(vacc), vr(xsad)]),
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![vr(sixteen), X86ISelOperand::Imm(LANES_B)],
        ),
        X86ISelInst::new(X86Opcode::AddRR, vec![vr(niv), vr(iv), vr(sixteen)]),
        X86ISelInst::new(X86Opcode::MovRR, vec![vr(iv), vr(niv)]),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(vh)]),
    ];

    // VR: fold the two u64 lane partials into `acc`, then fall into the scalar
    // loop for the `< 16` remainder from wherever `iv` stopped.
    let vr_insts = vec![
        X86ISelInst::new(X86Opcode::MovdquMR, vec![scratch_mem(0), vr(vacc)]),
        X86ISelInst::new(X86Opcode::MovRM, vec![vr(s0), scratch_mem(0)]),
        X86ISelInst::new(X86Opcode::MovRM, vec![vr(s1), scratch_mem(8)]),
        X86ISelInst::new(X86Opcode::AddRR, vec![vr(t01), vr(s0), vr(s1)]),
        X86ISelInst::new(X86Opcode::AddRR, vec![vr(accf), vr(acc), vr(t01)]),
        X86ISelInst::new(X86Opcode::MovRR, vec![vr(acc), vr(accf)]),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(plan.header)]),
    ];

    for (blk, insts, successors) in [
        (vp, vp_insts, vec![vh]),
        (vh, vh_insts, vec![vb, vrb]),
        (vb, vb_insts, vec![vh]),
        (vrb, vr_insts, vec![plan.header]),
    ] {
        func.blocks.insert(blk, X86ISelBlock { insts, successors });
    }

    if let Some(pre) = func.blocks.get_mut(&plan.preheader) {
        for inst in pre.insts.iter_mut() {
            if inst.opcode == X86Opcode::Jmp
                && let Some(X86ISelOperand::Block(t)) = inst.operands.first_mut()
                && *t == plan.header
            {
                *t = vp;
            }
        }
        pre.successors = pre
            .successors
            .iter()
            .map(|s| if *s == plan.header { vp } else { *s })
            .collect();
    }

    if let Some(pos) = func.block_order.iter().position(|b| *b == plan.preheader) {
        for (off, blk) in [vp, vh, vb, vrb].into_iter().enumerate() {
            func.block_order.insert(pos + 1 + off, blk);
        }
    } else {
        func.block_order.extend([vp, vh, vb, vrb]);
    }
}

/// Plan for the byte-equality COUNT reduction — the predicated shape
///
/// ```text
/// while iv <u BOUND { if a[iv] == K { count += 1 } iv += 1 }
/// ```
///
/// which is a DIAMOND in the body, not the linear chain every other tier here
/// matches, and whose IV may start at a RUNTIME value.
///
/// Packed form, 16 bytes/iteration, using only opcodes the x86 perimeter
/// already proves:
///
/// ```text
/// xeq  = PCMPEQB(chunk, splat(K))   ; 0xff per matching byte, 0x00 otherwise
/// xone = PSUBB(0, xeq)              ; 0x01 per match  (0 - 0xff == 1 mod 256)
/// xsad = PSADBW(xone, 0)            ; per-8-byte-lane sum, <= 8
/// vacc = PADDQ(vacc, xsad)          ; u64 lanes — cannot overflow
/// ```
///
/// PSADBW every iteration (rather than deferring a PSUBB byte-counter and
/// flushing before it wraps at 255) costs one extra op per chunk and removes
/// the trip-count ceiling entirely, so there is no wrap obligation to discharge.
struct ByteEqCountPlan {
    iv: VReg,
    /// The loop-carried count accumulator (Gpr64).
    acc: VReg,
    /// Constant exclusive upper bound on `iv` from the header test.
    bound: i64,
    /// The byte value counted (`0..=255`).
    k: i64,
    base: VReg,
    slot: u32,
    preheader: Block,
    header: Block,
}

/// Kill switch for the byte-equality count tier (DEFAULT-ON; opt out with
/// `TCG_NO_X86_BYTE_EQ_COUNT`).
fn byte_eq_count_enabled() -> bool {
    crate::env_lock::var_os("TCG_NO_X86_BYTE_EQ_COUNT").is_none()
}

/// `is_counter`, minus the zero-init requirement.
///
/// ⚑ The zero init is LOAD-BEARING for every other tier and must stay there.
/// Their vector guard is `iv < (n / 16) * 16`, which implies `iv + 16 <= n`
/// ONLY when `iv` steps 0, 16, 32, …; from a non-zero start the final chunk
/// reads past the slot (checked: `n=1024, start=3` reads `[1011, 1027)`).
/// This tier is admitted to use it because its guard is `iv < bound - 15`,
/// which implies `iv + 16 <= bound` for EVERY start — verified by exhaustion
/// over `n in [16,1200) x start in [0,16]`, and identical to the old guard at
/// `start == 0` over `n in [16,2000)`.
fn is_counter_any_init(
    func: &X86ISelFunction,
    defs: &DefIndex,
    iv: VReg,
    body: &BTreeSet<Block>,
) -> bool {
    let mut init_outside = false;
    let mut unit_increment_inside = false;
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        let in_body = body.contains(block_id);
        for inst in &block.insts {
            if !x86_produces_value(inst.opcode)
                || !matches!(inst.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == iv)
            {
                continue;
            }
            if !in_body {
                init_outside = true;
            } else if inst.opcode == X86Opcode::MovRR {
                if let Some(X86ISelOperand::VReg(src)) = inst.operands.get(1)
                    && is_iv_plus_one(func, defs, iv, *src)
                {
                    unit_increment_inside = true;
                }
            } else {
                // Any other in-body def of the IV breaks the +1 induction.
                return false;
            }
        }
    }
    init_outside && unit_increment_inside
}

/// Header analysis for [`ByteEqCountPlan`]: `iv <u BOUND` against a constant,
/// with `iv` a unit counter of ANY initial value.
fn recognize_header_any_init(
    func: &X86ISelFunction,
    defs: &DefIndex,
    header: Block,
    body: &BTreeSet<Block>,
) -> Option<(VReg, i64)> {
    let block = func.blocks.get(&header)?;
    for inst in &block.insts {
        match inst.opcode {
            X86Opcode::CmpRR => {
                let (Some(X86ISelOperand::VReg(a)), Some(X86ISelOperand::VReg(b))) =
                    (inst.operands.first(), inst.operands.get(1))
                else {
                    continue;
                };
                if let Some(n) = const_of(func, defs, *b) {
                    let iv = canon(func, defs, *a);
                    if is_counter_any_init(func, defs, iv, body) {
                        return Some((iv, n));
                    }
                }
            }
            X86Opcode::CmpRI | X86Opcode::CmpRI8 => {
                if let (Some(X86ISelOperand::VReg(a)), Some(X86ISelOperand::Imm(n))) =
                    (inst.operands.first(), inst.operands.get(1))
                {
                    let iv = canon(func, defs, *a);
                    if is_counter_any_init(func, defs, iv, body) {
                        return Some((iv, *n));
                    }
                }
            }
            _ => {}
        }
    }
    None
}

/// Recognizer for the byte-equality count shape (see [`ByteEqCountPlan`]).
fn recognize_byte_eq_count_loop(
    func: &X86ISelFunction,
    idom: &HashMap<Block, Block>,
    lp: &LoopInfo,
) -> Option<ByteEqCountPlan> {
    if !byte_eq_count_enabled() {
        return None;
    }
    let header = lp.header;
    let latch = lp.latch;
    let body = &lp.body;
    let preheader = lp.preheader?;
    let _ = idom;

    for block_id in body {
        let block = func.blocks.get(block_id)?;
        if block.insts.iter().any(|i| i.opcode == X86Opcode::Phi) {
            return None;
        }
    }

    let defs = DefIndex::build(func);
    let mut memo: HashMap<VReg, Prov> = HashMap::new();

    // 1. IV + constant bound (IV init may be runtime — see the guard note).
    let (iv, bound) = recognize_header_any_init(func, &defs, header, body)?;
    if bound < LANES_B {
        return None;
    }

    // 2. Walk single-successor body blocks (admitting only provably-safe inline
    //    bounds carriers) until the two-way TEST block.
    let header_succs = &func.blocks.get(&header)?.successors;
    let mut cur = unique_in_body_succ(header_succs, body)?;
    let mut seen: HashSet<Block> = HashSet::new();
    let test = loop {
        if !body.contains(&cur) || !seen.insert(cur) {
            return None;
        }
        let block = func.blocks.get(&cur)?;
        for inst in &block.insts {
            let op = inst.opcode;
            if op == X86Opcode::Call || op == X86Opcode::CallR || op == X86Opcode::CallM {
                return None;
            }
            if is_store_opcode(op) {
                return None;
            }
            if op == X86Opcode::TrapBoundsCheckExact
                && !is_safe_iv_bounds_carrier(func, &defs, iv, &mut memo, inst, bound)
            {
                return None;
            }
        }
        let in_body: Vec<Block> = block
            .successors
            .iter()
            .copied()
            .filter(|s| body.contains(s))
            .collect();
        for s in &block.successors {
            if !body.contains(s) && !is_pure_trap_block(func, *s) {
                return None;
            }
        }
        match in_body.len() {
            1 => cur = in_body[0],
            2 => break cur,
            _ => return None,
        }
    };

    // 3. The test block: exactly one byte load from `&slot[iv]`, widened, and
    //    compared against a byte constant, then a two-way branch.
    let tb = func.blocks.get(&test)?;
    let mut byte_load: Option<(VReg, u32)> = None;
    for inst in &tb.insts {
        let op = inst.opcode;
        if is_load_opcode(op) {
            if op != X86Opcode::MovRM8 || byte_load.is_some() {
                return None;
            }
            let dst = match inst.operands.first() {
                Some(X86ISelOperand::VReg(d)) => *d,
                _ => return None,
            };
            let slot = elem_addr_slot(
                func,
                &defs,
                iv,
                &mut memo,
                inst.operands.get(1),
                ELEM_SIZE_B as i64,
            )?;
            byte_load = Some((dst, slot));
        } else if op != X86Opcode::Movzx
            && op != X86Opcode::Jcc
            && op != X86Opcode::TrapBoundsCheckExact
            && !is_whitelisted_body_opcode(op)
        {
            return None;
        }
    }
    let (load_dst, slot) = byte_load?;

    // The compare feeding the branch must be `widened_byte == K`.
    let (cmp_v, k) = tb.insts.iter().rev().find_map(|i| {
        match (i.opcode, i.operands.first(), i.operands.get(1)) {
            (
                X86Opcode::CmpRI | X86Opcode::CmpRI8,
                Some(X86ISelOperand::VReg(a)),
                Some(X86ISelOperand::Imm(n)),
            ) => Some((*a, *n)),
            _ => None,
        }
    })?;
    if !(0..=255).contains(&k) {
        return None;
    }
    if !traces_to_zero_extended_byte(func, &defs, cmp_v, canon(func, &defs, load_dst)) {
        return None;
    }

    // 4. The arms. `Jcc cc -> taken`, fallthrough `Jmp -> other`; both must
    //    rejoin at the latch, one adding 1 to `acc` and the other passing it
    //    through. Only the EQUAL-counts polarity is claimed.
    let jcc = tb.insts.iter().rev().find(|i| i.opcode == X86Opcode::Jcc)?;
    let (Some(X86ISelOperand::CondCode(cc)), Some(X86ISelOperand::Block(taken))) =
        (jcc.operands.first(), jcc.operands.get(1))
    else {
        return None;
    };
    if *cc != X86CondCode::E {
        return None;
    }
    let taken = *taken;
    let other = *tb
        .successors
        .iter()
        .find(|s| **s != taken && body.contains(s))?;
    if unique_in_body_succ(&func.blocks.get(&taken)?.successors, body)? != latch
        || unique_in_body_succ(&func.blocks.get(&other)?.successors, body)? != latch
    {
        return None;
    }

    // `taken` (byte == K) increments; `other` passes through. Both write the
    // SAME merge vreg, which the latch copies into `acc`.
    let (merge, acc) = arm_increment_pair(func, &defs, taken, other)?;
    if acc == iv || acc.class != RegClass::Gpr64 {
        return None;
    }

    // 5. The latch writes back both `iv` and `acc`, and nothing else reads
    //    `acc` inside the loop.
    let lb = func.blocks.get(&latch)?;
    if !lb.insts.iter().any(|i| {
        i.opcode == X86Opcode::MovRR
            && matches!(i.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == acc)
            && matches!(i.operands.get(1), Some(X86ISelOperand::VReg(s)) if canon(func, &defs, *s) == merge)
    }) {
        return None;
    }
    let has_outside_def = func.block_order.iter().any(|b| {
        !body.contains(b)
            && func.blocks.get(b).is_some_and(|blk| {
                blk.insts.iter().any(|i| {
                    x86_produces_value(i.opcode)
                        && matches!(i.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == acc)
                })
            })
    });
    if !has_outside_def {
        return None;
    }
    for block_id in body {
        if *block_id == taken || *block_id == other {
            continue; // the reduction arms — validated above
        }
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            let produces = x86_produces_value(inst.opcode);
            for (opi, op) in inst.operands.iter().enumerate() {
                if (produces && opi == 0) || (*block_id == latch && inst.opcode == X86Opcode::MovRR)
                {
                    continue;
                }
                if operand_references_vreg(op, acc) {
                    return None;
                }
            }
        }
    }

    // 6. Slot must hold >= bound bytes so every packed access stays in-slot.
    let info = func.stack_slots.get(slot as usize)?;
    if (info.size as i64) < bound {
        return None;
    }
    let base = slot_base_vreg(func, &defs, slot)?;

    Some(ByteEqCountPlan {
        iv,
        acc,
        bound,
        k,
        base,
        slot,
        preheader,
        header,
    })
}

/// Validate the two arms of a count diamond and return `(merge, acc)`: `inc`
/// must compute `merge = acc + 1` and `nop` must compute `merge = acc`, for the
/// same `merge` and `acc`.
fn arm_increment_pair(
    func: &X86ISelFunction,
    defs: &DefIndex,
    inc: Block,
    nop: Block,
) -> Option<(VReg, VReg)> {
    // nop arm: `MovRR merge, acc` (plus only copies/constants).
    let nb = func.blocks.get(&nop)?;
    let (merge, acc) =
        nb.insts.iter().find_map(
            |i| match (i.opcode, i.operands.first(), i.operands.get(1)) {
                (
                    X86Opcode::MovRR,
                    Some(X86ISelOperand::VReg(d)),
                    Some(X86ISelOperand::VReg(s)),
                ) => Some((*d, canon(func, defs, *s))),
                _ => None,
            },
        )?;
    for inst in &nb.insts {
        if !matches!(
            inst.opcode,
            X86Opcode::MovRR | X86Opcode::MovRR32 | X86Opcode::MovRI | X86Opcode::Jmp
        ) {
            return None;
        }
    }
    // inc arm: some `AddRR t, acc, one` with `one` a constant 1, then
    // `MovRR merge, t`.
    let ib = func.blocks.get(&inc)?;
    for inst in &ib.insts {
        if !matches!(
            inst.opcode,
            X86Opcode::MovRR
                | X86Opcode::MovRR32
                | X86Opcode::MovRI
                | X86Opcode::AddRR
                | X86Opcode::Jmp
        ) {
            return None;
        }
    }
    let writes_merge = ib.insts.iter().any(|i| {
        i.opcode == X86Opcode::MovRR
            && matches!(i.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == merge)
            && matches!(i.operands.get(1), Some(X86ISelOperand::VReg(s)) if {
                let t = canon(func, defs, *s);
                defs.def_inst(func, t).is_some_and(|a| {
                    a.opcode == X86Opcode::AddRR
                        && match (a.operands.get(1), a.operands.get(2)) {
                            (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => {
                                let (cx, cy) = (canon(func, defs, *x), canon(func, defs, *y));
                                (cx == acc && const_of(func, defs, cy) == Some(1))
                                    || (cy == acc && const_of(func, defs, cx) == Some(1))
                            }
                            _ => false,
                        }
                })
            })
    });
    if !writes_merge {
        return None;
    }
    Some((merge, acc))
}

struct BitrevPlan {
    latch: Block,
    exit: Block,
    r: VReg,
    x: VReg,
    i: VReg,
}

/// Recognizer for the 64-bit bit-reversal idiom (see [`BitrevPlan`]). The exact
/// `for i in 0..64 { r=(r<<1)|(x&1); x>>=1 }` shape; fails closed otherwise. The
/// trip bound MUST be 64 (the type's bit width) so the loop reverses every bit.
fn recognize_bitrev_loop(func: &X86ISelFunction, lp: &LoopInfo) -> Option<BitrevPlan> {
    if !bitrev_idiom_enabled() {
        return None;
    }
    if lp.body.len() != 2 || lp.header == lp.latch {
        return None;
    }
    let header = lp.header;
    let latch = lp.latch;
    if !lp.body.contains(&header) || !lp.body.contains(&latch) {
        return None;
    }
    let _preheader = lp.preheader?;
    let hblock = func.blocks.get(&header)?;
    let lblock = func.blocks.get(&latch)?;
    if lblock.successors.as_slice() != [header] {
        return None;
    }
    if hblock.successors.len() != 2 || !hblock.successors.contains(&latch) {
        return None;
    }
    let exit = *hblock.successors.iter().find(|&&s| s != latch)?;

    let defs = DefIndex::build(func);
    let is_const = |v: VReg, k: i64| -> bool {
        defs.def_inst(func, v).is_some_and(|d| {
            d.opcode == X86Opcode::MovRI
                && matches!(d.operands.get(1), Some(X86ISelOperand::Imm(c)) if *c == k)
        })
    };

    // --- latch: find the recurrence `r_new = (r<<1) | (x&1)`. ---
    // OrRR rn, sl, ax  where sl = ShlRI(r, 1), ax = AndRR(x, const1) [or (const1, x)].
    let mut found: Option<(VReg, VReg)> = None; // (r, x)
    for inst in &lblock.insts {
        if inst.opcode != X86Opcode::OrRR {
            continue;
        }
        let [
            X86ISelOperand::VReg(_orn),
            X86ISelOperand::VReg(p),
            X86ISelOperand::VReg(q),
        ] = inst.operands.as_slice()
        else {
            continue;
        };
        for (shl_side, and_side) in [(*p, *q), (*q, *p)] {
            // shl_side = ShlRI(r, 1)
            let Some(shl) = defs.def_inst(func, shl_side) else {
                continue;
            };
            let r = match (shl.opcode, shl.operands.as_slice()) {
                (X86Opcode::ShlRI, [_, X86ISelOperand::VReg(rr), X86ISelOperand::Imm(1)]) => {
                    canon(func, &defs, *rr)
                }
                _ => continue,
            };
            // and_side = AndRR(x, 1) | AndRR(1, x)
            let Some(and) = defs.def_inst(func, and_side) else {
                continue;
            };
            let x = match (and.opcode, and.operands.as_slice()) {
                (X86Opcode::AndRR, [_, X86ISelOperand::VReg(a), X86ISelOperand::VReg(b)]) => {
                    if is_const(*b, 1) {
                        canon(func, &defs, *a)
                    } else if is_const(*a, 1) {
                        canon(func, &defs, *b)
                    } else {
                        continue;
                    }
                }
                _ => continue,
            };
            if r.class == RegClass::Gpr64 && x.class == RegClass::Gpr64 {
                found = Some((r, x));
            }
        }
    }
    let (r, x) = found?;

    // r loop-carried: redefined by `MovRR r, <=orn>` — verify r is written from
    // the Or result. (We required the Or above; confirm the carry copy exists.)
    let r_carried = lblock.insts.iter().any(|i| {
        i.opcode == X86Opcode::MovRR
            && matches!(i.operands.first(), Some(X86ISelOperand::VReg(d)) if canon(func, &defs, *d) == r)
    });
    // x loop-carried: `x = x >> 1` (ShrRI xn, x, 1; MovRR x, xn).
    let x_shifted = lblock.insts.iter().any(|i| {
        i.opcode == X86Opcode::ShrRI
            && matches!(i.operands.get(1), Some(X86ISelOperand::VReg(v)) if canon(func, &defs, *v) == x)
            && matches!(i.operands.get(2), Some(X86ISelOperand::Imm(1)))
    });
    if !r_carried || !x_shifted {
        return None;
    }

    // --- trip counter `i` (Gpr32): `i += 1` in the latch, bound `< 64` in the
    //     header (a MovRI-materialized 64 compared against i). ---
    let mut i_counter: Option<VReg> = None;
    for inst in &lblock.insts {
        let (iv, res) = match (inst.opcode, inst.operands.as_slice()) {
            (
                X86Opcode::AddRR,
                [
                    X86ISelOperand::VReg(res),
                    X86ISelOperand::VReg(iv),
                    X86ISelOperand::VReg(one),
                ],
            ) if is_const(*one, 1) => (*iv, *res),
            (
                X86Opcode::AddRI,
                [
                    X86ISelOperand::VReg(res),
                    X86ISelOperand::VReg(iv),
                    X86ISelOperand::Imm(1),
                ],
            ) => (*iv, *res),
            _ => continue,
        };
        let iv = canon(func, &defs, iv);
        if iv.class != RegClass::Gpr32 {
            continue;
        }
        let carried = lblock.insts.iter().any(|k| {
            matches!(k.opcode, X86Opcode::MovRR32 | X86Opcode::MovRR)
                && matches!(k.operands.first(), Some(X86ISelOperand::VReg(d)) if canon(func, &defs, *d) == iv)
                && matches!(k.operands.get(1), Some(X86ISelOperand::VReg(s)) if canon(func, &defs, *s) == canon(func, &defs, res))
        });
        if carried {
            i_counter = Some(iv);
        }
    }
    let i = i_counter?;
    // Header: a CmpRR/CmpRI establishing the bound 64 against `i`. Require the
    // bound to be EXACTLY 64 (the u64 bit width) so every bit is reversed.
    let bound_ok = hblock
        .insts
        .iter()
        .any(|inst| match (inst.opcode, inst.operands.as_slice()) {
            (X86Opcode::CmpRR, [X86ISelOperand::VReg(a), X86ISelOperand::VReg(b)]) => {
                (canon(func, &defs, *a) == i && is_const(*b, 64))
                    || (canon(func, &defs, *b) == i && is_const(*a, 64))
            }
            (X86Opcode::CmpRI, [X86ISelOperand::VReg(a), X86ISelOperand::Imm(64)]) => {
                canon(func, &defs, *a) == i
            }
            _ => false,
        });
    if !bound_ok {
        return None;
    }

    Some(BitrevPlan {
        latch,
        exit,
        r,
        x,
        i,
    })
}

/// Rewrite a recognized 64-bit bit-reversal loop to the branch-free SWAR
/// bit-reverse. `r_final = reverse_bits(x_entry)` is INDEPENDENT of `r`'s init
/// (the recurrence's `r << 64` overflows to 0), so we compute it directly. Like
/// the popcount idiom we rebuild the latch straight-line and drop the back-edge;
/// `x = 0` and `i = 64` restore the loop's exit invariants for any post-loop use.
fn apply_bitrev_swar(func: &mut X86ISelFunction, plan: &BitrevPlan) {
    let x = plan.x;
    let r = plan.r;
    let i = plan.i;
    let vr = |v: VReg| X86ISelOperand::VReg(v);
    let imm = |k: i64| X86ISelOperand::Imm(k);

    let mut insts: Vec<X86ISelInst> = Vec::new();
    // SWAR bit-reverse of `x` into `cur`, avoiding the unproven BSWAP by doing the
    // byte/word swaps with masks. Each step swaps 2^k-bit groups:
    //   cur = ((cur >> s) & M) | ((cur & M) << s)
    // (the final 32-bit swap needs no mask). Masks materialized via MovRI.
    let steps: [(u32, i64); 5] = [
        (1, 0x5555_5555_5555_5555u64 as i64),
        (2, 0x3333_3333_3333_3333u64 as i64),
        (4, 0x0f0f_0f0f_0f0f_0f0fu64 as i64),
        (8, 0x00ff_00ff_00ff_00ffu64 as i64),
        (16, 0x0000_ffff_0000_ffffu64 as i64),
    ];
    let mut cur = x;
    for (shift, mask) in steps {
        let hi = new_gpr64(func); // cur >> shift
        let m = new_gpr64(func); // mask
        let hi_m = new_gpr64(func); // (cur >> shift) & mask
        let lo_m = new_gpr64(func); // (cur & mask)
        let lo_s = new_gpr64(func); // (cur & mask) << shift
        let out = new_gpr64(func); // result of this step
        insts.push(X86ISelInst::new(
            X86Opcode::ShrRI,
            vec![vr(hi), vr(cur), imm(i64::from(shift))],
        ));
        insts.push(X86ISelInst::new(X86Opcode::MovRI, vec![vr(m), imm(mask)]));
        insts.push(X86ISelInst::new(
            X86Opcode::AndRR,
            vec![vr(hi_m), vr(hi), vr(m)],
        ));
        insts.push(X86ISelInst::new(
            X86Opcode::AndRR,
            vec![vr(lo_m), vr(cur), vr(m)],
        ));
        insts.push(X86ISelInst::new(
            X86Opcode::ShlRI,
            vec![vr(lo_s), vr(lo_m), imm(i64::from(shift))],
        ));
        insts.push(X86ISelInst::new(
            X86Opcode::OrRR,
            vec![vr(out), vr(hi_m), vr(lo_s)],
        ));
        cur = out;
    }
    // Final step: swap the two 32-bit halves — `(cur >> 32) | (cur << 32)`.
    let hi32 = new_gpr64(func);
    let lo32 = new_gpr64(func);
    insts.push(X86ISelInst::new(
        X86Opcode::ShrRI,
        vec![vr(hi32), vr(cur), imm(32)],
    ));
    insts.push(X86ISelInst::new(
        X86Opcode::ShlRI,
        vec![vr(lo32), vr(cur), imm(32)],
    ));
    // r = reversed
    insts.push(X86ISelInst::new(
        X86Opcode::OrRR,
        vec![vr(r), vr(hi32), vr(lo32)],
    ));
    // Restore the loop's exit invariants (x shifted out to 0; i reached 64).
    insts.push(X86ISelInst::new(X86Opcode::MovRI, vec![vr(x), imm(0)]));
    insts.push(X86ISelInst::new(X86Opcode::MovRI, vec![vr(i), imm(64)]));
    insts.push(X86ISelInst::new(
        X86Opcode::Jmp,
        vec![X86ISelOperand::Block(plan.exit)],
    ));

    if let Some(block) = func.blocks.get_mut(&plan.latch) {
        block.insts = insts;
        block.successors = vec![plan.exit];
    }
}

// ===========================================================================
// CRC bit-serial -> table-driven (a scalar loop-idiom win).
// `for _ in 0..8 { m=-(crc&1); crc=(crc>>1)^(POLY&m) }`  ==>  one table lookup
// `crc = (crc>>8) ^ T[crc & 0xff]` where T[b]=bitloop8(b), computed at compile
// time from POLY and stored in a stack table (indexed via MovRM32Sib). Both
// LLVM and tcg otherwise LOOP the 8 serial bit-iterations. Opt-in
// `TCG_X86_CRC_TABLE`.
// ===========================================================================

/// Kill switch for the CRC-table idiom tier (DEFAULT-ON; opt out with
/// `TCG_NO_X86_CRC_TABLE`). Emits only PROVEN scalar ops (MovRI/MovMR32/Lea/Movzx/
/// AndRI/MovRM32Sib/ShrRI/XorRR/MovRR32) — needs NO new proof and survives
/// proofs-ON. Default-on because BOTH compilers otherwise LOOP the 8 serial
/// bit-iterations per byte, so the one table lookup is a decisive WIN
/// (b12_crc32 2.2x behind LLVM -> 0.72x = 1.4x FASTER = a 5th win). Validated:
/// all 18 benches checksum==LLVM + proofs-ON; a 5-program CRC fuzz (varied
/// polynomial / init / length) all match; the 256-entry table is unit-tested
/// against the canonical CRC-32 values + re-derived per entry. `TCG_X86_CRC_TABLE`
/// is still accepted as a (redundant) force-on.
fn crc_table_enabled() -> bool {
    std::env::var_os("TCG_NO_X86_CRC_TABLE").is_none()
}

/// A recognized 8-bit CRC bit-serial loop, ready to be table-driven. Raw shape:
/// 2-block loop; header tests an 8-trip bit counter, latch does the recurrence
/// `crc = (crc>>1) ^ (POLY & -(crc&1))` (Gpr32 crc) and `bit += 1`.
struct CrcTablePlan {
    latch: Block,
    exit: Block,
    crc: VReg, // loop-carried Gpr32 crc
    poly: u32, // the CRC polynomial
}

/// Recognizer for the 8-bit CRC bit-serial idiom (see [`CrcTablePlan`]). Matches
/// the exact recurrence + an 8-trip counter (a WRONG trip would make the
/// compile-time table wrong, so the trip==8 proof is mandatory). Fails closed
/// otherwise.
fn recognize_crc_table_loop(func: &X86ISelFunction, lp: &LoopInfo) -> Option<CrcTablePlan> {
    if !crc_table_enabled() {
        return None;
    }
    if lp.body.len() != 2 || lp.header == lp.latch {
        return None;
    }
    let header = lp.header;
    let latch = lp.latch;
    if !lp.body.contains(&header) || !lp.body.contains(&latch) {
        return None;
    }
    let _preheader = lp.preheader?;
    let hblock = func.blocks.get(&header)?;
    let lblock = func.blocks.get(&latch)?;
    if lblock.successors.as_slice() != [header] {
        return None;
    }
    if hblock.successors.len() != 2 || !hblock.successors.contains(&latch) {
        return None;
    }
    let exit = *hblock.successors.iter().find(|&&s| s != latch)?;

    let defs = DefIndex::build(func);
    let is_const = |v: VReg, k: i64| -> bool {
        defs.def_inst(func, v).is_some_and(|d| {
            d.opcode == X86Opcode::MovRI
                && matches!(d.operands.get(1), Some(X86ISelOperand::Imm(c)) if *c == k)
        })
    };
    let const_val = |v: VReg| -> Option<i64> {
        let d = defs.def_inst(func, v)?;
        if d.opcode == X86Opcode::MovRI
            && let Some(X86ISelOperand::Imm(c)) = d.operands.get(1)
        {
            return Some(*c);
        }
        None
    };

    // Match the recurrence `XorRR(new_crc, ShrRI(crc,1), AndRR(POLY, -(crc&1)))`.
    let mut found: Option<(VReg, u32)> = None; // (crc, poly)
    for inst in &lblock.insts {
        if inst.opcode != X86Opcode::XorRR {
            continue;
        }
        let [
            X86ISelOperand::VReg(_new),
            X86ISelOperand::VReg(p),
            X86ISelOperand::VReg(q),
        ] = inst.operands.as_slice()
        else {
            continue;
        };
        for (shr_side, and_side) in [(*p, *q), (*q, *p)] {
            let Some(shr) = defs.def_inst(func, shr_side) else {
                continue;
            };
            let crc = match (shr.opcode, shr.operands.as_slice()) {
                (X86Opcode::ShrRI, [_, X86ISelOperand::VReg(c), X86ISelOperand::Imm(1)]) => {
                    canon(func, &defs, *c)
                }
                _ => continue,
            };
            if crc.class != RegClass::Gpr32 {
                continue;
            }
            let Some(and) = defs.def_inst(func, and_side) else {
                continue;
            };
            let (aa, ab) = match (and.opcode, and.operands.as_slice()) {
                (X86Opcode::AndRR, [_, X86ISelOperand::VReg(a), X86ISelOperand::VReg(b)]) => {
                    (*a, *b)
                }
                _ => continue,
            };
            for (poly_side, mask_side) in [(aa, ab), (ab, aa)] {
                let Some(poly_i) = const_val(poly_side) else {
                    continue;
                };
                let poly = poly_i as u32;
                if poly == 0 {
                    continue;
                }
                // mask_side = SubRR(0, x) with x = AndRR(crc, 1).
                let Some(sub) = defs.def_inst(func, mask_side) else {
                    continue;
                };
                let x_side = match (sub.opcode, sub.operands.as_slice()) {
                    (X86Opcode::SubRR, [_, X86ISelOperand::VReg(z), X86ISelOperand::VReg(xx)])
                        if is_const(*z, 0) =>
                    {
                        canon(func, &defs, *xx)
                    }
                    _ => continue,
                };
                let Some(xand) = defs.def_inst(func, x_side) else {
                    continue;
                };
                let and1_ok = match (xand.opcode, xand.operands.as_slice()) {
                    (X86Opcode::AndRR, [_, X86ISelOperand::VReg(a), X86ISelOperand::VReg(b)]) => {
                        (canon(func, &defs, *a) == crc && is_const(*b, 1))
                            || (canon(func, &defs, *b) == crc && is_const(*a, 1))
                    }
                    _ => continue,
                };
                if and1_ok {
                    found = Some((crc, poly));
                }
            }
        }
    }
    let (crc, poly) = found?;

    // crc must be loop-carried (redefined in the latch).
    let crc_carried = lblock.insts.iter().any(|i| {
        matches!(i.opcode, X86Opcode::MovRR32 | X86Opcode::MovRR)
            && matches!(i.operands.first(), Some(X86ISelOperand::VReg(d)) if canon(func, &defs, *d) == crc)
    });
    if !crc_carried {
        return None;
    }

    // MANDATORY trip==8 proof: a Gpr32 counter incremented by 1 in the latch,
    // loop-carried, bounded < 8 in the header. (Wrong trip => wrong table.)
    let mut counter: Option<VReg> = None;
    for inst in &lblock.insts {
        let (iv, res) = match (inst.opcode, inst.operands.as_slice()) {
            (
                X86Opcode::AddRR,
                [
                    X86ISelOperand::VReg(res),
                    X86ISelOperand::VReg(iv),
                    X86ISelOperand::VReg(one),
                ],
            ) if is_const(*one, 1) => (*iv, *res),
            (
                X86Opcode::AddRI,
                [
                    X86ISelOperand::VReg(res),
                    X86ISelOperand::VReg(iv),
                    X86ISelOperand::Imm(1),
                ],
            ) => (*iv, *res),
            _ => continue,
        };
        let iv = canon(func, &defs, iv);
        if iv.class != RegClass::Gpr32 {
            continue;
        }
        let carried = lblock.insts.iter().any(|k| {
            matches!(k.opcode, X86Opcode::MovRR32 | X86Opcode::MovRR)
                && matches!(k.operands.first(), Some(X86ISelOperand::VReg(d)) if canon(func, &defs, *d) == iv)
                && matches!(k.operands.get(1), Some(X86ISelOperand::VReg(s)) if canon(func, &defs, *s) == canon(func, &defs, res))
        });
        if carried {
            counter = Some(iv);
        }
    }
    let c = counter?;
    let bound8 = hblock
        .insts
        .iter()
        .any(|inst| match (inst.opcode, inst.operands.as_slice()) {
            (X86Opcode::CmpRR, [X86ISelOperand::VReg(a), X86ISelOperand::VReg(b)]) => {
                (canon(func, &defs, *a) == c && is_const(*b, 8))
                    || (canon(func, &defs, *b) == c && is_const(*a, 8))
            }
            (X86Opcode::CmpRI, [X86ISelOperand::VReg(a), X86ISelOperand::Imm(8)]) => {
                canon(func, &defs, *a) == c
            }
            _ => false,
        });
    if !bound8 {
        return None;
    }

    Some(CrcTablePlan {
        latch,
        exit,
        crc,
        poly,
    })
}

/// Compute the 256-entry CRC table `T[b] = bitloop8(b)` for `poly`. Byte-for-byte
/// the reference 8-iteration recurrence — asserted equal in the unit test.
fn crc_table_256(poly: u32) -> [u32; 256] {
    let mut t = [0u32; 256];
    let mut b = 0usize;
    while b < 256 {
        let mut crc = b as u32;
        let mut j = 0;
        while j < 8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (poly & mask);
            j += 1;
        }
        t[b] = crc;
        b += 1;
    }
    t
}

/// Rewrite a recognized 8-bit CRC bit-loop to a table lookup. Builds a 256-entry
/// stack table (initialized ONCE in the entry block) and replaces the latch with
/// `crc = (crc>>8) ^ T[crc & 0xff]`, dropping the back-edge (the table does all 8
/// iterations' work in one step; the loop runs once and exits). The compile-time
/// table equals `bitloop8` by construction (crc_table_256 mirrors the recurrence).
fn apply_crc_table(func: &mut X86ISelFunction, plan: &CrcTablePlan) {
    let table = crc_table_256(plan.poly);
    // 1KB stack slot for the 256 u32 table.
    let slot = func.stack_slots.len() as u32;
    func.stack_slots.push(StackSlotInfo::new(1024, 4));

    let vr = |v: VReg| X86ISelOperand::VReg(v);
    let imm = |k: i64| X86ISelOperand::Imm(k);
    let slot_mem = |disp: i32| X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::StackSlot(slot)),
        disp,
    };

    // Initialize the table in the ENTRY block (runs once, dominates all uses):
    // 256 x (MovRI val; MovMR32 [slot + b*4], val).
    let mut init: Vec<X86ISelInst> = Vec::with_capacity(512);
    for (b, &val) in table.iter().enumerate() {
        let valreg = new_gpr32(func);
        init.push(X86ISelInst::new(
            X86Opcode::MovRI,
            vec![vr(valreg), imm(i64::from(val))],
        ));
        init.push(X86ISelInst::new(
            X86Opcode::MovMR32,
            vec![slot_mem((b * 4) as i32), vr(valreg)],
        ));
    }
    let entry = func.block_order[0];
    if let Some(eblock) = func.blocks.get_mut(&entry) {
        let tail = std::mem::take(&mut eblock.insts);
        init.extend(tail);
        eblock.insts = init;
    }

    // Rewrite the latch: crc = (crc>>8) ^ table[crc & 0xff]; jmp exit.
    let crc = plan.crc;
    let base = new_gpr64(func); // &table
    let crc64 = new_gpr64(func); // zext(crc)
    let idx = new_gpr64(func); // crc & 0xff
    let t = new_gpr32(func); // table[idx]
    let hi = new_gpr32(func); // crc >> 8
    let newc = new_gpr32(func); // (crc>>8) ^ t
    let latch_insts = vec![
        X86ISelInst::new(X86Opcode::Lea, vec![vr(base), slot_mem(0)]),
        X86ISelInst::new(X86Opcode::Movzx, vec![vr(crc64), vr(crc)]),
        X86ISelInst::new(X86Opcode::AndRI, vec![vr(idx), vr(crc64), imm(0xff)]),
        X86ISelInst::new(
            X86Opcode::MovRM32Sib,
            vec![
                vr(t),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(vr(base)),
                    index: Box::new(vr(idx)),
                    scale: 4,
                    disp: 0,
                },
            ],
        ),
        X86ISelInst::new(X86Opcode::ShrRI, vec![vr(hi), vr(crc), imm(8)]),
        X86ISelInst::new(X86Opcode::XorRR, vec![vr(newc), vr(hi), vr(t)]),
        X86ISelInst::new(X86Opcode::MovRR32, vec![vr(crc), vr(newc)]),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(plan.exit)]),
    ];
    if let Some(lblock) = func.blocks.get_mut(&plan.latch) {
        lblock.insts = latch_insts;
        lblock.successors = vec![plan.exit];
    }
}

/// Rewrite a heap-slice i64 sum reduction (`while k < v.len() { acc += v[k] }`)
/// to a runtime-gated packed PADDQ-accumulate loop, a covered horizontal
/// reduce, and the unchanged scalar loop as the remainder. See
/// [`HeapSumQPlan`] for the legality argument.
///
/// CFG before: `preheader -[jmp]-> header`.
/// CFG after:  `preheader -> VP0`;
///             `VP0: len = [len_slot+dlen]; vN = len & !1; vN!=0 ? VPS : header`;
///             `VPS: ptr = [ptr_slot+dptr]; replay slice-temp stores; vacc=[0;2]; -> VH`;
///             `VH: iv <u vN ? VB : VR`;
///             `VB: vacc = PADDQ(vacc, [ptr + iv*8 .. +16)); iv += 2; -> VH`;
///             `VR: acc += lane0(vacc) + lane1(vacc); -> header`.
fn apply_heap_sumq_plan(func: &mut X86ISelFunction, plan: &HeapSumQPlan) {
    // A fresh, distinct 16-byte scratch slot: first zeroed to seed `[0;2]`,
    // then reused to spill `vacc` for the covered horizontal reduce.
    let scratch_slot = func.stack_slots.len() as u32;
    func.stack_slots.push(StackSlotInfo::new(16, 16));

    // Fresh block ids.
    let base = next_block_id(func);
    let vp0 = Block(base);
    let vps = Block(base + 1);
    let vh = Block(base + 2);
    let vb = Block(base + 3);
    let vrb = Block(base + 4);

    // Fresh vregs.
    let rlen = new_gpr64(func); // &[len_slot]
    let lenv = new_gpr64(func); // runtime length
    let vn = new_gpr64(func); // len & !1
    let rptr = new_gpr64(func); // &[ptr_slot]
    let ptrv = new_gpr64(func); // data pointer
    let rs = new_gpr64(func); // scratch slot base
    let rz = new_gpr64(func); // constant 0
    let vacc = new_fpr128(func); // loop-carried packed lane-partials
    let pe = new_gpr64(func); // &elem[iv]
    let xe = new_fpr128(func); // packed pair of elements
    let two = new_gpr64(func);
    let niv = new_gpr64(func);
    let s0 = new_gpr64(func);
    let s1 = new_gpr64(func);
    let t01 = new_gpr64(func);
    let accf = new_gpr64(func);
    // Per replayed store: (&[src slot], loaded value) — allocated up front.
    let mut store_regs: Vec<(VReg, VReg)> = Vec::new();
    for _ in &plan.stores {
        store_regs.push((new_gpr64(func), new_gpr64(func)));
    }
    let rss = new_gpr64(func); // &[slice_slot] (store replay destination)

    let iv = plan.iv;
    let acc = plan.acc;

    let vr = |v: VReg| X86ISelOperand::VReg(v);
    let slot_addr = |slot: u32| X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::StackSlot(slot)),
        disp: 0,
    };
    let mem_d = |base: VReg, disp: i32| X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::VReg(base)),
        disp,
    };

    // VP0: len = [len_slot + dlen]; vN = len & !1; vN != 0 ? VPS : header.
    let vp0_insts = vec![
        X86ISelInst::new(X86Opcode::Lea, vec![vr(rlen), slot_addr(plan.len_slot)]),
        X86ISelInst::new(X86Opcode::MovRM, vec![vr(lenv), mem_d(rlen, plan.len_disp)]),
        X86ISelInst::new(
            X86Opcode::AndRI,
            vec![vr(vn), vr(lenv), X86ISelOperand::Imm(-2)],
        ),
        X86ISelInst::new(X86Opcode::CmpRI, vec![vr(vn), X86ISelOperand::Imm(0)]),
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::NE),
                X86ISelOperand::Block(vps),
            ],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(plan.header)]),
    ];
    func.blocks.insert(
        vp0,
        X86ISelBlock {
            insts: vp0_insts,
            successors: vec![vps, plan.header],
        },
    );

    // VPS: ptr = [ptr_slot + dptr]; replay the invariant slice-temp stores
    // once (the scalar loop performs the same idempotent stores on every
    // iteration, and vN >= 2 means it would have run at least once); seed
    // vacc = [0;2] through the fresh scratch slot.
    let mut vps_insts = vec![
        X86ISelInst::new(X86Opcode::Lea, vec![vr(rptr), slot_addr(plan.ptr_slot)]),
        X86ISelInst::new(X86Opcode::MovRM, vec![vr(ptrv), mem_d(rptr, plan.ptr_disp)]),
    ];
    if let Some(ss) = plan.slice_slot.filter(|_| !plan.stores.is_empty()) {
        vps_insts.push(X86ISelInst::new(
            X86Opcode::Lea,
            vec![vr(rss), slot_addr(ss)],
        ));
        for ((dest_disp, src_slot, src_disp), (rf, tv)) in plan.stores.iter().zip(store_regs.iter())
        {
            vps_insts.push(X86ISelInst::new(
                X86Opcode::Lea,
                vec![vr(*rf), slot_addr(*src_slot)],
            ));
            vps_insts.push(X86ISelInst::new(
                X86Opcode::MovRM,
                vec![vr(*tv), mem_d(*rf, *src_disp)],
            ));
            vps_insts.push(X86ISelInst::new(
                X86Opcode::MovMR,
                vec![mem_d(rss, *dest_disp), vr(*tv)],
            ));
        }
    }
    vps_insts.push(X86ISelInst::new(
        X86Opcode::Lea,
        vec![vr(rs), slot_addr(scratch_slot)],
    ));
    vps_insts.push(X86ISelInst::new(
        X86Opcode::MovRI,
        vec![vr(rz), X86ISelOperand::Imm(0)],
    ));
    for disp in [0, ELEM_SIZE_Q as i32] {
        vps_insts.push(X86ISelInst::new(
            X86Opcode::MovMR,
            vec![mem_d(rs, disp), vr(rz)],
        ));
    }
    vps_insts.push(X86ISelInst::new(
        X86Opcode::MovdquRM,
        vec![vr(vacc), mem_d(rs, 0)],
    ));
    vps_insts.push(X86ISelInst::new(
        X86Opcode::Jmp,
        vec![X86ISelOperand::Block(vh)],
    ));
    func.blocks.insert(
        vps,
        X86ISelBlock {
            insts: vps_insts,
            successors: vec![vh],
        },
    );

    // VH: iv <u vN ? VB : VR.
    let vh_insts = vec![
        X86ISelInst::new(X86Opcode::CmpRR, vec![vr(iv), vr(vn)]),
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(vb),
            ],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(vrb)]),
    ];
    func.blocks.insert(
        vh,
        X86ISelBlock {
            insts: vh_insts,
            successors: vec![vb, vrb],
        },
    );

    // VB: vacc += [ptr + iv*8 .. +16); iv += 2.
    let vb_insts = vec![
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![
                vr(pe),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(vr(ptrv)),
                    index: Box::new(vr(iv)),
                    scale: ELEM_SIZE_Q,
                    disp: 0,
                },
            ],
        ),
        X86ISelInst::new(X86Opcode::MovdquRM, vec![vr(xe), mem_d(pe, 0)]),
        X86ISelInst::new(X86Opcode::Paddq, vec![vr(vacc), vr(vacc), vr(xe)]),
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![vr(two), X86ISelOperand::Imm(LANES_Q)],
        ),
        X86ISelInst::new(X86Opcode::AddRR, vec![vr(niv), vr(iv), vr(two)]),
        X86ISelInst::new(X86Opcode::MovRR, vec![vr(iv), vr(niv)]),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(vh)]),
    ];
    func.blocks.insert(
        vb,
        X86ISelBlock {
            insts: vb_insts,
            successors: vec![vh],
        },
    );

    // VR: horizontal reduce (covered ops only: MOVDQU spill + two MovRM loads
    // + AddRRs), fold into the carried `acc`, fall into the scalar loop.
    let vr_insts = vec![
        X86ISelInst::new(X86Opcode::MovdquMR, vec![mem_d(rs, 0), vr(vacc)]),
        X86ISelInst::new(X86Opcode::MovRM, vec![vr(s0), mem_d(rs, 0)]),
        X86ISelInst::new(
            X86Opcode::MovRM,
            vec![vr(s1), mem_d(rs, ELEM_SIZE_Q as i32)],
        ),
        X86ISelInst::new(X86Opcode::AddRR, vec![vr(t01), vr(s0), vr(s1)]),
        X86ISelInst::new(X86Opcode::AddRR, vec![vr(accf), vr(acc), vr(t01)]),
        X86ISelInst::new(X86Opcode::MovRR, vec![vr(acc), vr(accf)]),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(plan.header)]),
    ];
    func.blocks.insert(
        vrb,
        X86ISelBlock {
            insts: vr_insts,
            successors: vec![plan.header],
        },
    );

    // Redirect the preheader's terminator from `header` to `VP0`.
    if let Some(pre) = func.blocks.get_mut(&plan.preheader) {
        for inst in pre.insts.iter_mut() {
            if inst.opcode == X86Opcode::Jmp
                && let Some(X86ISelOperand::Block(t)) = inst.operands.first_mut()
                && *t == plan.header
            {
                *t = vp0;
            }
        }
        pre.successors = pre
            .successors
            .iter()
            .map(|s| if *s == plan.header { vp0 } else { *s })
            .collect();
    }

    // Place the new blocks right after the preheader in the layout order.
    let new_order = [vp0, vps, vh, vb, vrb];
    if let Some(pos) = func.block_order.iter().position(|b| *b == plan.preheader) {
        for (offset, b) in new_order.into_iter().enumerate() {
            func.block_order.insert(pos + 1 + offset, b);
        }
    } else {
        func.block_order.extend(new_order);
    }
}

// ===========================================================================
// Register-argument i64 sum reduction (OWN-LENGTH, SINGLE-SLICE) — the
// `for i in 0..s.len() { acc = acc.wrapping_add(s[i]) }` loop where the slice
// `(ptr, len)` arrive in REGISTERS (a `&[i64]`/`Vec<i64>` argument, exposed by
// SROA promoting the fat-pointer stack home to vregs) rather than as stack-slot
// fields. This is the dominant real-world indexing-loop shape that the
// stack-slot recognizers (`recognize_heap_sumq_loop`) do not reach.
// ===========================================================================

/// A verified-legal i64 sum-reduction over a slice whose `(ptr, len)` are held
/// in loop-invariant registers, ready to be rewritten to a packed PADDQ loop +
/// covered horizontal reduce + the unchanged scalar remainder.
///
/// # The recognized shape (post-ISel, raw; post-SROA register form)
///
/// ```text
/// for i in 0..s.len() {             // header: i <u len   (len a REGISTER!)
///     acc = acc.wrapping_add(s[i]); // guard:  i <u len → Ud2 ; elem: load [ptr + i*8]
/// }                                 // ptr may be an invariant in-body reload
/// ```
///
/// # Legality by construction (all checked; any failure ⇒ stay scalar)
///
/// * **Own-length identity (bound == trip count).** The header bound and every
///   per-element trap-guard bound canonicalize to the *same* register
///   `len_reg`, which is proven loop-invariant (no definition inside the loop
///   body — a single reaching def outside it). So its value `len0` is fixed;
///   the header admits iteration `i` only if `i <u len0`, and each guard's
///   `i <u len0` provably passes. Eliding the guards in the packed body cannot
///   lose a trap, and the scalar reference performs the element load for every
///   `i in [0, len0)`.
/// * **No stores ⇒ no aliasing, invariant reloads sound.** The loop body
///   contains NO memory stores at all (a pure reduction). Therefore (a) there
///   is no store to reason about aliasing against, and (b) any body load whose
///   address is loop-invariant yields a loop-invariant value — memory is never
///   mutated in the loop — so the vector preheader may replay that load ONCE
///   and use its result for the whole packed loop.
/// * **Packed reads are exactly the scalar reads.** The element address is
///   `ptr0 + 8*i` with `ptr0` a loop-invariant pointer (an invariant register,
///   or the invariant reload above). The packed loop reads
///   `[ptr0 + 8*j, ptr0 + 8*j + 16)` for even `j < vN` with `vN = len0 & !1` —
///   byte-for-byte the union of the scalar loop's `j`/`j+1` reads and no byte
///   the scalar loop would not read, so validity is inherited (MOVDQU needs no
///   alignment).
/// * **Exact wrapping-add reduction.** `acc` is a loop-carried Gpr64 register
///   accumulator: written back exactly once per iteration as
///   `acc = AddRR(acc, elem)`, initialized outside the body, read by nothing
///   else inside the body, and never stored. i64 wrapping add over `Z/2^64` is
///   associative and commutative, so two lane-partials + a covered horizontal
///   fold reproduce the sequential sum bit-for-bit (same argument as
///   [`HeapSumQPlan`], PADDQ lanes).
/// * **Loop-exit register state matches / runtime gate.** Identical to
///   [`HeapSumQPlan`]: `iv` leaves at `len0` on both paths (unit stride from a
///   unique zero init), every other non-`acc`/`iv` body-def is proven unused
///   outside the loop, and `vN == 0` (len0 < 2) branches to the UNCHANGED
///   scalar loop with memory untouched.
///
/// Every emitted op (MOVDQU load/store, PADDQ, and the Lea/MovRM/MovRR/MovRI/
/// AndRI/CmpRI/CmpRR/AddRR/LeaSib/Jcc/Jmp glue) is proof-covered; this pass owns
/// only the legality decision above. Kill switch: `TCG_NO_X86_VEC_REGARG`.
struct RegArgSumQPlan {
    /// Which per-element term is summed: the bare element (Sum), or its square
    /// `elem*elem` (Square — an extra per-lane i64 packed multiply is inserted
    /// between the packed load and the PADDQ; see [`emit_i64_packed_mul`]).
    kind: RegArgSumQKind,
    /// The loop counter vreg (element index; init 0, +1 per scalar iteration).
    iv: VReg,
    /// The loop-carried i64 (Gpr64) scalar accumulator vreg.
    acc: VReg,
    /// Loop-invariant register holding the runtime length: the header bound AND
    /// every per-element guard bound (own-length identity — the SAME vreg).
    len_reg: VReg,
    /// The data-pointer source. If `ptr_reload`, the pointer is
    /// `load [ptr_base + ptr_disp]` (an invariant in-body reload the vector
    /// preheader replays once); otherwise the pointer IS `ptr_base` directly
    /// (and `ptr_disp == 0`).
    ptr_base: VReg,
    ptr_disp: i32,
    ptr_reload: bool,
    /// The SECOND data-pointer source (`Dot` only — the other slice of
    /// `acc += x[i]*y[i]`), same (base, disp, reload) convention as the first.
    /// `None` for `Sum`/`Square`.
    ptr2: Option<(VReg, i32, bool)>,
    /// The loop's preheader (its terminator is redirected to the vector CFG).
    preheader: Block,
    /// The scalar loop header (runtime-gate failure and the remainder enter it).
    header: Block,
}

/// The summed per-element term of a reg-arg i64 reduction: the bare loaded
/// element (`Sum`), the square `elem*elem` (`Square`, recognized as a body
/// `ImulRR(elem, elem)` whose product feeds the reduction add), or the
/// two-slice product `x[i]*y[i]` (`Dot`, recognized as `ImulRR(e1, e2)` of the
/// loop's EXACTLY-TWO element loads — each from its own invariant base, read at
/// the SAME index `iv`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum RegArgSumQKind {
    Sum,
    Square,
    Dot,
}

/// Kill switch for the register-argument reduction vectorizer tier. Defaults ON
/// at O2/O3; set `TCG_NO_X86_VEC_REGARG` (any value) to disable ONLY this tier
/// for forensic rollback / A-B comparison (mirrors `TCG_NO_VECTORIZE`, which
/// disables the whole pass, and `TCG_NO_X86_SROA`).
fn regarg_vectorize_enabled() -> bool {
    std::env::var_os("TCG_NO_X86_VEC_REGARG").is_none()
}

/// Sub-switch: recognition of the `Square` (`elem*elem`) reduction term. On by
/// default; set `TCG_NO_X86_VEC_DOT` (any value) to reject ONLY the square term
/// (it falls back to the always-correct scalar loop) while keeping the plain
/// `Sum` tier — a narrow forensic rollback for the packed-multiply compose.
fn regarg_square_enabled() -> bool {
    std::env::var_os("TCG_NO_X86_VEC_DOT").is_none()
}

/// Emit the SSE2 compose for per-lane `lo64(a*b)` on packed i64 (2 lanes) — the
/// exact low 64 bits of the scalar `wrapping_mul`, identical to the compose in
/// `apply_saxpyq_plan`'s `emit_group`:
///
/// ```text
///   t1    = PMULUDQ(a, b)                    // a_lo * b_lo (full 64b/lane)
///   bh    = PSRLQ(b, 32)                     // b_hi (LOGICAL shift)
///   t2    = PMULUDQ(a, bh)                   // a_lo * b_hi
///   ah    = PSRLQ(a, 32)                     // a_hi
///   t3    = PMULUDQ(ah, b)                   // a_hi * b_lo
///   cross = PSLLQ(PADDQ(t2, t3), 32)         // (a_lo*b_hi + a_hi*b_lo)<<32
///   prod  = PADDQ(t1, cross)                 // lo64(a*b)
/// ```
///
/// SOUND: `a*b mod 2^64 = a_lo*b_lo + ((a_lo*b_hi + a_hi*b_lo) mod 2^32)<<32`;
/// the `a_hi*b_hi<<64` term vanishes mod 2^64 and PSLLQ(.,32) auto-takes the
/// cross term mod 2^32. Sign-agnostic: two's-complement low 64 bits are the same
/// signed/unsigned, and PSRLQ is a LOGICAL (Ushr) shift so `a = a_lo + a_hi*2^32`
/// holds as the unsigned reading regardless of sign. Returns `(prod, insts)`;
/// every temp is fresh so callers get an independent chain. All ops are
/// proof-covered (same set as the saxpy packed multiply).
fn emit_i64_packed_mul(func: &mut X86ISelFunction, a: VReg, b: VReg) -> (VReg, Vec<X86ISelInst>) {
    let vr = |v: VReg| X86ISelOperand::VReg(v);
    let t1 = new_fpr128(func);
    let bh = new_fpr128(func);
    let t2 = new_fpr128(func);
    let ah = new_fpr128(func);
    let t3 = new_fpr128(func);
    let t4 = new_fpr128(func);
    let cross = new_fpr128(func);
    let prod = new_fpr128(func);
    let insts = vec![
        X86ISelInst::new(X86Opcode::Pmuludq, vec![vr(t1), vr(a), vr(b)]),
        X86ISelInst::new(
            X86Opcode::Psrlq,
            vec![vr(bh), vr(b), X86ISelOperand::Imm(32)],
        ),
        X86ISelInst::new(X86Opcode::Pmuludq, vec![vr(t2), vr(a), vr(bh)]),
        X86ISelInst::new(
            X86Opcode::Psrlq,
            vec![vr(ah), vr(a), X86ISelOperand::Imm(32)],
        ),
        X86ISelInst::new(X86Opcode::Pmuludq, vec![vr(t3), vr(ah), vr(b)]),
        X86ISelInst::new(X86Opcode::Paddq, vec![vr(t4), vr(t2), vr(t3)]),
        X86ISelInst::new(
            X86Opcode::Psllq,
            vec![vr(cross), vr(t4), X86ISelOperand::Imm(32)],
        ),
        X86ISelInst::new(X86Opcode::Paddq, vec![vr(prod), vr(t1), vr(cross)]),
    ];
    (prod, insts)
}

/// Unroll factor K for the reg-arg PADDQ reduction: the number of INDEPENDENT
/// packed accumulators (and thus PADDQs) the hot body emits per iteration, each
/// over a disjoint 2-element (LANES_Q) lane group. Group = `K * LANES_Q`
/// elements per iteration. Multiple accumulators break the single serial PADDQ
/// dependency chain (ILP), matching LLVM's reduction-split + unroll.
///
/// Soundness: regrouping a wrapping-add reduction into K partial sums that are
/// PADDQ-combined at the end is valid because i64 `wrapping_add` is associative
/// AND commutative over Z/2^64 — exactly the identity in
/// `reduction_split_proofs.rs` (used by `reduction_split.rs`). The recognizer
/// already restricts the op to `AddRR`, so this extension inherits that.
///
/// K MUST be a power of two: the packed-body gate `len & !(K*LANES_Q - 1)` is
/// emitted as a single `AndRI len, -(K*LANES_Q)`, and `-(m) == !(m-1)` in two's
/// complement ONLY when `m = K*LANES_Q` is a power of two. Non-power-of-two K is
/// clamped down to the nearest power of two (never up — never widens the group).
///
/// A/B kill switches:
///   * `TCG_NO_X86_VEC_UNROLL`   -> K=1 (single accumulator; the pre-extension
///     1-PADDQ/iter behavior, remainder loop dead).
///   * `TCG_X86_VEC_UNROLL_K=<n>` -> override the default (clamped to {1,2,4,8}).
///     Default K=2 (2 PADDQ/iter, 4 i64/iter — LLVM-parity structure).
fn regarg_unroll_k() -> i64 {
    if std::env::var_os("TCG_NO_X86_VEC_UNROLL").is_some() {
        return 1;
    }
    let mut k = 2i64;
    if let Some(v) = std::env::var_os("TCG_X86_VEC_UNROLL_K")
        && let Some(parsed) = v.to_str().and_then(|s| s.parse::<i64>().ok())
        && (1..=8).contains(&parsed)
    {
        k = parsed;
    }
    // Clamp DOWN to the nearest power of two in {1,2,4,8}. Never widen.
    if k >= 8 {
        8
    } else if k >= 4 {
        4
    } else if k >= 2 {
        2
    } else {
        1
    }
}

/// True iff `v`'s canonical vreg has NO definition inside the loop `body` — it
/// is defined outside the loop and never redefined in it, so its value is
/// loop-invariant. Conservative: any in-body def ⇒ not proven invariant ⇒ the
/// caller fails safe to the scalar loop.
fn is_reg_loop_invariant(
    func: &X86ISelFunction,
    defs: &DefIndex,
    body: &BTreeSet<Block>,
    v: VReg,
) -> bool {
    let c = canon(func, defs, v);
    for block_id in body {
        let Some(block) = func.blocks.get(block_id) else {
            return false;
        };
        for inst in &block.insts {
            if x86_produces_value(inst.opcode)
                && matches!(inst.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == c)
            {
                return false;
            }
        }
    }
    true
}

/// If `mem` is `MemAddr { base: VReg(b), disp }` whose canonical base is a
/// loop-invariant register, return `(canonical_base, disp)`. Used to classify a
/// body load as reading a fixed (invariant) address. Only sound to treat the
/// loaded VALUE as invariant when the loop performs no stores (the caller
/// enforces this), so nothing can mutate the address between iterations.
fn invariant_load_addr(
    func: &X86ISelFunction,
    defs: &DefIndex,
    body: &BTreeSet<Block>,
    mem: Option<&X86ISelOperand>,
) -> Option<(VReg, i64)> {
    match mem? {
        X86ISelOperand::MemAddr { base, disp } => match base.as_ref() {
            X86ISelOperand::VReg(b) => {
                let c = canon(func, defs, *b);
                if is_reg_loop_invariant(func, defs, body, c) {
                    Some((c, *disp as i64))
                } else {
                    None
                }
            }
            _ => None,
        },
        _ => None,
    }
}

/// True iff `op` references (directly, or via a mem base/index) a vreg whose
/// copy-canonical form equals `target`.
fn operand_refs_canon(
    func: &X86ISelFunction,
    defs: &DefIndex,
    op: &X86ISelOperand,
    target: VReg,
) -> bool {
    match op {
        X86ISelOperand::VReg(x) => canon(func, defs, *x) == target,
        X86ISelOperand::MemAddr { base, .. } => operand_refs_canon(func, defs, base, target),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            operand_refs_canon(func, defs, base, target)
                || operand_refs_canon(func, defs, index, target)
        }
        _ => false,
    }
}

/// Recognizer for the register-argument i64 sum-reduction shape (see
/// [`RegArgSumQPlan`]). Returns a legal plan, or `None` for anything else —
/// every rejection leaves the (always-correct) scalar loop in place.
fn recognize_regarg_sumq_loop(
    func: &X86ISelFunction,
    preds: &HashMap<Block, Vec<Block>>,
    idom: &HashMap<Block, Block>,
    lp: &LoopInfo,
) -> Option<RegArgSumQPlan> {
    if !regarg_vectorize_enabled() {
        return None;
    }
    let header = lp.header;
    let latch = lp.latch;
    let body = &lp.body;
    let preheader = lp.preheader?;
    let _ = idom;

    // No PHI pseudo anywhere in the loop (non-SSA at this stage).
    for block_id in body {
        let block = func.blocks.get(block_id)?;
        if block.insts.iter().any(|i| i.opcode == X86Opcode::Phi) {
            return None;
        }
    }

    let defs = DefIndex::build(func);
    let mut memo: HashMap<VReg, Prov> = HashMap::new();
    let dbg = std::env::var_os("TCG_DBG_REGARG").is_some();
    macro_rules! bail {
        ($($t:tt)*) => {{ if dbg { eprintln!("regarg-bail[{}]: {}", func.name, format!($($t)*)); } return None; }};
    }

    // 1. Header: `iv <u len_reg` with a RUNTIME REGISTER bound — the pinned
    //    CmpRR/Setcc(B)/Jcc(NE, body)/Jmp(exit) chain.
    let Some((lhs, rhs, t_body, t_exit)) = chase_below_branch(func, header) else {
        bail!("header chase_below_branch");
    };
    if !body.contains(&t_body) || body.contains(&t_exit) {
        bail!("header taken/fall not body/exit");
    }
    let iv = canon(func, &defs, lhs);
    if iv.class != RegClass::Gpr64 || !is_counter(func, &defs, iv, body) {
        bail!("iv {:?} not gpr64 counter", iv);
    }
    let len_reg = canon(func, &defs, rhs);
    if len_reg == iv || len_reg.class != RegClass::Gpr64 {
        bail!("len_reg {:?} == iv or not gpr64", len_reg);
    }
    // The length must be a proven loop-invariant register: the crux of the
    // own-length (bound == trip-count) identity is that this value never
    // changes in the loop, so `i <u len` at the header and at each guard are the
    // SAME predicate over the SAME `len0`.
    if !is_reg_loop_invariant(func, &defs, body, len_reg) {
        bail!("len_reg {:?} not loop-invariant", len_reg);
    }

    // 1b. The IV must enter the loop as EXACTLY zero: exactly ONE def outside
    //     the body, a `MovRR iv, <MovRI 0>` in the preheader (identical
    //     discipline to `recognize_heap_sumq_loop` — the packed loop pairs
    //     [iv, iv+1] from the entry value, so a non-zero/odd entry would break
    //     the packed-reads-are-exactly-scalar-reads argument at the tail).
    {
        let mut outside_defs = 0usize;
        let mut preheader_zero_init = false;
        for block_id in &func.block_order {
            if body.contains(block_id) {
                continue;
            }
            let Some(block) = func.blocks.get(block_id) else {
                continue;
            };
            for inst in &block.insts {
                if x86_produces_value(inst.opcode)
                    && matches!(inst.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == iv)
                {
                    outside_defs += 1;
                    if *block_id == preheader
                        && inst.opcode == X86Opcode::MovRR
                        && let Some(X86ISelOperand::VReg(s)) = inst.operands.get(1)
                        && const_of(func, &defs, *s) == Some(0)
                    {
                        preheader_zero_init = true;
                    }
                }
            }
        }
        if outside_defs != 1 || !preheader_zero_init {
            return None;
        }
    }

    // The header must have exactly one exit successor and one body successor,
    // and the preheader must be the header's only non-body pred.
    {
        let hsuccs = &func.blocks.get(&header)?.successors;
        let non_body: Vec<Block> = hsuccs
            .iter()
            .copied()
            .filter(|s| !body.contains(s))
            .collect();
        if non_body.len() != 1 {
            return None;
        }
        let empty = Vec::new();
        let hpreds = preds.get(&header).unwrap_or(&empty);
        let non_body_preds: Vec<Block> = hpreds
            .iter()
            .copied()
            .filter(|p| !body.contains(p))
            .collect();
        if non_body_preds != vec![preheader] {
            return None;
        }
    }
    // The preheader must reach the header ONLY via its terminating `Jmp` (the
    // apply rewrites exactly that operand); any `Jcc` targeting the header would
    // desync the successor list. Fail-safe: reject.
    {
        let pre = func.blocks.get(&preheader)?;
        match pre.insts.last() {
            Some(j)
                if j.opcode == X86Opcode::Jmp
                    && matches!(j.operands.first(), Some(X86ISelOperand::Block(t)) if *t == header) =>
                {}
            _ => return None,
        }
        for inst in &pre.insts {
            if inst.opcode == X86Opcode::Jcc
                && matches!(inst.operands.get(1), Some(X86ISelOperand::Block(t)) if *t == header)
            {
                return None;
            }
        }
    }

    // 2. Walk the body as a linear chain; every off-chain edge must be a pure
    //    `Ud2` trap guarded by the SAME `iv <u len_reg` compare (own-length).
    let header_succs = &func.blocks.get(&header)?.successors;
    let body_entry = unique_in_body_succ(header_succs, body)?;
    let mut chain: Vec<Block> = Vec::new();
    let mut visited: HashSet<Block> = HashSet::new();
    let mut cur = body_entry;
    loop {
        if !body.contains(&cur) || !visited.insert(cur) {
            return None;
        }
        chain.push(cur);
        let succs = &func.blocks.get(&cur)?.successors;
        let mut has_trap_edge = false;
        for s in succs {
            if body.contains(s) {
                continue;
            }
            if !is_pure_trap_block(func, *s) {
                return None;
            }
            has_trap_edge = true;
        }
        if has_trap_edge {
            let Some((glhs, grhs, gt_taken, gt_fall)) = chase_below_branch(func, cur) else {
                bail!("guard {:?} not chase_below_branch", cur);
            };
            if !body.contains(&gt_taken) || body.contains(&gt_fall) {
                bail!("guard {:?} taken/fall not body/trap", cur);
            }
            if canon(func, &defs, glhs) != iv {
                bail!(
                    "guard {:?} lhs {:?} != iv {:?}",
                    cur,
                    canon(func, &defs, glhs),
                    iv
                );
            }
            if canon(func, &defs, grhs) != len_reg {
                // The per-element bound differs from the trip-count bound: the
                // own-length identity FAILS (cross-length). Fail-safe to scalar.
                bail!(
                    "guard {:?} bound {:?} != len_reg {:?} (CROSS-LENGTH)",
                    cur,
                    canon(func, &defs, grhs),
                    len_reg
                );
            }
        }
        if cur == latch {
            break;
        }
        let next = unique_in_body_succ(succs, body)?;
        cur = next;
    }
    // The latch's only in-body successor must be the header (the back-edge).
    if unique_in_body_succ(&func.blocks.get(&latch)?.successors, body)? != header {
        return None;
    }
    // Every body block except the header must be on the chain (nothing hidden).
    for block_id in body {
        if *block_id != header && !visited.contains(block_id) {
            return None;
        }
    }

    // 3. Closed-world scan over header + chain: NO stores at all (a pure
    //    reduction — this makes aliasing impossible and any invariant-address
    //    reload sound), no calls, only whitelisted compute. Classify each load
    //    as either the element load (`[ptr + iv*8]`) or an invariant-address
    //    load (a pointer materialization).
    let mut elem_loads: Vec<(VReg, VReg)> = Vec::new(); // (dst, base_reg)
    let mut inv_loads: Vec<(VReg, VReg, i64)> = Vec::new(); // (dst, base, disp)
    for block_id in std::iter::once(&header).chain(chain.iter()) {
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            let op = inst.opcode;
            if op == X86Opcode::Call || op == X86Opcode::CallR || op == X86Opcode::CallM {
                return None;
            }
            if is_store_opcode(op) {
                bail!("store {:?} in body (not a pure reduction)", op);
            }
            if is_load_opcode(op) {
                if op != X86Opcode::MovRM {
                    return None; // 64-bit Gpr loads only.
                }
                let dst = match inst.operands.first() {
                    Some(X86ISelOperand::VReg(d)) if d.class == RegClass::Gpr64 => *d,
                    _ => return None,
                };
                let dc = canon(func, &defs, dst);
                if let Some(base) = heap_elem_base(func, &defs, iv, &mut memo, inst.operands.get(1))
                {
                    elem_loads.push((dc, base));
                } else if let Some((b, d)) =
                    invariant_load_addr(func, &defs, body, inst.operands.get(1))
                {
                    inv_loads.push((dc, b, d));
                } else {
                    return None; // unclassifiable load — refuse.
                }
            } else if !is_whitelisted_body_opcode(op) {
                return None;
            }
        }
    }

    // 4. Exactly ONE element load (Sum/Square) or exactly TWO (the two-slice
    //    Dot term `x[iv]*y[iv]` — classified in step 5); resolve EACH load's
    //    base to an invariant pointer — either a preceding invariant-address
    //    reload (replayed once), or an invariant register used directly.
    if elem_loads.is_empty() || elem_loads.len() > 2 {
        bail!(
            "elem_loads={} inv_loads={}",
            elem_loads.len(),
            inv_loads.len()
        );
    }
    let resolve_base = |elem_base: VReg| -> Option<(VReg, i64, bool)> {
        if let Some((_, b, d)) = inv_loads.iter().find(|(dst, ..)| *dst == elem_base) {
            Some((*b, *d, true))
        } else if is_reg_loop_invariant(func, &defs, body, elem_base) {
            Some((elem_base, 0i64, false))
        } else {
            None
        }
    };
    let (elem_dst, elem_base) = elem_loads[0];
    let Some((ptr_base, ptr_disp, ptr_reload)) = resolve_base(elem_base) else {
        bail!("elem_base {:?} not invariant/reloadable", elem_base);
    };
    // The second load's (dst, resolved base) — present iff this is a Dot shape.
    let second = if elem_loads.len() == 2 {
        let (e2_dst, e2_base) = elem_loads[1];
        let Some(resolved2) = resolve_base(e2_base) else {
            bail!("elem_base2 {:?} not invariant/reloadable", e2_base);
        };
        Some((e2_dst, resolved2))
    } else {
        None
    };

    // 5. Find the single loop-carried Gpr64 accumulator + its reduction add
    //    `acc = AddRR(acc, elem)` (identical discipline to `HeapSumQPlan`), or
    //    the square variant `acc = AddRR(acc, ImulRR(elem, elem))`.
    let mut found: Option<(VReg, (Block, usize), RegArgSumQKind)> = None; // (acc, add loc, kind)
    for block_id in &chain {
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            if !matches!(inst.opcode, X86Opcode::MovRR | X86Opcode::MovRR32) {
                continue;
            }
            let (acc, raw_src) = match (inst.operands.first(), inst.operands.get(1)) {
                (Some(X86ISelOperand::VReg(d)), Some(X86ISelOperand::VReg(s))) => (*d, *s),
                _ => continue,
            };
            if acc == iv || acc.class != RegClass::Gpr64 {
                continue;
            }
            let acc_new = canon(func, &defs, raw_src);
            let Some((add_block, add_idx)) = defs.single.get(&acc_new).copied() else {
                continue;
            };
            let add = func.blocks.get(&add_block)?.insts.get(add_idx)?;
            if add.opcode != X86Opcode::AddRR {
                continue;
            }
            let (x, y) = match (add.operands.get(1), add.operands.get(2)) {
                (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => (*x, *y),
                _ => continue,
            };
            let (cx, cy) = (canon(func, &defs, x), canon(func, &defs, y));
            let term = if cx == acc {
                cy
            } else if cy == acc {
                cx
            } else {
                continue; // not a self-accumulation.
            };
            // The summed term must be THE element load (Sum), the square
            // `ImulRR(elem_dst, elem_dst)` of that load (Square), or — when the
            // body has EXACTLY TWO element loads — the two-slice product
            // `ImulRR(e1, e2)` whose operands are exactly those two loads in
            // either order (Dot). Closed world: with two loads present, Sum and
            // Square shapes are impossible (a stray second load bails), and the
            // Dot mul must consume BOTH loads. Mirrors the local-array i32 Dot
            // recognizer's two-load classification.
            let kind = if let Some((e2_dst, _)) = second {
                let is_dot = matches!(defs.def_inst(func, term), Some(mul)
                    if mul.opcode == X86Opcode::ImulRR
                        && matches!((mul.operands.get(1), mul.operands.get(2)),
                            (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y)))
                                if (canon(func, &defs, *x) == elem_dst
                                        && canon(func, &defs, *y) == e2_dst)
                                    || (canon(func, &defs, *x) == e2_dst
                                        && canon(func, &defs, *y) == elem_dst)));
                if !is_dot || !regarg_square_enabled() {
                    continue; // not the (enabled) two-load product.
                }
                RegArgSumQKind::Dot
            } else if term == elem_dst {
                RegArgSumQKind::Sum
            } else {
                let is_square = matches!(defs.def_inst(func, term), Some(mul)
                    if mul.opcode == X86Opcode::ImulRR
                        && matches!((mul.operands.get(1), mul.operands.get(2)),
                            (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y)))
                                if canon(func, &defs, *x) == elem_dst
                                    && canon(func, &defs, *y) == elem_dst));
                if !is_square || !regarg_square_enabled() {
                    continue; // neither the bare load nor its (enabled) square.
                }
                RegArgSumQKind::Square
            };
            let has_outside_def = func.block_order.iter().any(|b| {
                !body.contains(b)
                    && func
                        .blocks
                        .get(b)
                        .map(|blk| {
                            blk.insts.iter().any(|i| {
                                x86_produces_value(i.opcode)
                                    && matches!(i.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == acc)
                            })
                        })
                        .unwrap_or(false)
            });
            if !has_outside_def {
                continue;
            }
            if found.is_some() {
                return None; // more than one reduction accumulator — refuse.
            }
            found = Some((acc, (add_block, add_idx), kind));
        }
    }
    let Some((acc, add_loc, kind)) = found else {
        bail!("no reduction accumulator (elem_dst={:?})", elem_dst);
    };

    // 6. `acc`'s value must flow ONLY into the reduction add. Every read of a
    //    vreg that copy-canonicalizes to `acc` (post-ISel routes the loop-
    //    carried accumulator through plain `MovRR` copies) is permitted only if
    //    it IS the reduction add, or a `MovRR`/`MovRR32` copy whose destination
    //    ALSO canonicalizes to `acc` — such a copy merely renames the
    //    accumulator, and its result can (recursively) reach nothing but the add
    //    or further copies. So `acc` cannot escape or reach the element
    //    address/bound (both proven to depend only on `iv`/`ptr`/`len`); with no
    //    stores in the body, its partial values are unobservable and reordering
    //    the additions is exact. Anything else that reads an `acc`-alias ⇒ bail.
    for block_id in body {
        let block = func.blocks.get(block_id)?;
        for (idx, inst) in block.insts.iter().enumerate() {
            if (*block_id, idx) == add_loc {
                continue;
            }
            let is_acc_alias_copy = matches!(inst.opcode, X86Opcode::MovRR | X86Opcode::MovRR32)
                && matches!(inst.operands.first(),
                    Some(X86ISelOperand::VReg(d)) if canon(func, &defs, *d) == acc);
            let produces = x86_produces_value(inst.opcode);
            for (opi, op) in inst.operands.iter().enumerate() {
                if produces && opi == 0 {
                    continue;
                }
                if operand_refs_canon(func, &defs, op, acc) {
                    if is_acc_alias_copy {
                        continue; // acc -> acc copy: benign renaming.
                    }
                    bail!(
                        "acc {:?} read by non-add {:?} at {:?}:{}",
                        acc,
                        inst.opcode,
                        block_id,
                        idx
                    );
                }
            }
        }
    }

    // 7. `acc` and `iv` must each have exactly ONE in-body def (the writeback).
    for carried in [acc, iv] {
        let mut n_defs = 0usize;
        for block_id in body {
            let block = func.blocks.get(block_id)?;
            for inst in &block.insts {
                if x86_produces_value(inst.opcode)
                    && matches!(inst.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == carried)
                {
                    n_defs += 1;
                }
            }
        }
        if n_defs != 1 {
            bail!("carried {:?} has {} in-body defs", carried, n_defs);
        }
    }

    // 8. No vreg defined ANYWHERE in the loop body (other than `acc`/`iv`) may
    //    be used outside the loop body — the packed path may skip the body's
    //    final execution, so a non-carried body def could be stale at the exit.
    let mut inner_defs: HashSet<VReg> = HashSet::new();
    for block_id in body {
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            if x86_produces_value(inst.opcode)
                && let Some(X86ISelOperand::VReg(d)) = inst.operands.first()
            {
                inner_defs.insert(*d);
            }
        }
    }
    inner_defs.remove(&acc);
    inner_defs.remove(&iv);
    for block_id in &func.block_order {
        if body.contains(block_id) {
            continue;
        }
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            let produces = x86_produces_value(inst.opcode);
            for (opi, op) in inst.operands.iter().enumerate() {
                if produces && opi == 0 {
                    continue;
                }
                if inner_defs.iter().any(|v| operand_references_vreg(op, *v)) {
                    bail!("inner def used outside body in {:?}", block_id);
                }
            }
        }
    }

    // The second slice's resolved pointer (Dot only — `second` is present iff
    // there were two element loads, and step 5 then classified the term as Dot
    // or refused).
    let ptr2 = match second {
        Some((_, (b2, d2, r2))) => Some((b2, i32::try_from(d2).ok()?, r2)),
        None => None,
    };
    if dbg {
        eprintln!(
            "regarg-OK[{}]: kind={:?} iv={:?} acc={:?} len={:?} ptr_base={:?} disp={} reload={} ptr2={:?}",
            func.name, kind, iv, acc, len_reg, ptr_base, ptr_disp, ptr_reload, ptr2
        );
    }
    Some(RegArgSumQPlan {
        kind,
        iv,
        acc,
        len_reg,
        ptr_base,
        ptr_disp: i32::try_from(ptr_disp).ok()?,
        ptr_reload,
        ptr2,
        preheader,
        header,
    })
}

/// Rewrite the register-argument i64 sum reduction (see [`RegArgSumQPlan`]) to a
/// K-way unrolled packed PADDQ reduction in front of the UNCHANGED scalar loop:
///
/// ```text
/// preheader -[jmp]-> VP0                      // was: preheader -> header
/// VP0:  vNk = len & !(K*LANES_Q - 1);         // unrolled-body bound (mult of K*2)
///       vN  = len & !(LANES_Q - 1) = len&!1;  // packed-remainder bound (mult of 2)
///       vN != 0 ? VPS : header                // len<2 fast-path: pure scalar
/// VPS:  ptrv = &data (reload or copy of invariant reg);
///       [rs+0]=0; [rs+8]=0; vacc0..vacc(K-1) = MOVDQU [rs]  // K zero accumulators
///       -> VH
/// // -- K-way unrolled body: K independent PADDQ chains over disjoint lane groups
/// VH:   iv <u vNk ? VB : RH                   // top-test
/// VB:   pe = &data[iv];                        // LeaSib ptrv + iv*8
///       for g in 0..K:                         // group g reads [pe + g*16 .. +16)
///         xe_g = MOVDQU [pe + g*16]; vacc_g = PADDQ(vacc_g, xe_g)
///       iv += K*LANES_Q; -> VH                 // 1 branch / K*2 elements
/// // -- packed remainder: leftover FULL 2-lane groups (0..K-1 of them)
/// RH:   iv <u vN ? RB : CB                     // top-test
/// RB:   pe = &data[iv]; xe = MOVDQU [pe]; vacc0 = PADDQ(vacc0, xe);
///       iv += LANES_Q; -> RH                   // 1 branch / 2 elements
/// // -- combine + covered horizontal reduce
/// CB:   vacc0 = PADDQ(vacc0, vacc_g) for g in 1..K;   // K-1 lane-group merges
///       [rs] = vacc0; s0=[rs]; s1=[rs+8]; acc += s0 + s1; -> header
/// // scalar loop UNCHANGED: sums the final `len % 2` element(s) from iv = vN.
/// ```
///
/// EXACTLY-ONCE COVERAGE (the classic unroll miscompile is an off-by-one here):
/// `iv` is shared across all three stages and advanced in place. The unrolled
/// body covers `[0, vNk)` in tiles of `K*LANES_Q` (each `xe_g` reads the disjoint
/// span `[iv+g*2, iv+g*2+2)`, so the K groups exactly tile `[iv, iv+K*2)`); it
/// halts with `iv == vNk` (a multiple of `K*LANES_Q`). The packed remainder
/// covers `[vNk, vN)` in tiles of `LANES_Q`, halting with `iv == vN` (a multiple
/// of `LANES_Q`). The scalar loop covers `[vN, len)`. Since
/// `vNk <= vN <= len` and every bound is a multiple of its stage's step, the
/// three half-open ranges partition `[0, len)` with no gap and no overlap —
/// every element is summed EXACTLY once. The K partial sums are PADDQ-combined
/// before the reduce; this regroup is sound because i64 `wrapping_add` is
/// associative and commutative over Z/2^64 (`reduction_split_proofs.rs`).
///
/// K = [`regarg_unroll_k`] (default 2). K=1 (kill switch) degenerates to the
/// original single-accumulator 1-PADDQ/iter loop: `vNk == vN`, the remainder
/// range is empty, and the combine is a no-op. Structurally mirrors
/// `apply_saxpyq_plan`'s unroll-2 packed body; the length/pointer come from
/// invariant registers (no slice-temp stores to replay).
fn apply_regarg_sumq_plan(func: &mut X86ISelFunction, plan: &RegArgSumQPlan) {
    // K independent PADDQ accumulators over disjoint 2-lane groups; group =
    // K*LANES_Q elements per unrolled iteration. K is a power of two so the
    // packed-body gate `len & !(group-1)` is a single `AndRI len, -group`.
    let k = regarg_unroll_k() as usize;
    let group = (k as i64) * LANES_Q; // elements consumed per unrolled iteration

    // A fresh, distinct 16-byte scratch slot: first zeroed to seed each `[0;2]`
    // accumulator, then reused to spill the combined `vacc0` for the covered
    // horizontal reduce.
    let scratch_slot = func.stack_slots.len() as u32;
    func.stack_slots.push(StackSlotInfo::new(16, 16));

    // Seven contiguous block ids (x86 regalloc replay requires contiguity):
    //   VP0 gate, VPS seed, VH/VB unrolled loop, RH/RB packed-remainder loop,
    //   CB combine+reduce.
    let base = next_block_id(func);
    let vp0 = Block(base);
    let vps = Block(base + 1);
    let vh = Block(base + 2);
    let vb = Block(base + 3);
    let rh = Block(base + 4);
    let rb = Block(base + 5);
    let cb = Block(base + 6);

    let vnk = new_gpr64(func); // len & !(group-1): unrolled-body bound
    let vn = new_gpr64(func); // len & !1: packed-remainder bound
    let ptrv = new_gpr64(func); // data pointer
    let rs = new_gpr64(func); // scratch slot base
    let rz = new_gpr64(func); // constant 0
    let vacc: Vec<VReg> = (0..k).map(|_| new_fpr128(func)).collect(); // K accumulators
    // Unrolled body temporaries.
    let pe = new_gpr64(func); // &elem[iv]
    let xe: Vec<VReg> = (0..k).map(|_| new_fpr128(func)).collect(); // K packed loads
    let stepu = new_gpr64(func); // = group
    let nivu = new_gpr64(func);
    // Remainder body temporaries.
    let per = new_gpr64(func);
    let xer = new_fpr128(func);
    let stepr = new_gpr64(func); // = LANES_Q
    let nivr = new_gpr64(func);
    // Second-slice (Dot) temporaries: the y-pointer, its per-stage element
    // addresses, and the K (+1 remainder) packed y-loads. Allocated only for a
    // Dot plan so Sum/Square emission is byte-identical to before.
    let dot2 = plan.ptr2.map(|_| {
        let ptrv2 = new_gpr64(func);
        let pe2 = new_gpr64(func);
        let ye: Vec<VReg> = (0..k).map(|_| new_fpr128(func)).collect();
        let per2 = new_gpr64(func);
        let yer = new_fpr128(func);
        (ptrv2, pe2, ye, per2, yer)
    });
    // Horizontal reduce temporaries.
    let s0 = new_gpr64(func);
    let s1 = new_gpr64(func);
    let t01 = new_gpr64(func);
    let accf = new_gpr64(func);

    let iv = plan.iv;
    let acc = plan.acc;
    let len_reg = plan.len_reg;

    let vr = |v: VReg| X86ISelOperand::VReg(v);
    let slot_addr = |slot: u32| X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::StackSlot(slot)),
        disp: 0,
    };
    let mem_d = |base: VReg, disp: i32| X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::VReg(base)),
        disp,
    };

    // VP0: vNk = len & !(group-1) (unrolled bound), vN = len & !1 (remainder
    // bound). Both WRITE fresh vregs so the scalar loop's `len_reg` is preserved.
    // `vN != 0 ? VPS : header` — len<2 has no full 2-lane group, so run pure
    // scalar (identical fast-path to the pre-unroll version).
    let vp0_insts = vec![
        X86ISelInst::new(
            X86Opcode::AndRI,
            vec![vr(vnk), vr(len_reg), X86ISelOperand::Imm(-group)],
        ),
        X86ISelInst::new(
            X86Opcode::AndRI,
            vec![vr(vn), vr(len_reg), X86ISelOperand::Imm(-LANES_Q)],
        ),
        X86ISelInst::new(X86Opcode::CmpRI, vec![vr(vn), X86ISelOperand::Imm(0)]),
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::NE),
                X86ISelOperand::Block(vps),
            ],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(plan.header)]),
    ];
    func.blocks.insert(
        vp0,
        X86ISelBlock {
            insts: vp0_insts,
            successors: vec![vps, plan.header],
        },
    );

    // VPS: materialize the data pointer (invariant reload, or a copy of the
    // invariant pointer register); seed each vacc_g = [0;2] via the fresh
    // scratch slot.
    let mut vps_insts = Vec::new();
    if plan.ptr_reload {
        vps_insts.push(X86ISelInst::new(
            X86Opcode::MovRM,
            vec![vr(ptrv), mem_d(plan.ptr_base, plan.ptr_disp)],
        ));
    } else {
        vps_insts.push(X86ISelInst::new(
            X86Opcode::MovRR,
            vec![vr(ptrv), vr(plan.ptr_base)],
        ));
    }
    // Dot: materialize the SECOND slice's pointer the same way.
    if let (Some((ptrv2, ..)), Some((base2, disp2, reload2))) = (&dot2, plan.ptr2) {
        if reload2 {
            vps_insts.push(X86ISelInst::new(
                X86Opcode::MovRM,
                vec![vr(*ptrv2), mem_d(base2, disp2)],
            ));
        } else {
            vps_insts.push(X86ISelInst::new(
                X86Opcode::MovRR,
                vec![vr(*ptrv2), vr(base2)],
            ));
        }
    }
    vps_insts.push(X86ISelInst::new(
        X86Opcode::Lea,
        vec![vr(rs), slot_addr(scratch_slot)],
    ));
    vps_insts.push(X86ISelInst::new(
        X86Opcode::MovRI,
        vec![vr(rz), X86ISelOperand::Imm(0)],
    ));
    for disp in [0, ELEM_SIZE_Q as i32] {
        vps_insts.push(X86ISelInst::new(
            X86Opcode::MovMR,
            vec![mem_d(rs, disp), vr(rz)],
        ));
    }
    for &vacc_g in &vacc {
        vps_insts.push(X86ISelInst::new(
            X86Opcode::MovdquRM,
            vec![vr(vacc_g), mem_d(rs, 0)],
        ));
    }
    vps_insts.push(X86ISelInst::new(
        X86Opcode::Jmp,
        vec![X86ISelOperand::Block(vh)],
    ));
    func.blocks.insert(
        vps,
        X86ISelBlock {
            insts: vps_insts,
            successors: vec![vh],
        },
    );

    // VH: iv <u vNk ? VB : RH (top-test — vNk may be 0, then skip straight to
    // the packed remainder).
    let vh_insts = vec![
        X86ISelInst::new(X86Opcode::CmpRR, vec![vr(iv), vr(vnk)]),
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(vb),
            ],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(rh)]),
    ];
    func.blocks.insert(
        vh,
        X86ISelBlock {
            insts: vh_insts,
            successors: vec![vb, rh],
        },
    );

    // VB: K-way unrolled body. pe = &data[iv]; for each group g in 0..K,
    // vacc_g += [pe + g*16 .. +16). The K groups tile [iv, iv + K*LANES_Q)
    // disjointly. iv += group.
    let mut vb_insts = vec![X86ISelInst::new(
        X86Opcode::LeaSib,
        vec![
            vr(pe),
            X86ISelOperand::SibMemAddr {
                base: Box::new(vr(ptrv)),
                index: Box::new(vr(iv)),
                scale: ELEM_SIZE_Q,
                disp: 0,
            },
        ],
    )];
    // Dot: the SECOND slice's element address at the SAME index `iv`.
    if let Some((ptrv2, pe2, ..)) = &dot2 {
        vb_insts.push(X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![
                vr(*pe2),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(vr(*ptrv2)),
                    index: Box::new(vr(iv)),
                    scale: ELEM_SIZE_Q,
                    disp: 0,
                },
            ],
        ));
    }
    for g in 0..k {
        // Byte displacement of group g: g * LANES_Q elements * ELEM_SIZE_Q bytes.
        let disp = (g as i64 * LANES_Q * ELEM_SIZE_Q as i64) as i32;
        vb_insts.push(X86ISelInst::new(
            X86Opcode::MovdquRM,
            vec![vr(xe[g]), mem_d(pe, disp)],
        ));
        // Sum: PADDQ the raw element. Square: PADDQ per-lane lo64(elem*elem).
        // Dot: load the second slice's group at the SAME displacement and PADDQ
        // per-lane lo64(x*y) — the identical packed-multiply compose, with two
        // DISTINCT vector operands.
        let term = match plan.kind {
            RegArgSumQKind::Sum => xe[g],
            RegArgSumQKind::Square => {
                let (prod, mul_insts) = emit_i64_packed_mul(func, xe[g], xe[g]);
                vb_insts.extend(mul_insts);
                prod
            }
            RegArgSumQKind::Dot => {
                let (_, pe2, ye, ..) = dot2.as_ref().expect("Dot plan carries ptr2");
                vb_insts.push(X86ISelInst::new(
                    X86Opcode::MovdquRM,
                    vec![vr(ye[g]), mem_d(*pe2, disp)],
                ));
                let (prod, mul_insts) = emit_i64_packed_mul(func, xe[g], ye[g]);
                vb_insts.extend(mul_insts);
                prod
            }
        };
        vb_insts.push(X86ISelInst::new(
            X86Opcode::Paddq,
            vec![vr(vacc[g]), vr(vacc[g]), vr(term)],
        ));
    }
    vb_insts.push(X86ISelInst::new(
        X86Opcode::MovRI,
        vec![vr(stepu), X86ISelOperand::Imm(group)],
    ));
    vb_insts.push(X86ISelInst::new(
        X86Opcode::AddRR,
        vec![vr(nivu), vr(iv), vr(stepu)],
    ));
    vb_insts.push(X86ISelInst::new(X86Opcode::MovRR, vec![vr(iv), vr(nivu)]));
    vb_insts.push(X86ISelInst::new(
        X86Opcode::Jmp,
        vec![X86ISelOperand::Block(vh)],
    ));
    func.blocks.insert(
        vb,
        X86ISelBlock {
            insts: vb_insts,
            successors: vec![vh],
        },
    );

    // RH: iv <u vN ? RB : CB. Packed remainder over the leftover full 2-lane
    // groups (the 0..K-1 groups between vNk and vN).
    let rh_insts = vec![
        X86ISelInst::new(X86Opcode::CmpRR, vec![vr(iv), vr(vn)]),
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(rb),
            ],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(cb)]),
    ];
    func.blocks.insert(
        rh,
        X86ISelBlock {
            insts: rh_insts,
            successors: vec![rb, cb],
        },
    );

    // RB: one 2-lane group into vacc0; iv += LANES_Q. (Identical to the original
    // single-accumulator body.)
    let mut rb_insts = vec![
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![
                vr(per),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(vr(ptrv)),
                    index: Box::new(vr(iv)),
                    scale: ELEM_SIZE_Q,
                    disp: 0,
                },
            ],
        ),
        X86ISelInst::new(X86Opcode::MovdquRM, vec![vr(xer), mem_d(per, 0)]),
    ];
    // Sum vs Square vs Dot: same choice as the unrolled body (per-lane,
    // orthogonal). Dot loads the second slice's 2-lane group at the same index.
    let rterm = match plan.kind {
        RegArgSumQKind::Sum => xer,
        RegArgSumQKind::Square => {
            let (prod, mul_insts) = emit_i64_packed_mul(func, xer, xer);
            rb_insts.extend(mul_insts);
            prod
        }
        RegArgSumQKind::Dot => {
            let (ptrv2, _, _, per2, yer) = dot2.as_ref().expect("Dot plan carries ptr2");
            rb_insts.push(X86ISelInst::new(
                X86Opcode::LeaSib,
                vec![
                    vr(*per2),
                    X86ISelOperand::SibMemAddr {
                        base: Box::new(vr(*ptrv2)),
                        index: Box::new(vr(iv)),
                        scale: ELEM_SIZE_Q,
                        disp: 0,
                    },
                ],
            ));
            rb_insts.push(X86ISelInst::new(
                X86Opcode::MovdquRM,
                vec![vr(*yer), mem_d(*per2, 0)],
            ));
            let (prod, mul_insts) = emit_i64_packed_mul(func, xer, *yer);
            rb_insts.extend(mul_insts);
            prod
        }
    };
    rb_insts.extend([
        X86ISelInst::new(X86Opcode::Paddq, vec![vr(vacc[0]), vr(vacc[0]), vr(rterm)]),
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![vr(stepr), X86ISelOperand::Imm(LANES_Q)],
        ),
        X86ISelInst::new(X86Opcode::AddRR, vec![vr(nivr), vr(iv), vr(stepr)]),
        X86ISelInst::new(X86Opcode::MovRR, vec![vr(iv), vr(nivr)]),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(rh)]),
    ]);
    func.blocks.insert(
        rb,
        X86ISelBlock {
            insts: rb_insts,
            successors: vec![rh],
        },
    );

    // CB: combine vacc0 += vacc_g (g in 1..K) — sound because packed
    // wrapping-add is associative+commutative per lane (reduction_split_proofs).
    // Then the covered horizontal reduce of vacc0's two lanes into `acc`, and
    // fall into the UNCHANGED scalar loop for the `len % 2` remainder.
    let mut cb_insts = Vec::new();
    for g in 1..k {
        cb_insts.push(X86ISelInst::new(
            X86Opcode::Paddq,
            vec![vr(vacc[0]), vr(vacc[0]), vr(vacc[g])],
        ));
    }
    cb_insts.extend([
        X86ISelInst::new(X86Opcode::MovdquMR, vec![mem_d(rs, 0), vr(vacc[0])]),
        X86ISelInst::new(X86Opcode::MovRM, vec![vr(s0), mem_d(rs, 0)]),
        X86ISelInst::new(
            X86Opcode::MovRM,
            vec![vr(s1), mem_d(rs, ELEM_SIZE_Q as i32)],
        ),
        X86ISelInst::new(X86Opcode::AddRR, vec![vr(t01), vr(s0), vr(s1)]),
        X86ISelInst::new(X86Opcode::AddRR, vec![vr(accf), vr(acc), vr(t01)]),
        X86ISelInst::new(X86Opcode::MovRR, vec![vr(acc), vr(accf)]),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(plan.header)]),
    ]);
    func.blocks.insert(
        cb,
        X86ISelBlock {
            insts: cb_insts,
            successors: vec![plan.header],
        },
    );

    // Redirect the preheader's terminator from `header` to `VP0`.
    if let Some(pre) = func.blocks.get_mut(&plan.preheader) {
        for inst in pre.insts.iter_mut() {
            if inst.opcode == X86Opcode::Jmp
                && let Some(X86ISelOperand::Block(t)) = inst.operands.first_mut()
                && *t == plan.header
            {
                *t = vp0;
            }
        }
        pre.successors = pre
            .successors
            .iter()
            .map(|s| if *s == plan.header { vp0 } else { *s })
            .collect();
    }

    let new_order = [vp0, vps, vh, vb, rh, rb, cb];
    if let Some(pos) = func.block_order.iter().position(|b| *b == plan.preheader) {
        for (offset, b) in new_order.into_iter().enumerate() {
            func.block_order.insert(pos + 1 + offset, b);
        }
    } else {
        func.block_order.extend(new_order);
    }
}

// ===========================================================================
// Window-scan (naive substring search) vectorizer — b16 shape
// ===========================================================================
//
// Design of record: docs/b16-window-scan-vectorizer-design-2026-07-18.md.
//
// Scalar shape (2-level nest; M, N compile-time constants):
//
//   while s + M <= N {                      // outer: windows over hay
//       k = 0; ok = 1;
//       while k < M {                       // inner: constant trip M, break
//           if hay[s + k] != pat[k] { ok = 0; break; }
//           k += 1;
//       }
//       if ok { acc += 1; }
//       s += 1;
//   }
//
// The scalar early-exit `break` is ELIMINATED, not vectorized: 16 consecutive
// windows are compared branchlessly per vector iteration — for each pattern
// index k, `PCMPEQB(movdqu(hay[s+k..s+k+16]), splat(pat[k]))` answers all 16
// windows' "match at k?" at once; the M masks PAND-join into the all-M
// conjunction, and `POPCNT(V16I8MaskExtract(mask))` counts the matching
// windows. This is VALUE-equivalent: `ok` is a pure conjunction of the M byte
// equalities (the break has no side effects), and the guard/trap carriers in
// the scalar body cannot fire in the vectorized range (max byte touched is
// `(vs+15)+(M-1) <= N-2 < N` under the vector bound `vs <= N-M-16`). The
// scalar loop is kept untouched as the remainder.
struct WindowScanPlan {
    /// The outer window IV `s` (Gpr64; zero entry, unit stride).
    outer_iv: VReg,
    /// The outer loop-carried match counter (multi-def carrier vreg).
    acc_outer: VReg,
    /// The invariant haystack base pointer register.
    hay_base: VReg,
    /// The invariant (outer-invariant) pattern base pointer register.
    pat_base: VReg,
    /// Constant pattern length (1..=8).
    m: i64,
    /// Constant outer bound term (`s + m <= n`).
    n: i64,
    /// The outer preheader (its terminator is redirected to the vector CFG).
    preheader: Block,
    /// The outer scalar header (the vector remainder re-enters it).
    header: Block,
}

/// Kill switch for the window-scan vectorizer tier. Defaults ON at O2/O3
/// (flipped after the stage-2 gate: 24/24 differential matches across
/// m∈1..=8 / n∈23..=4096 / wrapper / aliasing shapes at O2+O3, and b16
/// measured 1.30× FASTER than LLVM — see
/// docs/b16-window-scan-vectorizer-design-2026-07-18.md). Set
/// `TCG_NO_X86_WINDOW_SCAN` (any value) to disable ONLY this tier for
/// forensic rollback / A-B comparison (mirrors `TCG_NO_X86_VEC_REGARG`).
fn window_scan_enabled() -> bool {
    std::env::var_os("TCG_NO_X86_WINDOW_SCAN").is_none()
}

/// [`chase_below_branch`] with a caller-chosen `Setcc` condition code (the
/// original hard-codes `B`; the window shapes need `BE` for `s+m <= n`).
fn chase_below_branch_cc(
    func: &X86ISelFunction,
    block_id: Block,
    want: X86CondCode,
) -> Option<(VReg, VReg, Block, Block)> {
    let block = func.blocks.get(&block_id)?;
    let n = block.insts.len();
    if n < 5 {
        return None;
    }
    let jcc = &block.insts[n - 2];
    let jmp = &block.insts[n - 1];
    if jcc.opcode != X86Opcode::Jcc || jmp.opcode != X86Opcode::Jmp {
        return None;
    }
    let taken = match (jcc.operands.first(), jcc.operands.get(1)) {
        (Some(X86ISelOperand::CondCode(X86CondCode::NE)), Some(X86ISelOperand::Block(t))) => *t,
        _ => return None,
    };
    let fallthrough = match jmp.operands.first() {
        Some(X86ISelOperand::Block(t)) => *t,
        _ => return None,
    };
    let cmpri = &block.insts[n - 3];
    if !matches!(cmpri.opcode, X86Opcode::CmpRI | X86Opcode::CmpRI8) {
        return None;
    }
    let mut cur = match (cmpri.operands.first(), cmpri.operands.get(1)) {
        (Some(X86ISelOperand::VReg(w)), Some(X86ISelOperand::Imm(0))) => *w,
        _ => return None,
    };
    let mut i = n - 3;
    while i > 0 {
        i -= 1;
        let inst = &block.insts[i];
        if !x86_produces_value(inst.opcode) {
            continue;
        }
        match inst.operands.first() {
            Some(X86ISelOperand::VReg(d)) if *d == cur => {}
            _ => continue,
        }
        match inst.opcode {
            X86Opcode::Movzx | X86Opcode::MovzxW | X86Opcode::MovRR | X86Opcode::MovRR32 => {
                match inst.operands.get(1) {
                    Some(X86ISelOperand::VReg(s)) => cur = *s,
                    _ => return None,
                }
            }
            X86Opcode::AndRI => match (inst.operands.get(1), inst.operands.get(2)) {
                (Some(X86ISelOperand::VReg(s)), Some(X86ISelOperand::Imm(1))) => cur = *s,
                _ => return None,
            },
            X86Opcode::Setcc => {
                if !matches!(
                    inst.operands.get(1),
                    Some(X86ISelOperand::CondCode(cc)) if *cc == want
                ) {
                    return None;
                }
                if i == 0 {
                    return None;
                }
                let prev = &block.insts[i - 1];
                if prev.opcode != X86Opcode::CmpRR {
                    return None;
                }
                return match (prev.operands.first(), prev.operands.get(1)) {
                    (Some(X86ISelOperand::VReg(l)), Some(X86ISelOperand::VReg(r))) => {
                        Some((*l, *r, taken, fallthrough))
                    }
                    _ => None,
                };
            }
            _ => return None,
        }
    }
    None
}

/// Match a Setcc-LESS boolean-test block tail (`…; CmpRI x, 0; Jcc NE, taken;
/// Jmp fall`), chasing `x` back through Movzx/copy/AndRI-1 to its source
/// vreg. Returns `(source, taken, fall)`. This is the `if ok { … }` join
/// idiom (the bool was materialized in a DIFFERENT block, so there is no
/// in-block `Setcc` to stop at — the chase ends at the first def outside the
/// copy/mask set, or at a vreg with no unique def).
fn chase_bool_test(
    func: &X86ISelFunction,
    defs: &DefIndex,
    block_id: Block,
) -> Option<(VReg, Block, Block)> {
    let block = func.blocks.get(&block_id)?;
    let n = block.insts.len();
    if n < 3 {
        return None;
    }
    let jcc = &block.insts[n - 2];
    let jmp = &block.insts[n - 1];
    if jcc.opcode != X86Opcode::Jcc || jmp.opcode != X86Opcode::Jmp {
        return None;
    }
    let taken = match (jcc.operands.first(), jcc.operands.get(1)) {
        (Some(X86ISelOperand::CondCode(X86CondCode::NE)), Some(X86ISelOperand::Block(t))) => *t,
        _ => return None,
    };
    let fall = match jmp.operands.first() {
        Some(X86ISelOperand::Block(t)) => *t,
        _ => return None,
    };
    let cmpri = &block.insts[n - 3];
    if !matches!(cmpri.opcode, X86Opcode::CmpRI | X86Opcode::CmpRI8) {
        return None;
    }
    let mut cur = match (cmpri.operands.first(), cmpri.operands.get(1)) {
        (Some(X86ISelOperand::VReg(w)), Some(X86ISelOperand::Imm(0))) => *w,
        _ => return None,
    };
    // Phase 1: positional in-block backward walk (the test block re-defines
    // its scratch vreg — Movzx then AndRI onto the same dst — so the def
    // index alone cannot chase it).
    let mut i = n - 3;
    while i > 0 {
        i -= 1;
        let inst = &block.insts[i];
        if !x86_produces_value(inst.opcode) {
            continue;
        }
        match inst.operands.first() {
            Some(X86ISelOperand::VReg(d)) if *d == cur => {}
            _ => continue,
        }
        match inst.opcode {
            X86Opcode::Movzx | X86Opcode::MovzxW | X86Opcode::MovRR | X86Opcode::MovRR32 => {
                match inst.operands.get(1) {
                    Some(X86ISelOperand::VReg(s)) => cur = *s,
                    _ => return None,
                }
            }
            X86Opcode::AndRI => match (inst.operands.get(1), inst.operands.get(2)) {
                (Some(X86ISelOperand::VReg(s)), Some(X86ISelOperand::Imm(1))) => cur = *s,
                _ => return None,
            },
            _ => return None,
        }
    }
    // Phase 2: chase through copy/zext/mask defs cross-block via the def
    // index, stopping at the first non-copy (or multi-def) source.
    for _ in 0..16 {
        let Some(inst) = defs.def_inst(func, cur) else {
            return Some((cur, taken, fall));
        };
        match inst.opcode {
            X86Opcode::Movzx | X86Opcode::MovzxW | X86Opcode::MovRR | X86Opcode::MovRR32 => {
                match inst.operands.get(1) {
                    Some(X86ISelOperand::VReg(s)) => cur = *s,
                    _ => return Some((cur, taken, fall)),
                }
            }
            X86Opcode::AndRI => match (inst.operands.get(1), inst.operands.get(2)) {
                (Some(X86ISelOperand::VReg(s)), Some(X86ISelOperand::Imm(1))) => cur = *s,
                _ => return Some((cur, taken, fall)),
            },
            _ => return Some((cur, taken, fall)),
        }
    }
    None
}

/// [`canon`] that additionally chases through a bounds-carrier "self-def":
/// `TrapBoundsCheckExact [v, v, …]` names `v` as its first (def) operand, so
/// `DefIndex` counts it as a second def and drops `v` from the single-def
/// map, stopping the plain copy chase. When a multi-def vreg's defs are
/// EXACTLY one `MovRR v, s` plus identity trap carriers (`dst == src == v`),
/// the value is still the copy source — continue the chase through `s`.
fn canon_through_carrier(func: &X86ISelFunction, defs: &DefIndex, mut v: VReg) -> VReg {
    for _ in 0..64 {
        v = canon(func, defs, v);
        if defs.def_inst(func, v).is_some() {
            return v; // single-def non-copy root
        }
        // Multi-def (or def-less): collect every value-producing def of `v`.
        let mut copy_src: Option<VReg> = None;
        let mut clean = true;
        'scan: for block_id in &func.block_order {
            let Some(block) = func.blocks.get(block_id) else {
                continue;
            };
            for inst in &block.insts {
                if !x86_produces_value(inst.opcode) {
                    continue;
                }
                if !matches!(inst.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == v) {
                    continue;
                }
                match inst.opcode {
                    X86Opcode::TrapBoundsCheckExact => {
                        // Identity carrier: dst == checked src.
                        if !matches!(
                            inst.operands.get(1),
                            Some(X86ISelOperand::VReg(s)) if *s == v
                        ) {
                            clean = false;
                            break 'scan;
                        }
                    }
                    X86Opcode::MovRR | X86Opcode::MovRR32 => {
                        let Some(X86ISelOperand::VReg(s)) = inst.operands.get(1) else {
                            clean = false;
                            break 'scan;
                        };
                        if copy_src.replace(*s).is_some() {
                            clean = false; // more than one real def
                            break 'scan;
                        }
                    }
                    _ => {
                        clean = false;
                        break 'scan;
                    }
                }
            }
        }
        match (clean, copy_src) {
            (true, Some(s)) if s != v => v = s,
            _ => return v,
        }
    }
    v
}

/// Recognizer for the window-scan nest (see [`WindowScanPlan`] and the module
/// comment). Every rejection leaves the always-correct scalar nest in place.
#[allow(clippy::too_many_lines)]
fn recognize_window_scan_loop(
    func: &X86ISelFunction,
    preds: &HashMap<Block, Vec<Block>>,
    lp: &LoopInfo,
    all_loops: &[LoopInfo],
) -> Option<WindowScanPlan> {
    if !window_scan_enabled() {
        return None;
    }
    let header = lp.header;
    let latch = lp.latch;
    let body = &lp.body;
    let preheader = lp.preheader?;

    // No PHI pseudo anywhere in the loop (non-SSA at this stage).
    for block_id in body {
        let block = func.blocks.get(block_id)?;
        if block.insts.iter().any(|i| i.opcode == X86Opcode::Phi) {
            return None;
        }
    }

    let defs = DefIndex::build(func);
    let dbg = std::env::var_os("TCG_DBG_WINSCAN").is_some();
    macro_rules! bail {
        ($($t:tt)*) => {{ if dbg { eprintln!("winscan-bail[{}]: {}", func.name, format!($($t)*)); } return None; }};
    }

    // 0. Exactly ONE nested natural loop, strictly inside this one.
    let mut inner: Option<&LoopInfo> = None;
    for lp2 in all_loops {
        if lp2.header != header && lp2.body.is_subset(body) {
            if inner.is_some() {
                bail!("more than one inner loop");
            }
            inner = Some(lp2);
        }
    }
    let Some(inner) = inner else {
        bail!("no inner loop");
    };

    // 1. Outer header: `s + m <= n` — CmpRR/Setcc(BE) idiom over an AddRR of
    //    the IV and a constant, against a constant bound.
    let Some((olhs, orhs, t_body, t_exit)) = chase_below_branch_cc(func, header, X86CondCode::BE)
    else {
        bail!("outer header idiom");
    };
    if !body.contains(&t_body) || body.contains(&t_exit) {
        bail!("outer header taken/fall");
    }
    let Some(n_bound) = const_of(func, &defs, orhs) else {
        bail!("outer bound not const");
    };
    let add = defs.def_inst(func, canon(func, &defs, olhs))?;
    if add.opcode != X86Opcode::AddRR {
        bail!("outer lhs not AddRR");
    }
    let (ax, ay) = match (add.operands.get(1), add.operands.get(2)) {
        (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => (*x, *y),
        _ => bail!("outer AddRR operands"),
    };
    let (iv, m) = match (const_of(func, &defs, ay), const_of(func, &defs, ax)) {
        (Some(c), _) => (canon(func, &defs, ax), c),
        (_, Some(c)) => (canon(func, &defs, ay), c),
        _ => bail!("outer AddRR no const side"),
    };
    if !(1..=8).contains(&m) {
        bail!("m={m} out of 1..=8");
    }
    // At least one full 16-window vector iteration must exist.
    if n_bound < m + 16 {
        bail!("n={n_bound} too small for m={m}");
    }
    // The PSUBB byte-lane counter holds up to 255 per lane; each lane gains at
    // most 1 per vector iteration and there are at most (n-m)/16 iterations.
    if n_bound - m > 255 * 16 {
        bail!("n={n_bound} exceeds the byte-counter drain cap");
    }
    if iv.class != RegClass::Gpr64 || !is_counter(func, &defs, iv, body) {
        bail!("outer iv {iv:?} not a gpr64 counter");
    }

    // 1b. IV zero entry + preheader-Jmp-only discipline (same as regarg).
    {
        let mut outside_defs = 0usize;
        let mut preheader_zero_init = false;
        for block_id in &func.block_order {
            if body.contains(block_id) {
                continue;
            }
            let Some(block) = func.blocks.get(block_id) else {
                continue;
            };
            for inst in &block.insts {
                if x86_produces_value(inst.opcode)
                    && matches!(inst.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == iv)
                {
                    outside_defs += 1;
                    if *block_id == preheader
                        && inst.opcode == X86Opcode::MovRR
                        && let Some(X86ISelOperand::VReg(s)) = inst.operands.get(1)
                        && const_of(func, &defs, *s) == Some(0)
                    {
                        preheader_zero_init = true;
                    }
                }
            }
        }
        if outside_defs != 1 || !preheader_zero_init {
            bail!("iv entry not preheader-zero");
        }
    }
    {
        let hsuccs = &func.blocks.get(&header)?.successors;
        let non_body: Vec<Block> = hsuccs
            .iter()
            .copied()
            .filter(|s| !body.contains(s))
            .collect();
        if non_body.len() != 1 {
            bail!("outer header exits != 1");
        }
        let empty = Vec::new();
        let hpreds = preds.get(&header).unwrap_or(&empty);
        let non_body_preds: Vec<Block> = hpreds
            .iter()
            .copied()
            .filter(|p| !body.contains(p))
            .collect();
        if non_body_preds != vec![preheader] {
            bail!("outer header preds");
        }
        let pre = func.blocks.get(&preheader)?;
        match pre.insts.last() {
            Some(j)
                if j.opcode == X86Opcode::Jmp
                    && matches!(j.operands.first(), Some(X86ISelOperand::Block(t)) if *t == header) =>
                {}
            _ => bail!("preheader terminator"),
        }
        for inst in &pre.insts {
            if inst.opcode == X86Opcode::Jcc
                && matches!(inst.operands.get(1), Some(X86ISelOperand::Block(t)) if *t == header)
            {
                bail!("preheader Jcc to header");
            }
        }
    }

    // 2. The outer body entry must be the inner loop's preheader.
    let body_entry = unique_in_body_succ(&func.blocks.get(&header)?.successors, body)?;
    if inner.preheader != Some(body_entry) {
        bail!("body entry is not the inner preheader");
    }

    // 3. Inner header: `k < m` (Setcc B); natural exit = the ok-test block.
    let Some((klhs, krhs, kt, kf)) = chase_below_branch_cc(func, inner.header, X86CondCode::B)
    else {
        bail!("inner header idiom");
    };
    if const_of(func, &defs, krhs) != Some(m) {
        bail!("inner bound != m");
    }
    if !inner.body.contains(&kt) || inner.body.contains(&kf) || !body.contains(&kf) {
        bail!("inner header taken/fall");
    }
    let okb = kf;
    let k = canon(func, &defs, klhs);
    if k.class != RegClass::Gpr64 || !is_counter(func, &defs, k, &inner.body) {
        bail!("inner iv {k:?} not a gpr64 counter");
    }

    // 4. Inner body closed-world scan: classify the two byte loads, accept the
    //    statically-redundant `s+k < n` guard branch and the `k < m` trap
    //    carrier, refuse everything else.
    let mut hay_base: Option<VReg> = None;
    let mut pat_base: Option<VReg> = None;
    let mut break_target: Option<Block> = None;
    for block_id in &inner.body {
        let block = func.blocks.get(block_id)?;
        // Off-inner-body edges: the natural exit (okb), ONE break edge to an
        // outer-only block, and the guard's panic edge (outside the OUTER
        // body; legality argued in the module comment).
        for s in &block.successors {
            if inner.body.contains(s) || *s == okb {
                continue;
            }
            if body.contains(s) {
                if break_target.is_some() && break_target != Some(*s) {
                    bail!("two distinct break targets");
                }
                break_target = Some(*s);
            } else {
                // The panic-path edge: sound to drop from the VECTOR body only
                // because the guard proving it dead is matched here (its bound
                // is `n`, and every vectorized access has s+k < n).
                let Some((glhs, grhs, gt, _gf)) =
                    chase_below_branch_cc(func, *block_id, X86CondCode::B)
                else {
                    bail!("guard block {block_id:?} idiom");
                };
                if !inner.body.contains(&gt) {
                    bail!("guard taken not inner");
                }
                if const_of(func, &defs, grhs) != Some(n_bound) {
                    bail!("guard bound != n (cross-bound)");
                }
                let gadd = defs.def_inst(func, canon(func, &defs, glhs))?;
                if gadd.opcode != X86Opcode::AddRR {
                    bail!("guard lhs not AddRR");
                }
                let (gx, gy) = match (gadd.operands.get(1), gadd.operands.get(2)) {
                    (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => (*x, *y),
                    _ => bail!("guard AddRR operands"),
                };
                let sides = [canon(func, &defs, gx), canon(func, &defs, gy)];
                if !(sides.contains(&iv) && sides.contains(&k)) {
                    bail!("guard index not s+k");
                }
            }
        }
        for inst in &block.insts {
            let op = inst.opcode;
            if op == X86Opcode::Call || op == X86Opcode::CallR || op == X86Opcode::CallM {
                bail!("call in inner body");
            }
            if is_store_opcode(op) {
                bail!("store in inner body");
            }
            if op == X86Opcode::TrapBoundsCheckExact {
                // Accept ONLY the pat-side `k < m` carrier: it cannot fire
                // (inner header bound) and stays in the scalar tail.
                let ok_carrier = matches!(
                    (inst.operands.first(), inst.operands.get(2)),
                    (Some(X86ISelOperand::VReg(v)), Some(X86ISelOperand::Imm(c)))
                        if canon_through_carrier(func, &defs, *v) == k && *c == m
                );
                if !ok_carrier {
                    bail!("foreign trap carrier");
                }
                continue;
            }
            if is_load_opcode(op) {
                if op != X86Opcode::MovRM8 {
                    bail!("non-byte load in inner body");
                }
                let base = match inst.operands.get(1) {
                    Some(X86ISelOperand::MemAddr { base, disp: 0 }) => match base.as_ref() {
                        X86ISelOperand::VReg(b) => *b,
                        _ => bail!("load base not vreg"),
                    },
                    _ => bail!("load addr form"),
                };
                let badd = defs.def_inst(func, canon(func, &defs, base))?;
                if badd.opcode != X86Opcode::AddRR {
                    bail!("load base not AddRR");
                }
                let (bx, by) = match (badd.operands.get(1), badd.operands.get(2)) {
                    (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => (*x, *y),
                    _ => bail!("load base AddRR operands"),
                };
                let cx = canon_through_carrier(func, &defs, bx);
                let cy = canon_through_carrier(func, &defs, by);
                // pat: `inv + k`. hay: `inv + (s+k)`.
                let classify = |side: VReg, other: VReg| -> Option<(bool, VReg)> {
                    if side == k {
                        return Some((false, other)); // pat
                    }
                    let d = defs.def_inst(func, side)?;
                    if d.opcode != X86Opcode::AddRR {
                        return None;
                    }
                    let (ix, iy) = match (d.operands.get(1), d.operands.get(2)) {
                        (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => (*x, *y),
                        _ => return None,
                    };
                    let sides = [
                        canon_through_carrier(func, &defs, ix),
                        canon_through_carrier(func, &defs, iy),
                    ];
                    if sides.contains(&iv) && sides.contains(&k) {
                        Some((true, other)) // hay
                    } else {
                        None
                    }
                };
                let hit = classify(cx, cy).or_else(|| classify(cy, cx));
                match hit {
                    Some((true, b)) => {
                        if !is_reg_loop_invariant(func, &defs, body, b) {
                            bail!("hay base not invariant");
                        }
                        if hay_base.replace(b).is_some() {
                            bail!("two hay loads");
                        }
                    }
                    Some((false, b)) => {
                        if !is_reg_loop_invariant(func, &defs, body, b) {
                            bail!("pat base not invariant");
                        }
                        if pat_base.replace(b).is_some() {
                            bail!("two pat loads");
                        }
                    }
                    None => bail!(
                        "unclassifiable load base: base={base:?} canon={:?} cx={cx:?} cy={cy:?} \
                         k={k:?} iv={iv:?}",
                        canon(func, &defs, base)
                    ),
                }
            } else if !is_whitelisted_body_opcode(op) {
                bail!("inner body opcode {op:?}");
            }
        }
    }
    let hay_base = hay_base?;
    let pat_base = pat_base?;
    let Some(break_b) = break_target else {
        bail!("no break edge");
    };
    if hay_base == pat_base {
        bail!("hay base == pat base");
    }

    // 5. The ok-test join: `okb` tests a bool whose source is the constant 1
    //    materialized in the body entry (reaching okb means no break fired),
    //    so the taken side increments and the fall side passes through.
    let (ok_src, inc_b, noinc_b) = chase_bool_test(func, &defs, okb)?;
    if const_of(func, &defs, ok_src) != Some(1) {
        bail!("ok source not const 1");
    }
    if !body.contains(&inc_b) || !body.contains(&noinc_b) {
        bail!("ok-test targets outside body");
    }

    // 6. Accumulator chain. inc_b: `join = acc_in + 1`; noinc_b/break_b:
    //    `join = acc_in`; latch: `acc_outer = join`; body entry:
    //    `acc_in = copy(acc_outer)`.
    let find_addrr_plus1 = |b: Block| -> Option<(VReg, VReg)> {
        let block = func.blocks.get(&b)?;
        let mut hit = None;
        for inst in &block.insts {
            if inst.opcode == X86Opcode::AddRR {
                let d = match inst.operands.first() {
                    Some(X86ISelOperand::VReg(d)) => *d,
                    _ => return None,
                };
                let (x, y) = match (inst.operands.get(1), inst.operands.get(2)) {
                    (Some(X86ISelOperand::VReg(x)), Some(X86ISelOperand::VReg(y))) => (*x, *y),
                    _ => return None,
                };
                let src = if const_of(func, &defs, y) == Some(1) {
                    x
                } else if const_of(func, &defs, x) == Some(1) {
                    y
                } else {
                    return None;
                };
                if hit.is_some() {
                    return None; // exactly one increment
                }
                hit = Some((d, canon(func, &defs, src)));
            }
        }
        hit
    };
    let Some((sum_vreg, acc_outer)) = find_addrr_plus1(inc_b) else {
        bail!("inc block has no acc+1");
    };
    // `canon` chases the body-entry copy straight to the outer loop-carried
    // carrier (multi-def, so the chase stops exactly there).
    if acc_outer.class != RegClass::Gpr64 {
        bail!("acc not gpr64");
    }
    if acc_outer == iv || acc_outer == k {
        bail!("acc_outer identity");
    }
    if defs.def_inst(func, acc_outer).is_some() {
        bail!("acc_outer is single-def (not a loop carrier)");
    }
    // Latch: exactly one def of acc_outer, `MovRR acc_outer, join`.
    let join = {
        let block = func.blocks.get(&latch)?;
        let mut join = None;
        for inst in &block.insts {
            if x86_produces_value(inst.opcode)
                && matches!(inst.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == acc_outer)
            {
                if inst.opcode != X86Opcode::MovRR || join.is_some() {
                    bail!("latch acc writeback shape");
                }
                match inst.operands.get(1) {
                    Some(X86ISelOperand::VReg(s)) => join = Some(*s),
                    _ => bail!("latch acc src"),
                }
            }
        }
        let Some(j) = join else {
            bail!("no latch acc writeback");
        };
        j
    };
    // Each latch predecessor must assign `join` the right value.
    {
        let empty = Vec::new();
        let lpreds = preds.get(&latch).unwrap_or(&empty);
        let mut seen: HashSet<Block> = HashSet::new();
        for p in lpreds {
            if !seen.insert(*p) {
                continue;
            }
            let block = func.blocks.get(p)?;
            let mut assigned: Option<VReg> = None;
            for inst in &block.insts {
                if x86_produces_value(inst.opcode)
                    && matches!(inst.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == join)
                {
                    if inst.opcode != X86Opcode::MovRR && inst.opcode != X86Opcode::MovRR32 {
                        bail!("join def in {p:?} not a copy");
                    }
                    match inst.operands.get(1) {
                        Some(X86ISelOperand::VReg(s)) => assigned = Some(*s),
                        _ => bail!("join src in {p:?}"),
                    }
                }
            }
            let Some(a) = assigned else {
                bail!("latch pred {p:?} does not assign join");
            };
            let want_sum = *p == inc_b;
            let ca = canon(func, &defs, a);
            if want_sum {
                if ca != canon(func, &defs, sum_vreg) {
                    bail!("inc pred join != acc+1");
                }
            } else if ca != acc_outer {
                bail!("pred {p:?} join != acc passthrough");
            }
        }
        // The joining preds must be exactly the three recognized blocks.
        let expect: HashSet<Block> = [inc_b, noinc_b, break_b].into_iter().collect();
        if seen != expect {
            bail!("latch preds {seen:?} != {expect:?}");
        }
    }

    // 7. Outer-only closed-world scan: no loads/stores/calls/traps outside the
    //    inner loop; only whitelisted compute. (This covers body_entry, okb,
    //    inc_b, noinc_b, break_b and the latch.)
    for block_id in body {
        if *block_id == header || inner.body.contains(block_id) {
            continue;
        }
        let block = func.blocks.get(block_id)?;
        for inst in &block.insts {
            let op = inst.opcode;
            if is_load_opcode(op) || is_store_opcode(op) {
                bail!("memory op {op:?} outside inner loop");
            }
            if op == X86Opcode::Call || op == X86Opcode::CallR || op == X86Opcode::CallM {
                bail!("call outside inner loop");
            }
            if !is_whitelisted_body_opcode(op) {
                bail!("outer-only opcode {op:?}");
            }
        }
    }

    Some(WindowScanPlan {
        outer_iv: iv,
        acc_outer,
        hay_base,
        pat_base,
        m,
        n: n_bound,
        preheader,
        header,
    })
}

/// Emit the vector CFG for a recognized window scan: WP (splat + zero-counter
/// preheader), WH (bound check), WB (16-window branchless body), WE (byte-
/// counter drain epilogue). The scalar nest is untouched and handles the
/// remainder windows.
///
/// PROVEN-OPS-ONLY discipline: every emitted value op has a proof mapping
/// (the coverage-gate inventory fail-closes the function otherwise — PSHUFD/
/// PMOVMSKB are honestly-deferred, so splats go through a 16-byte scratch
/// slot round-trip and match-counting is a PSUBB byte-lane accumulate,
/// drained once through the same slot).
fn apply_window_scan_plan(func: &mut X86ISelFunction, plan: &WindowScanPlan) {
    let m = plan.m as usize;

    // A fresh 16-byte scratch slot: zero-seeds the byte counter, then builds
    // each pattern splat, then drains the counter in the epilogue.
    let scratch_slot = func.stack_slots.len() as u32;
    func.stack_slots.push(StackSlotInfo::new(16, 16));

    let base = next_block_id(func);
    let wp = Block(base);
    let wh = Block(base + 1);
    let wb = Block(base + 2);
    let we = Block(base + 3);

    let vs = new_gpr64(func); // vector window index
    let bnd = new_gpr64(func); // n - m - 15 (vs <u bnd gates the body)
    let rs = new_gpr64(func); // scratch slot base
    let rz = new_gpr64(func); // constant 0
    let pe = new_gpr64(func); // &hay[vs]
    let step = new_gpr64(func); // 16
    let nvs = new_gpr64(func); // vs + 16
    let splat_mul = new_gpr64(func); // 0x0101010101010101
    let vcnt = new_fpr128(func); // per-lane match counter (vcnt -= mask)
    let pat_bytes: Vec<VReg> = (0..m).map(|_| new_gpr32(func)).collect();
    let pat_wide: Vec<VReg> = (0..m).map(|_| new_gpr64(func)).collect();
    let pat_rep: Vec<VReg> = (0..m).map(|_| new_gpr64(func)).collect();
    let splats: Vec<VReg> = (0..m).map(|_| new_fpr128(func)).collect();
    let wins: Vec<VReg> = (0..m).map(|_| new_fpr128(func)).collect();
    // Epilogue drain temporaries: 16 byte loads + a running accumulator chain.
    let lane_b: Vec<VReg> = (0..16).map(|_| new_gpr32(func)).collect();
    let lane_w: Vec<VReg> = (0..16).map(|_| new_gpr64(func)).collect();
    let acc_run: Vec<VReg> = (0..16).map(|_| new_gpr64(func)).collect();

    let vr = |v: VReg| X86ISelOperand::VReg(v);
    let slot_addr = |disp: i32| X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::StackSlot(scratch_slot)),
        disp,
    };
    let mem_d = |base: VReg, disp: i32| X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::VReg(base)),
        disp,
    };
    let _ = slot_addr;

    // WP: rs = &scratch; zero-seed vcnt via the slot; build each pattern
    // splat: rep64 = pat[j] * 0x0101010101010101, stored to both slot halves,
    // reloaded as a 16-byte splat. Then vs = iv (the required zero entry).
    let mut wp_insts = vec![
        X86ISelInst::new(
            X86Opcode::Lea,
            vec![
                vr(rs),
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::StackSlot(scratch_slot)),
                    disp: 0,
                },
            ],
        ),
        X86ISelInst::new(X86Opcode::MovRI, vec![vr(rz), X86ISelOperand::Imm(0)]),
        X86ISelInst::new(X86Opcode::MovMR, vec![mem_d(rs, 0), vr(rz)]),
        X86ISelInst::new(X86Opcode::MovMR, vec![mem_d(rs, 8), vr(rz)]),
        X86ISelInst::new(X86Opcode::MovdquRM, vec![vr(vcnt), mem_d(rs, 0)]),
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![vr(splat_mul), X86ISelOperand::Imm(0x0101_0101_0101_0101)],
        ),
    ];
    for j in 0..m {
        wp_insts.push(X86ISelInst::new(
            X86Opcode::MovRM8,
            vec![vr(pat_bytes[j]), mem_d(plan.pat_base, j as i32)],
        ));
        wp_insts.push(X86ISelInst::new(
            X86Opcode::Movzx,
            vec![vr(pat_wide[j]), vr(pat_bytes[j])],
        ));
        wp_insts.push(X86ISelInst::new(
            X86Opcode::ImulRR,
            vec![vr(pat_rep[j]), vr(pat_wide[j]), vr(splat_mul)],
        ));
        wp_insts.push(X86ISelInst::new(
            X86Opcode::MovMR,
            vec![mem_d(rs, 0), vr(pat_rep[j])],
        ));
        wp_insts.push(X86ISelInst::new(
            X86Opcode::MovMR,
            vec![mem_d(rs, 8), vr(pat_rep[j])],
        ));
        wp_insts.push(X86ISelInst::new(
            X86Opcode::MovdquRM,
            vec![vr(splats[j]), mem_d(rs, 0)],
        ));
    }
    wp_insts.extend([
        X86ISelInst::new(X86Opcode::MovRR, vec![vr(vs), vr(plan.outer_iv)]),
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![vr(bnd), X86ISelOperand::Imm(plan.n - plan.m - 15)],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(wh)]),
    ]);
    func.blocks.insert(
        wp,
        X86ISelBlock {
            insts: wp_insts,
            successors: vec![wh],
        },
    );

    // WH: vs <u (n-m-15) ? WB : WE (drain, then scalar remainder).
    let wh_insts = vec![
        X86ISelInst::new(X86Opcode::CmpRR, vec![vr(vs), vr(bnd)]),
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(wb),
            ],
        ),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(we)]),
    ];
    func.blocks.insert(
        wh,
        X86ISelBlock {
            insts: wh_insts,
            successors: vec![wb, we],
        },
    );

    // WB: pe = hay + vs; for each pattern index j: 16-window compare at
    // displacement j; PAND-join; vcnt -= mask (mask lanes are -1 per match,
    // so the byte counter gains +1 per matching window; the recognizer caps
    // the trip count at 255 so a lane cannot wrap).
    let mut wb_insts = vec![X86ISelInst::new(
        X86Opcode::AddRR,
        vec![vr(pe), vr(plan.hay_base), vr(vs)],
    )];
    for j in 0..m {
        wb_insts.push(X86ISelInst::new(
            X86Opcode::MovdquRM,
            vec![vr(wins[j]), mem_d(pe, j as i32)],
        ));
        wb_insts.push(X86ISelInst::new(
            X86Opcode::Pcmpeqb,
            vec![vr(wins[j]), vr(wins[j]), vr(splats[j])],
        ));
        if j > 0 {
            wb_insts.push(X86ISelInst::new(
                X86Opcode::Pand,
                vec![vr(wins[0]), vr(wins[0]), vr(wins[j])],
            ));
        }
    }
    wb_insts.extend([
        X86ISelInst::new(X86Opcode::Psubb, vec![vr(vcnt), vr(vcnt), vr(wins[0])]),
        X86ISelInst::new(X86Opcode::MovRI, vec![vr(step), X86ISelOperand::Imm(16)]),
        X86ISelInst::new(X86Opcode::AddRR, vec![vr(nvs), vr(vs), vr(step)]),
        X86ISelInst::new(X86Opcode::MovRR, vec![vr(vs), vr(nvs)]),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(wh)]),
    ]);
    func.blocks.insert(
        wb,
        X86ISelBlock {
            insts: wb_insts,
            successors: vec![wh],
        },
    );

    // WE: drain the byte counter through the scratch slot (16 byte loads,
    // one accumulator chain), thread the resume index into the scalar IV,
    // and fall into the untouched scalar loop for the remainder windows.
    let mut we_insts = vec![X86ISelInst::new(
        X86Opcode::MovdquMR,
        vec![mem_d(rs, 0), vr(vcnt)],
    )];
    let mut acc_prev = plan.acc_outer;
    for lane in 0..16usize {
        we_insts.push(X86ISelInst::new(
            X86Opcode::MovRM8,
            vec![vr(lane_b[lane]), mem_d(rs, lane as i32)],
        ));
        we_insts.push(X86ISelInst::new(
            X86Opcode::Movzx,
            vec![vr(lane_w[lane]), vr(lane_b[lane])],
        ));
        we_insts.push(X86ISelInst::new(
            X86Opcode::AddRR,
            vec![vr(acc_run[lane]), vr(acc_prev), vr(lane_w[lane])],
        ));
        acc_prev = acc_run[lane];
    }
    we_insts.extend([
        X86ISelInst::new(X86Opcode::MovRR, vec![vr(plan.acc_outer), vr(acc_prev)]),
        X86ISelInst::new(X86Opcode::MovRR, vec![vr(plan.outer_iv), vr(vs)]),
        X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(plan.header)]),
    ]);
    func.blocks.insert(
        we,
        X86ISelBlock {
            insts: we_insts,
            successors: vec![plan.header],
        },
    );

    // Redirect the preheader's terminator from the scalar header to WP.
    if let Some(pre) = func.blocks.get_mut(&plan.preheader) {
        for inst in pre.insts.iter_mut() {
            if inst.opcode == X86Opcode::Jmp
                && let Some(X86ISelOperand::Block(t)) = inst.operands.first_mut()
                && *t == plan.header
            {
                *t = wp;
            }
        }
        pre.successors = pre
            .successors
            .iter()
            .map(|s| if *s == plan.header { wp } else { *s })
            .collect();
    }

    let new_order = [wp, wh, wb, we];
    if let Some(pos) = func.block_order.iter().position(|b| *b == plan.preheader) {
        for (offset, b) in new_order.into_iter().enumerate() {
            func.block_order.insert(pos + 1 + offset, b);
        }
    } else {
        func.block_order.extend(new_order);
    }
}

fn next_block_id(func: &X86ISelFunction) -> u32 {
    func.block_order
        .iter()
        .map(|b| b.0)
        .max()
        .map(|m| m + 1)
        .unwrap_or(0)
}

fn next_block_id_after(func: &X86ISelFunction, after: Block) -> u32 {
    func.block_order
        .iter()
        .map(|b| b.0)
        .chain(std::iter::once(after.0))
        .max()
        .map(|m| m + 1)
        .unwrap_or(0)
}

fn new_gpr64(func: &mut X86ISelFunction) -> VReg {
    let id = func.next_vreg;
    func.next_vreg += 1;
    let v = VReg::new(id, RegClass::Gpr64);
    func.vreg_nominal_widths.insert(v, 64);
    v
}

fn new_gpr32(func: &mut X86ISelFunction) -> VReg {
    let id = func.next_vreg;
    func.next_vreg += 1;
    let v = VReg::new(id, RegClass::Gpr32);
    func.vreg_nominal_widths.insert(v, 32);
    v
}

fn new_fpr128(func: &mut X86ISelFunction) -> VReg {
    let id = func.next_vreg;
    func.next_vreg += 1;
    VReg::new(id, RegClass::Fpr128)
}

// ===========================================================================
// CFG / dominators / natural loops come from the arch-neutral
// `crate::mach_view` analyses (`CfgAnalysis::compute` = predecessor_map, RPO,
// Cooper/Harvey/Kennedy idom, natural-loop discovery — the same algorithms
// this file previously re-implemented privately; `dominates` is imported from
// there as well). ONE piece stays private because mach_view does not provide
// it: the vectorizer's SINGLE-latch rule. `GenericLoop` merges all back-edge
// latches (sorted by raw block index), while every recognizer in this file
// was written against the FIRST back-edge source in `block_order` scan order.
// `loops_from_cfg_analysis` re-selects that latch below.
// ===========================================================================

/// A natural loop on the x86 ISel CFG, with header and single latch retained.
struct LoopInfo {
    header: Block,
    latch: Block,
    /// ⚑ DETERMINISM: a `BTreeSet`, NOT a `HashSet`. This set is ITERATED to
    /// choose which block and which instruction to transform, so hash order
    /// leaks Rust's per-process `RandomState` seed into the emitted bytes —
    /// `v2_memfill` compiled to two different (both valid) binaries roughly
    /// 50/50 across builds. Same reasoning as the `BTreeMap` on
    /// `LoopForest::loops` in `loops.rs`; a verified compiler must be
    /// reproducible.
    body: BTreeSet<Block>,
    preheader: Option<Block>,
    #[allow(dead_code)]
    depth: u32,
}

/// Lower [`GenericLoop`]s into the vectorizer's [`LoopInfo`], applying the
/// PRIVATE single-latch rule: the latch is the first back-edge source
/// encountered while scanning `func.block_order` (the historical
/// `latches.entry(header).or_insert(block)` behavior of the deleted private
/// `find_natural_loops`). `GenericLoop::latches` holds exactly the set of
/// back-edge sources, so the first one in scan order is the one with the
/// minimal `block_order` position. The `unwrap_or(header)` fallback mirrors
/// the old `latches.get(header).copied().unwrap_or(*header)` (unreachable in
/// practice: every natural loop has at least one back edge).
fn loops_from_cfg_analysis(
    func: &X86ISelFunction,
    cfg_loops: &[GenericLoop<Block>],
) -> Vec<LoopInfo> {
    let order_pos: HashMap<Block, usize> = func
        .block_order
        .iter()
        .enumerate()
        .map(|(i, &b)| (b, i))
        .collect();
    cfg_loops
        .iter()
        .map(|lp| LoopInfo {
            header: lp.header,
            latch: lp
                .latches
                .iter()
                .copied()
                .min_by_key(|b| order_pos.get(b).copied().unwrap_or(usize::MAX))
                .unwrap_or(lp.header),
            // The CFG loop's body is a `HashSet`; collect into the
            // deterministic `BTreeSet` this pass iterates. (`latch` above
            // already takes the same care via `min_by_key`.)
            body: lp.body.iter().copied().collect(),
            preheader: lp.preheader,
            depth: lp.depth,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_lower::function::{Signature, StackSlotInfo};
    use trust_cg_lower::types::Type;

    // ------------------------------------------------------------------
    // A small builder that reproduces the exact post-ISel shape the bridge
    // emits for `for i in 0..N { c[i] = a[i] OP b[i]; }` over three distinct
    // local [i32;N] arrays: an entry block with three `Lea r,[StackSlot]`, a
    // preheader (`iv=0`), a header (`iv<N`), a 3-block body chain with one
    // bounds-check diamond (→ single-`Ud2`) per access, and a latch (`iv+=1`).
    // ------------------------------------------------------------------
    struct B {
        next: u32,
    }
    impl B {
        fn g(&mut self) -> VReg {
            let v = VReg::new(self.next, RegClass::Gpr64);
            self.next += 1;
            v
        }
        fn g32(&mut self) -> VReg {
            let v = VReg::new(self.next, RegClass::Gpr32);
            self.next += 1;
            v
        }
    }

    fn vr(v: VReg) -> X86ISelOperand {
        X86ISelOperand::VReg(v)
    }
    fn imm(i: i64) -> X86ISelOperand {
        X86ISelOperand::Imm(i)
    }
    fn inst(op: X86Opcode, ops: Vec<X86ISelOperand>) -> X86ISelInst {
        X86ISelInst::new(op, ops)
    }
    fn memaddr(base: VReg) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(vr(base)),
            disp: 0,
        }
    }

    /// Emit `dst = base + iv*4` via the ImulRR+AddRR idiom (matching isel), plus
    /// a trailing copy, returning the address vreg and the instruction stream.
    fn addr_of(b: &mut B, base: VReg, iv: VReg) -> (VReg, Vec<X86ISelInst>) {
        addr_of_scale(b, base, iv, 4)
    }

    /// Like `addr_of` but with an explicit per-element byte scale (models a
    /// `[uN; _]` array whose element is `scale` bytes). Uses the ImulRR+AddRR
    /// form, which the recognizer accepts via the `AddRR(SlotBase, ScaledIv)`
    /// arm.
    fn addr_of_scale(b: &mut B, base: VReg, iv: VReg, scale: i64) -> (VReg, Vec<X86ISelInst>) {
        let bp = b.g();
        let idx = b.g();
        let f4 = b.g();
        let mul = b.g();
        let add = b.g();
        let addc = b.g();
        let insts = vec![
            inst(X86Opcode::MovRR, vec![vr(bp), vr(base)]),
            inst(X86Opcode::MovRR, vec![vr(idx), vr(iv)]),
            inst(X86Opcode::MovRI, vec![vr(f4), imm(scale)]),
            inst(X86Opcode::ImulRR, vec![vr(mul), vr(idx), vr(f4)]),
            inst(X86Opcode::AddRR, vec![vr(add), vr(bp), vr(mul)]),
            inst(X86Opcode::MovRR, vec![vr(addc), vr(add)]),
        ];
        (addc, insts)
    }

    /// Emit `dst = &base[iv]` in the real-isel `LeaSib [base + iv*scale]` form
    /// (the exact shape the bridge produces for a `[uN; _]` element address with
    /// `scale` in {1,2,4,8}), returning the address vreg and the stream.
    fn addr_of_leasib(b: &mut B, base: VReg, iv: VReg, scale: u8) -> (VReg, Vec<X86ISelInst>) {
        let dst = b.g();
        let insts = vec![inst(
            X86Opcode::LeaSib,
            vec![
                vr(dst),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(vr(base)),
                    index: Box::new(vr(iv)),
                    scale,
                    disp: 0,
                },
            ],
        )];
        (dst, insts)
    }

    /// Emit the bounds-check tail `iv <u N ? cont : trap`.
    fn bounds_check(b: &mut B, iv: VReg, n: i64, cont: Block, trap: Block) -> Vec<X86ISelInst> {
        let ivc = b.g();
        let nn = b.g();
        vec![
            inst(X86Opcode::MovRR, vec![vr(ivc), vr(iv)]),
            inst(X86Opcode::MovRI, vec![vr(nn), imm(n)]),
            inst(X86Opcode::CmpRR, vec![vr(ivc), vr(nn)]),
            inst(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(cont),
                ],
            ),
            inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(trap)]),
        ]
    }

    struct LoopShape {
        func: X86ISelFunction,
        iv: VReg,
    }

    /// Build the canonical shape. `op` is the i32 arithmetic opcode
    /// (Add/Sub/And/Or/Xor). `dest_slot`/`lhs_slot`/`rhs_slot` select which of
    /// the three arrays are read/written (used to construct adversarial cases).
    /// `stride_imm` is the latch increment (1 = unit; other values model a
    /// non-unit stride). `alias_base` replaces the destination base with a
    /// non-`StackSlot` pointer when true.
    #[allow(clippy::too_many_arguments)]
    fn build_loop(
        n: i64,
        op: X86Opcode,
        lhs_slot: usize,
        rhs_slot: usize,
        dest_slot: usize,
        stride_imm: i64,
        alias_base: bool,
    ) -> LoopShape {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("vadd_test".to_string(), sig);
        func.stack_slots = vec![
            StackSlotInfo::new((n * 4) as u32, 4),
            StackSlotInfo::new((n * 4) as u32, 4),
            StackSlotInfo::new((n * 4) as u32, 4),
        ];
        let mut b = B { next: 0 };

        let bases = [b.g(), b.g(), b.g()];
        let iv = b.g();
        // Block ids.
        let entry = Block(0);
        let pre = Block(1);
        let header = Block(2);
        let b3 = Block(3);
        let b4 = Block(4);
        let b5 = Block(5);
        let latch = Block(6);
        let trap = Block(7);
        let exit = Block(8);
        for blk in [entry, pre, header, b3, b4, b5, latch, trap, exit] {
            func.ensure_block(blk);
        }

        // Entry: three Lea r,[StackSlot(k)].
        {
            let e = func.blocks.get_mut(&entry).unwrap();
            for (k, base) in bases.iter().enumerate() {
                e.insts.push(inst(
                    X86Opcode::Lea,
                    vec![
                        vr(*base),
                        X86ISelOperand::MemAddr {
                            base: Box::new(X86ISelOperand::StackSlot(k as u32)),
                            disp: 0,
                        },
                    ],
                ));
            }
            e.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(pre)]));
            e.successors = vec![pre];
        }
        // Preheader: iv = 0.
        {
            let zero = b.g();
            let p = func.blocks.get_mut(&pre).unwrap();
            p.insts.push(inst(X86Opcode::MovRI, vec![vr(zero), imm(0)]));
            p.insts.push(inst(X86Opcode::MovRR, vec![vr(iv), vr(zero)]));
            p.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            p.successors = vec![header];
        }
        // Header: iv <u N ? b3 : exit.
        {
            let t = b.g();
            let nn = b.g();
            let h = func.blocks.get_mut(&header).unwrap();
            h.insts.push(inst(X86Opcode::MovRR, vec![vr(t), vr(iv)]));
            h.insts.push(inst(X86Opcode::MovRI, vec![vr(nn), imm(n)]));
            h.insts.push(inst(X86Opcode::CmpRR, vec![vr(t), vr(nn)]));
            h.insts.push(inst(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(b3),
                ],
            ));
            h.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(exit)]));
            h.successors = vec![b3, exit];
        }
        // b3: bounds-check for the first source.
        {
            let checks = bounds_check(&mut b, iv, n, b4, trap);
            let blk = func.blocks.get_mut(&b3).unwrap();
            blk.insts.extend(checks);
            blk.successors = vec![b4, trap];
        }
        // b4: load lhs[iv]; bounds-check for the second source.
        let la;
        {
            let (addr, mut stream) = addr_of(&mut b, bases[lhs_slot], iv);
            la = b.g32();
            stream.push(inst(X86Opcode::MovRM32, vec![vr(la), memaddr(addr)]));
            stream.extend(bounds_check(&mut b, iv, n, b5, trap));
            let blk = func.blocks.get_mut(&b4).unwrap();
            blk.insts.extend(stream);
            blk.successors = vec![b5, trap];
        }
        // b5: load rhs[iv]; sum = la OP lb; bounds-check for the store.
        let sum;
        {
            let (addr, mut stream) = addr_of(&mut b, bases[rhs_slot], iv);
            let lb = b.g32();
            stream.push(inst(X86Opcode::MovRM32, vec![vr(lb), memaddr(addr)]));
            sum = b.g32();
            stream.push(inst(op, vec![vr(sum), vr(la), vr(lb)]));
            stream.extend(bounds_check(&mut b, iv, n, latch, trap));
            let blk = func.blocks.get_mut(&b5).unwrap();
            blk.insts.extend(stream);
            blk.successors = vec![latch, trap];
        }
        // latch: store dest[iv] = sum; iv += stride; back-edge.
        {
            let dest_base = if alias_base {
                // A pointer that is NOT a Lea-from-StackSlot (models aliasing).
                let p = b.g();
                let blk = func.blocks.get_mut(&latch).unwrap();
                blk.insts
                    .push(inst(X86Opcode::MovRI, vec![vr(p), imm(0x1000)]));
                p
            } else {
                bases[dest_slot]
            };
            let (addr, mut stream) = addr_of(&mut b, dest_base, iv);
            let sm = b.g32();
            stream.push(inst(X86Opcode::MovRR32, vec![vr(sm), vr(sum)]));
            stream.push(inst(X86Opcode::MovMR32, vec![memaddr(addr), vr(sm)]));
            let one = b.g();
            let niv = b.g();
            stream.push(inst(X86Opcode::MovRI, vec![vr(one), imm(stride_imm)]));
            stream.push(inst(X86Opcode::AddRR, vec![vr(niv), vr(iv), vr(one)]));
            stream.push(inst(X86Opcode::MovRR, vec![vr(iv), vr(niv)]));
            stream.push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            let blk = func.blocks.get_mut(&latch).unwrap();
            blk.insts.extend(stream);
            blk.successors = vec![header];
        }
        // trap: single Ud2.
        {
            let blk = func.blocks.get_mut(&trap).unwrap();
            blk.insts.push(inst(X86Opcode::Ud2, vec![]));
        }
        // exit: Ret.
        {
            let blk = func.blocks.get_mut(&exit).unwrap();
            blk.insts.push(inst(X86Opcode::Ret, vec![]));
        }

        func.next_vreg = b.next;
        LoopShape { func, iv }
    }

    fn count_op(func: &X86ISelFunction, op: X86Opcode) -> usize {
        func.blocks
            .values()
            .flat_map(|b| b.insts.iter())
            .filter(|i| i.opcode == op)
            .count()
    }

    #[test]
    fn vectorizes_distinct_array_add() {
        let LoopShape { mut func, iv } = build_loop(64, X86Opcode::AddRR, 0, 1, 2, 1, false);
        let blocks_before = func.block_order.len();
        assert!(X86Vectorize.run_on_function(&mut func), "should vectorize");
        // Two new blocks (vector header + body).
        assert_eq!(func.block_order.len(), blocks_before + 2);
        // Packed add + two packed loads + one packed store emitted.
        assert_eq!(count_op(&func, X86Opcode::Paddd), 1);
        assert_eq!(count_op(&func, X86Opcode::MovdquRM), 2);
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 1);
        // The original scalar loop (MovRM32 loads, MovMR32 store) is untouched.
        assert_eq!(count_op(&func, X86Opcode::MovRM32), 2);
        assert_eq!(count_op(&func, X86Opcode::MovMR32), 1);
        // The shared counter is reused: the vector body increments it by 4
        // (`AddRR niv, iv, four`) and there is exactly one `MovRI Imm(4)` for
        // the stride (the scalar loop uses Imm(4) only inside address scaling).
        assert!(func.blocks.values().flat_map(|b| b.insts.iter()).any(|i| {
            i.opcode == X86Opcode::AddRR
                && matches!(i.operands.get(1), Some(X86ISelOperand::VReg(d)) if *d == iv)
                && i.operands.len() == 3
        }));
        // The preheader's terminator was redirected off the scalar header (2)
        // onto a freshly-created vector-header block.
        let pre = func.blocks.get(&Block(1)).unwrap();
        let jmp_target = pre
            .insts
            .iter()
            .rev()
            .find(|i| i.opcode == X86Opcode::Jmp)
            .and_then(|i| match i.operands.first() {
                Some(X86ISelOperand::Block(t)) => Some(*t),
                _ => None,
            })
            .unwrap();
        assert_ne!(
            jmp_target,
            Block(2),
            "preheader must be redirected off header"
        );
        assert_eq!(pre.successors, vec![jmp_target]);
    }

    #[test]
    fn vectorizes_each_supported_op() {
        for (scalar, packed) in [
            (X86Opcode::AddRR, X86Opcode::Paddd),
            (X86Opcode::SubRR, X86Opcode::Psubd),
            (X86Opcode::AndRR, X86Opcode::Pand),
            (X86Opcode::OrRR, X86Opcode::Por),
            (X86Opcode::XorRR, X86Opcode::Pxor),
        ] {
            let LoopShape { mut func, .. } = build_loop(64, scalar, 0, 1, 2, 1, false);
            assert!(X86Vectorize.run_on_function(&mut func), "{scalar:?}");
            assert_eq!(count_op(&func, packed), 1, "{scalar:?} -> {packed:?}");
        }
    }

    #[test]
    fn rejects_reduction_dest_equals_source() {
        // c aliases a source slot (write slot 0, read slots 0 and 1): a
        // loop-carried dependence — must not vectorize.
        let LoopShape { mut func, .. } = build_loop(64, X86Opcode::AddRR, 0, 1, 0, 1, false);
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::Paddd), 0);
    }

    #[test]
    fn rejects_aliasable_pointer_base() {
        // The destination base is not a distinct local StackSlot (a raw
        // pointer): aliasing is possible — must not vectorize.
        let LoopShape { mut func, .. } = build_loop(64, X86Opcode::AddRR, 0, 1, 2, 1, true);
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::Paddd), 0);
    }

    #[test]
    fn rejects_non_unit_stride() {
        // iv += 2 (non-unit stride): the accesses are not contiguous — must not
        // vectorize.
        let LoopShape { mut func, .. } = build_loop(64, X86Opcode::AddRR, 0, 1, 2, 2, false);
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::Paddd), 0);
    }

    #[test]
    fn rejects_small_trip_count() {
        // N < lanes: no full vector iteration.
        let LoopShape { mut func, .. } = build_loop(3, X86Opcode::AddRR, 0, 1, 2, 1, false);
        assert!(!X86Vectorize.run_on_function(&mut func));
    }

    #[test]
    fn rejects_non_trap_side_exit() {
        // If a body side-exit targets a non-`Ud2` block (some observable path),
        // the loop must not be vectorized.
        let LoopShape { mut func, .. } = build_loop(64, X86Opcode::AddRR, 0, 1, 2, 1, false);
        // Corrupt the trap block so it is no longer a pure single-Ud2 block.
        let trap = Block(7);
        func.blocks.get_mut(&trap).unwrap().insts = vec![inst(X86Opcode::Ret, vec![])];
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::Paddd), 0);
    }

    // ------------------------------------------------------------------
    // Fill shape (`for i in 0..N { a[i] = v; }`) over ONE distinct, write-only
    // local `[uN;N]` array: entry (`Lea r,[StackSlot]` + any invariant value
    // setup), preheader (`iv=0`), header (`iv<N`), a bounds-check block
    // (→ single-`Ud2`), and a latch that stores `v` and increments the IV.
    // `elem_size` selects the element width (u8/u16/u32); `use_leasib` selects
    // the real-isel `LeaSib` address form vs the ImulRR+AddRR form; `value`
    // selects the stored value (constant / IV / runtime-invariant / etc.).
    // ------------------------------------------------------------------
    #[derive(Clone, Copy)]
    enum FillTestValue {
        /// `a[i] = k` — a compile-time constant (the vectorizable case).
        Const(i64),
        /// `a[i] = i` — a per-iteration-varying value (must stay scalar).
        Iv,
        /// `a[i] = <undefined runtime reg>` — no def at all (must stay scalar).
        RuntimeUndef,
        /// `a[i] = v` where `v` is a runtime value computed ONCE in the entry
        /// block (single-def, dominates the preheader, outside the loop body):
        /// provably loop-invariant — the vectorizable runtime case (v2_memfill).
        InvariantOutside,
        /// `a[i] = v` where `v` is recomputed INSIDE the loop body each iteration
        /// (single-def but in-body, IV-dependent): NOT invariant (must stay
        /// scalar). THE critical adversarial case.
        RedefinedInside,
    }

    fn store_op_for(elem_size: u8) -> X86Opcode {
        match elem_size {
            1 => X86Opcode::MovMR8,
            2 => X86Opcode::MovMR16,
            _ => X86Opcode::MovMR32,
        }
    }

    fn build_fill_loop(
        n: i64,
        elem_size: u8,
        alias_base: bool,
        use_leasib: bool,
        value: FillTestValue,
    ) -> LoopShape {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("vfill_test".to_string(), sig);
        func.stack_slots = vec![StackSlotInfo::new(
            (n * elem_size as i64) as u32,
            elem_size as u32,
        )];
        let mut b = B { next: 0 };

        let base = b.g();
        let iv = b.g();
        // An undefined "runtime" source used only by the RuntimeUndef case.
        let rext = b.g32();
        // A runtime value computed once in the entry block (InvariantOutside).
        let rinv = b.g32();
        // A per-element constant `1` materialized in the entry block, used to
        // build both the invariant and the in-body (adversarial) runtime values.
        let rone = b.g32();

        let entry = Block(0);
        let pre = Block(1);
        let header = Block(2);
        let b3 = Block(3);
        let latch = Block(4);
        let trap = Block(5);
        let exit = Block(6);
        for blk in [entry, pre, header, b3, latch, trap, exit] {
            func.ensure_block(blk);
        }

        // Entry: Lea base,[StackSlot(0)]; set up any invariant value.
        {
            let e = func.blocks.get_mut(&entry).unwrap();
            e.insts.push(inst(
                X86Opcode::Lea,
                vec![
                    vr(base),
                    X86ISelOperand::MemAddr {
                        base: Box::new(X86ISelOperand::StackSlot(0)),
                        disp: 0,
                    },
                ],
            ));
            // rone = 1 (used by InvariantOutside / RedefinedInside).
            e.insts.push(inst(X86Opcode::MovRI, vec![vr(rone), imm(1)]));
            // rinv = 40 | 1 — a runtime value computed ONCE, outside the loop.
            let r40 = b.g32();
            e.insts.push(inst(X86Opcode::MovRI, vec![vr(r40), imm(40)]));
            e.insts
                .push(inst(X86Opcode::OrRR, vec![vr(rinv), vr(r40), vr(rone)]));
            e.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(pre)]));
            e.successors = vec![pre];
        }
        // Preheader: iv = 0.
        {
            let zero = b.g();
            let p = func.blocks.get_mut(&pre).unwrap();
            p.insts.push(inst(X86Opcode::MovRI, vec![vr(zero), imm(0)]));
            p.insts.push(inst(X86Opcode::MovRR, vec![vr(iv), vr(zero)]));
            p.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            p.successors = vec![header];
        }
        // Header: iv <u N ? b3 : exit.
        {
            let t = b.g();
            let nn = b.g();
            let h = func.blocks.get_mut(&header).unwrap();
            h.insts.push(inst(X86Opcode::MovRR, vec![vr(t), vr(iv)]));
            h.insts.push(inst(X86Opcode::MovRI, vec![vr(nn), imm(n)]));
            h.insts.push(inst(X86Opcode::CmpRR, vec![vr(t), vr(nn)]));
            h.insts.push(inst(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(b3),
                ],
            ));
            h.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(exit)]));
            h.successors = vec![b3, exit];
        }
        // b3: bounds-check for the store (iv <u N ? latch : trap). For the
        // RedefinedInside case, ALSO recompute the stored value here (in-body).
        let rmod = b.g32();
        {
            let mut checks = bounds_check(&mut b, iv, n, latch, trap);
            if let FillTestValue::RedefinedInside = value {
                // rmod = iv | 1 — recomputed every iteration (in the loop body).
                checks.insert(0, inst(X86Opcode::OrRR, vec![vr(rmod), vr(iv), vr(rone)]));
            }
            let blk = func.blocks.get_mut(&b3).unwrap();
            blk.insts.extend(checks);
            blk.successors = vec![latch, trap];
        }
        // latch: store dest[iv] = value; iv += 1; back-edge.
        {
            let dest_base = if alias_base {
                // A pointer that is NOT a Lea-from-StackSlot (models aliasing).
                let p = b.g();
                let blk = func.blocks.get_mut(&latch).unwrap();
                blk.insts
                    .push(inst(X86Opcode::MovRI, vec![vr(p), imm(0x1000)]));
                p
            } else {
                base
            };
            let (addr, mut stream) = if use_leasib {
                addr_of_leasib(&mut b, dest_base, iv, elem_size)
            } else {
                addr_of_scale(&mut b, dest_base, iv, elem_size as i64)
            };
            // The value register stored into a[iv].
            let val_reg = match value {
                FillTestValue::Const(k) => {
                    let sm = b.g32();
                    stream.push(inst(X86Opcode::MovRI, vec![vr(sm), imm(k)]));
                    sm
                }
                FillTestValue::Iv => iv,
                FillTestValue::RuntimeUndef => rext,
                FillTestValue::InvariantOutside => rinv,
                FillTestValue::RedefinedInside => rmod,
            };
            stream.push(inst(
                store_op_for(elem_size),
                vec![memaddr(addr), vr(val_reg)],
            ));
            let one = b.g();
            let niv = b.g();
            stream.push(inst(X86Opcode::MovRI, vec![vr(one), imm(1)]));
            stream.push(inst(X86Opcode::AddRR, vec![vr(niv), vr(iv), vr(one)]));
            stream.push(inst(X86Opcode::MovRR, vec![vr(iv), vr(niv)]));
            stream.push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            let blk = func.blocks.get_mut(&latch).unwrap();
            blk.insts.extend(stream);
            blk.successors = vec![header];
        }
        // trap: single Ud2.
        {
            func.blocks
                .get_mut(&trap)
                .unwrap()
                .insts
                .push(inst(X86Opcode::Ud2, vec![]));
        }
        // exit: Ret.
        {
            func.blocks
                .get_mut(&exit)
                .unwrap()
                .insts
                .push(inst(X86Opcode::Ret, vec![]));
        }

        func.next_vreg = b.next;
        LoopShape { func, iv }
    }

    #[test]
    fn vectorizes_constant_fill() {
        let LoopShape { mut func, iv } =
            build_fill_loop(64, 4, false, false, FillTestValue::Const(0x1234));
        let blocks_before = func.block_order.len();
        let slots_before = func.stack_slots.len();
        assert!(X86Vectorize.run_on_function(&mut func), "should vectorize");
        // Three new blocks (vector preheader + header + body).
        assert_eq!(func.block_order.len(), blocks_before + 3);
        // One fresh 16-byte scratch slot for the packed constant.
        assert_eq!(func.stack_slots.len(), slots_before + 1);
        assert_eq!(func.stack_slots.last().unwrap().size, 16);
        // Packed store + one packed load of the scratch constant.
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 1);
        assert_eq!(count_op(&func, X86Opcode::MovdquRM), 1);
        // The scratch build is 4 covered i32 stores; the original scalar store
        // survives untouched (4 + 1 = 5 total MovMR32). No broadcast opcodes.
        assert_eq!(count_op(&func, X86Opcode::MovMR32), 5);
        assert_eq!(count_op(&func, X86Opcode::Pshufd), 0);
        // The shared counter is reused: the vector body increments it by 4.
        assert!(func.blocks.values().flat_map(|b| b.insts.iter()).any(|i| {
            i.opcode == X86Opcode::AddRR
                && matches!(i.operands.get(1), Some(X86ISelOperand::VReg(d)) if *d == iv)
                && i.operands.len() == 3
        }));
        // The preheader's terminator was redirected off the scalar header (2).
        let pre = func.blocks.get(&Block(1)).unwrap();
        let jmp_target = pre
            .insts
            .iter()
            .rev()
            .find(|i| i.opcode == X86Opcode::Jmp)
            .and_then(|i| match i.operands.first() {
                Some(X86ISelOperand::Block(t)) => Some(*t),
                _ => None,
            })
            .unwrap();
        assert_ne!(
            jmp_target,
            Block(2),
            "preheader must be redirected off header"
        );
        assert_eq!(pre.successors, vec![jmp_target]);
    }

    #[test]
    fn rejects_per_iteration_varying_fill() {
        // `a[i] = i` — the stored value is the IV, not a constant. There is no
        // covered broadcast for a per-iteration value; must stay scalar.
        let LoopShape { mut func, .. } = build_fill_loop(64, 4, false, false, FillTestValue::Iv);
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
    }

    #[test]
    fn rejects_variable_fill_value() {
        // `a[i] = <undefined runtime>` — the value has no reaching def, so it
        // cannot be proven loop-invariant; must stay scalar.
        let LoopShape { mut func, .. } =
            build_fill_loop(64, 4, false, false, FillTestValue::RuntimeUndef);
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
    }

    #[test]
    fn rejects_aliasable_fill_base() {
        // The destination base is not a distinct local StackSlot (a raw
        // pointer): aliasing is possible — must not vectorize.
        let LoopShape { mut func, .. } =
            build_fill_loop(64, 4, true, false, FillTestValue::Const(7));
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
    }

    #[test]
    fn rejects_small_trip_fill() {
        // N < lanes: no full vector iteration.
        let LoopShape { mut func, .. } =
            build_fill_loop(3, 4, false, false, FillTestValue::Const(7));
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
    }

    // ------------------------------------------------------------------
    // Runtime loop-invariant fills (the v2_memfill win) at u8/u16/u32, in the
    // real-isel LeaSib address form.
    // ------------------------------------------------------------------

    /// Assert the emitted vector loop for a runtime-invariant fill of `elem_size`
    /// bytes: one 16-byte packed store/load, `lanes` scratch stores of the
    /// matching width, a `MovRR32` copy of the invariant value, and iv += lanes.
    fn assert_invariant_fill_vectorized(func: &X86ISelFunction, elem_size: u8) {
        let lanes = 16 / elem_size as i64;
        assert_eq!(count_op(func, X86Opcode::MovdquMR), 1, "one packed store");
        assert_eq!(count_op(func, X86Opcode::MovdquRM), 1, "one packed load");
        // The invariant value is copied into the splat register with MovRR32.
        assert!(
            count_op(func, X86Opcode::MovRR32) >= 1,
            "invariant value copied with MovRR32"
        );
        // `lanes` scratch stores of the matching width + the 1 untouched scalar
        // store = lanes + 1 of the element-width store opcode.
        let store_op = store_op_for(elem_size);
        assert_eq!(
            count_op(func, store_op),
            (lanes + 1) as usize,
            "{lanes} scratch stores + 1 scalar store of {store_op:?}"
        );
        // No broadcast pseudo (covered-ops only).
        assert_eq!(count_op(func, X86Opcode::Pshufd), 0);
        // iv is advanced by `lanes` in the vector body (MovRI Imm(lanes)).
        assert!(
            func.blocks.values().flat_map(|b| b.insts.iter()).any(|i| {
                i.opcode == X86Opcode::MovRI
                    && matches!(i.operands.get(1), Some(X86ISelOperand::Imm(k)) if *k == lanes)
            }),
            "vector body steps iv by {lanes}"
        );
    }

    #[test]
    fn vectorizes_u8_runtime_invariant_fill() {
        // The v2_memfill shape: `[u8; N]`, value a loop-invariant runtime reg.
        let LoopShape { mut func, .. } =
            build_fill_loop(256, 1, false, true, FillTestValue::InvariantOutside);
        let slots_before = func.stack_slots.len();
        assert!(X86Vectorize.run_on_function(&mut func), "u8 invariant fill");
        assert_eq!(func.stack_slots.len(), slots_before + 1);
        assert_eq!(func.stack_slots.last().unwrap().size, 16);
        assert_invariant_fill_vectorized(&func, 1); // 16 lanes
    }

    #[test]
    fn vectorizes_u16_runtime_invariant_fill() {
        let LoopShape { mut func, .. } =
            build_fill_loop(128, 2, false, true, FillTestValue::InvariantOutside);
        assert!(
            X86Vectorize.run_on_function(&mut func),
            "u16 invariant fill"
        );
        assert_invariant_fill_vectorized(&func, 2); // 8 lanes
    }

    #[test]
    fn vectorizes_u32_runtime_invariant_fill() {
        let LoopShape { mut func, .. } =
            build_fill_loop(64, 4, false, true, FillTestValue::InvariantOutside);
        assert!(
            X86Vectorize.run_on_function(&mut func),
            "u32 invariant fill"
        );
        assert_invariant_fill_vectorized(&func, 4); // 4 lanes
    }

    #[test]
    fn vectorizes_u8_runtime_invariant_fill_imul_address_form() {
        // Same as above but with the ImulRR+AddRR address form (exercises the
        // `AddRR(SlotBase, ScaledIv)` provenance arm rather than `LeaSib`).
        let LoopShape { mut func, .. } =
            build_fill_loop(256, 1, false, false, FillTestValue::InvariantOutside);
        assert!(
            X86Vectorize.run_on_function(&mut func),
            "u8 invariant fill (imul form)"
        );
        assert_invariant_fill_vectorized(&func, 1);
    }

    // ------------------------------------------------------------------
    // Adversarial: values that are NOT provably loop-invariant must stay scalar.
    // A wrong invariance decision would broadcast a stale value (a miscompile).
    // ------------------------------------------------------------------

    /// The NEW rule, tested directly: invariance is "no def INSIDE the loop",
    /// NOT "exactly one def in the whole function".
    ///
    /// The old rule demanded a single def function-wide plus dominance over the
    /// preheader. That rejects the real shape of every nested loop whose outer
    /// body re-computes the scalar — `v1_saxpy`'s `k` has two defs, both plain
    /// `MovRR32` copies, both outside the inner loop — and it left that loop
    /// scalar at 8.75x of LLVM. Relaxing it is sound because each caller has
    /// already established the loop's only non-body predecessor is its
    /// preheader, and the broadcast is rebuilt on that edge at every entry.
    #[test]
    fn loop_invariant_vreg_allows_many_outside_defs_and_rejects_inside_defs() {
        let LoopShape { mut func, iv } =
            build_fill_loop(64, 4, false, true, FillTestValue::InvariantOutside);
        let entry = func.block_order[0];
        let body: BTreeSet<Block> = func
            .blocks
            .keys()
            .copied()
            .filter(|b| *b != entry && *b != func.block_order[1])
            .collect();

        // The IV is defined inside the loop (the latch increments it), so it is
        // NOT invariant. This is the property a wrong relaxation would break.
        assert!(
            !loop_invariant_vreg(&func, iv, &body),
            "the induction variable is redefined in the loop and must not be invariant"
        );

        // A vreg with NO def at all stays rejected (fail-safe for entry live-ins).
        let undefined = VReg {
            id: 9999,
            class: RegClass::Gpr32,
        };
        assert!(
            !loop_invariant_vreg(&func, undefined, &body),
            "a value with no def must not be treated as invariant"
        );

        // A value defined ONLY outside the loop is invariant — and stays
        // invariant after a SECOND outside def is added, which is the whole
        // point of the relaxation.
        let outside = VReg {
            id: 9998,
            class: RegClass::Gpr32,
        };
        {
            let e = func.blocks.get_mut(&entry).expect("entry");
            let at = e.insts.len() - 1;
            e.insts
                .insert(at, inst(X86Opcode::MovRI, vec![vr(outside), imm(7)]));
        }
        assert!(
            loop_invariant_vreg(&func, outside, &body),
            "a single outside def is invariant"
        );
        {
            let e = func.blocks.get_mut(&entry).expect("entry");
            let at = e.insts.len() - 1;
            e.insts
                .insert(at, inst(X86Opcode::MovRI, vec![vr(outside), imm(9)]));
        }
        assert!(
            loop_invariant_vreg(&func, outside, &body),
            "MULTIPLE defs, all outside the loop, must still be invariant — this is \
             exactly what the old single-def rule rejected"
        );

        // Move one of those defs INSIDE the loop: invariance must be lost.
        let inside_block = *body.iter().next().expect("loop has a body block");
        {
            let blk = func.blocks.get_mut(&inside_block).expect("body block");
            blk.insts
                .insert(0, inst(X86Opcode::MovRI, vec![vr(outside), imm(11)]));
        }
        assert!(
            !loop_invariant_vreg(&func, outside, &body),
            "a def inside the loop must lose invariance"
        );
    }

    #[test]
    fn rejects_value_redefined_inside_loop() {
        // THE critical adversarial case: `v` is recomputed every iteration inside
        // the loop body (single-def, but its def is IN the body and IV-dependent).
        // It is not loop-invariant, so it MUST stay scalar.
        for elem_size in [1u8, 2, 4] {
            let LoopShape { mut func, .. } =
                build_fill_loop(256, elem_size, false, true, FillTestValue::RedefinedInside);
            assert!(
                !X86Vectorize.run_on_function(&mut func),
                "in-body value (elem={elem_size}) must not vectorize"
            );
            assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
            // The scalar store survives untouched.
            assert_eq!(count_op(&func, store_op_for(elem_size)), 1);
        }
    }

    #[test]
    fn rejects_iv_dependent_u8_fill() {
        // `a[i] = i as u8` — the value is the IV itself (per-iteration varying,
        // and multi-def). Must stay scalar.
        let LoopShape { mut func, .. } = build_fill_loop(256, 1, false, true, FillTestValue::Iv);
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
    }

    #[test]
    fn rejects_aliasable_u8_invariant_fill() {
        // A loop-invariant value but an aliasable (non-StackSlot) destination:
        // must stay scalar (aliasing is possible).
        let LoopShape { mut func, .. } =
            build_fill_loop(256, 1, true, true, FillTestValue::InvariantOutside);
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
    }

    // ------------------------------------------------------------------
    // RUNTIME-count invariant-pointer byte fill (the `__trustcg_array_fill_i8`
    // helper-loop shape): `i = 0; while i <s n { *(base + i) = v; i += 1 }`
    // with `n`, `base`, `v` runtime values computed once in the entry block.
    // The positive must vectorize to a guarded MOVDQU loop; every adversarial
    // variant must stay scalar. NOTE the aliasable-base rejection does NOT
    // apply to this slice: with zero loads and a strict store-subset argument,
    // base provenance is irrelevant (see recognize_runtime_byte_fill_loop).
    // ------------------------------------------------------------------
    #[derive(Clone, Copy, PartialEq)]
    enum RtFill {
        /// The exact helper shape (isel bool-materialization header).
        Ok,
        /// Header uses a direct `Jcc L` (no bool materialization).
        OkDirectJcc,
        /// `CmpRR(n, iv)` — reversed compare operand order (`n <s iv`).
        ReversedCmp,
        /// A `!=`-style loop: direct `Jcc NE` on the compare.
        NeLoop,
        /// The store base pointer is defined inside the loop body.
        BaseInLoop,
        /// The stored value is (re)computed inside the loop body.
        ValueInLoop,
        /// A second store in the body.
        SecondStore,
        /// A load in the body.
        LoadInBody,
        /// The store is 4 bytes wide (`MovMR32`), not a byte fill.
        WideStore,
        /// The body has an extra off-chain edge (to a `Ud2` trap).
        OffChainEdge,
        /// `n` has a second def, ALSO OUTSIDE the loop. Still invariant — the
        /// loop cannot observe a change — so this must VECTORIZE. It used to be
        /// rejected only because the old rule demanded a single def
        /// function-wide.
        MultiDefN,
        /// `n` is REDEFINED INSIDE the loop body: genuinely not invariant, and
        /// the trip bound the vector loop computes at entry would be stale.
        /// Must stay scalar.
        RedefinedNInLoop,
    }

    fn build_runtime_byte_fill_loop(variant: RtFill) -> LoopShape {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("rtfill_test".to_string(), sig);
        let mut b = B { next: 0 };

        let base = b.g();
        let n = b.g();
        let src = b.g32();
        let iv = b.g();

        let entry = Block(0);
        let pre = Block(1);
        let header = Block(2);
        let body = Block(3);
        let latch = Block(4);
        let exit = Block(5);
        let trap = Block(6);
        for blk in [entry, pre, header, body, latch, exit, trap] {
            func.ensure_block(blk);
        }

        // Entry: base/n/src computed once (runtime-shaped: OrRR of constants,
        // so `const_of` sees no immediate).
        {
            let c1 = b.g();
            let c2 = b.g();
            let c3 = b.g();
            let c4 = b.g32();
            let c5 = b.g32();
            let e = func.blocks.get_mut(&entry).unwrap();
            e.insts
                .push(inst(X86Opcode::MovRI, vec![vr(c1), imm(0x2000)]));
            e.insts.push(inst(X86Opcode::MovRI, vec![vr(c2), imm(1)]));
            e.insts
                .push(inst(X86Opcode::OrRR, vec![vr(base), vr(c1), vr(c2)]));
            e.insts
                .push(inst(X86Opcode::MovRI, vec![vr(c3), imm(1000)]));
            e.insts
                .push(inst(X86Opcode::OrRR, vec![vr(n), vr(c3), vr(c2)]));
            e.insts
                .push(inst(X86Opcode::MovRI, vec![vr(c4), imm(0xA5)]));
            e.insts.push(inst(X86Opcode::MovRI, vec![vr(c5), imm(0)]));
            e.insts
                .push(inst(X86Opcode::OrRR, vec![vr(src), vr(c4), vr(c5)]));
            if variant == RtFill::MultiDefN {
                e.insts.push(inst(X86Opcode::MovRI, vec![vr(n), imm(64)]));
            }
            e.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(pre)]));
            e.successors = vec![pre];
        }
        // Preheader: iv = 0.
        {
            let zero = b.g();
            let p = func.blocks.get_mut(&pre).unwrap();
            p.insts.push(inst(X86Opcode::MovRI, vec![vr(zero), imm(0)]));
            p.insts.push(inst(X86Opcode::MovRR, vec![vr(iv), vr(zero)]));
            p.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            p.successors = vec![header];
        }
        // Header: `iv <s n ? body : exit` — the isel bool-materialization chain
        // (Ok) or a direct Jcc (OkDirectJcc / NeLoop), or reversed operands.
        {
            let bv = b.g32();
            let bw = b.g();
            let h = func.blocks.get_mut(&header).unwrap();
            let (ca, cb) = if variant == RtFill::ReversedCmp {
                (n, iv)
            } else {
                (iv, n)
            };
            h.insts.push(inst(X86Opcode::CmpRR, vec![vr(ca), vr(cb)]));
            match variant {
                RtFill::OkDirectJcc | RtFill::ReversedCmp => {
                    h.insts.push(inst(
                        X86Opcode::Jcc,
                        vec![
                            X86ISelOperand::CondCode(X86CondCode::L),
                            X86ISelOperand::Block(body),
                        ],
                    ));
                }
                RtFill::NeLoop => {
                    h.insts.push(inst(
                        X86Opcode::Jcc,
                        vec![
                            X86ISelOperand::CondCode(X86CondCode::NE),
                            X86ISelOperand::Block(body),
                        ],
                    ));
                }
                _ => {
                    h.insts.push(inst(
                        X86Opcode::Setcc,
                        vec![vr(bv), X86ISelOperand::CondCode(X86CondCode::L)],
                    ));
                    h.insts.push(inst(X86Opcode::Movzx, vec![vr(bv), vr(bv)]));
                    h.insts.push(inst(X86Opcode::Movzx, vec![vr(bw), vr(bv)]));
                    h.insts
                        .push(inst(X86Opcode::AndRI, vec![vr(bw), vr(bw), imm(1)]));
                    h.insts.push(inst(X86Opcode::CmpRI, vec![vr(bw), imm(0)]));
                    h.insts.push(inst(
                        X86Opcode::Jcc,
                        vec![
                            X86ISelOperand::CondCode(X86CondCode::NE),
                            X86ISelOperand::Block(body),
                        ],
                    ));
                }
            }
            h.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(exit)]));
            h.successors = vec![body, exit];
        }
        // Body: iv8 = iv (the isel body-entry copy).
        let iv8 = b.g();
        {
            let blk = func.blocks.get_mut(&body).unwrap();
            if variant == RtFill::RedefinedNInLoop {
                // A def of the trip count INSIDE the loop — the hazard the
                // invariance check exists to catch.
                blk.insts.push(inst(X86Opcode::MovRI, vec![vr(n), imm(32)]));
            }
            blk.insts
                .push(inst(X86Opcode::MovRR, vec![vr(iv8), vr(iv)]));
            if variant == RtFill::OffChainEdge {
                blk.insts
                    .push(inst(X86Opcode::CmpRI, vec![vr(iv8), imm(1 << 20)]));
                blk.insts.push(inst(
                    X86Opcode::Jcc,
                    vec![
                        X86ISelOperand::CondCode(X86CondCode::AE),
                        X86ISelOperand::Block(trap),
                    ],
                ));
                blk.insts
                    .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(latch)]));
                blk.successors = vec![latch, trap];
            } else {
                blk.insts
                    .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(latch)]));
                blk.successors = vec![latch];
            }
        }
        // Latch: `*(base + iv8*1) = src; iv = iv8 + 1` (the exact helper form).
        {
            let one = b.g();
            let mul = b.g();
            let bc = b.g();
            let sum = b.g();
            let addr = b.g();
            let one2 = b.g();
            let niv = b.g();
            let blk = func.blocks.get_mut(&latch).unwrap();
            let store_base = if variant == RtFill::BaseInLoop {
                let p = b.g();
                blk.insts
                    .push(inst(X86Opcode::MovRI, vec![vr(p), imm(0x3000)]));
                p
            } else {
                base
            };
            let store_src = if variant == RtFill::ValueInLoop {
                // Recomputed in-body (even though value-equal, the def is inside
                // the loop — invariance must fail closed).
                let s = b.g32();
                blk.insts
                    .push(inst(X86Opcode::OrRR, vec![vr(s), vr(src), vr(src)]));
                s
            } else {
                src
            };
            if variant == RtFill::LoadInBody {
                let l = b.g32();
                blk.insts
                    .push(inst(X86Opcode::MovRM8, vec![vr(l), memaddr(base)]));
            }
            blk.insts
                .push(inst(X86Opcode::MovRI, vec![vr(one), imm(1)]));
            blk.insts
                .push(inst(X86Opcode::ImulRR, vec![vr(mul), vr(iv8), vr(one)]));
            blk.insts
                .push(inst(X86Opcode::MovRR, vec![vr(bc), vr(store_base)]));
            blk.insts
                .push(inst(X86Opcode::AddRR, vec![vr(sum), vr(bc), vr(mul)]));
            blk.insts
                .push(inst(X86Opcode::MovRR, vec![vr(addr), vr(sum)]));
            let store_op = if variant == RtFill::WideStore {
                X86Opcode::MovMR32
            } else {
                X86Opcode::MovMR8
            };
            blk.insts
                .push(inst(store_op, vec![memaddr(addr), vr(store_src)]));
            if variant == RtFill::SecondStore {
                blk.insts
                    .push(inst(X86Opcode::MovMR8, vec![memaddr(base), vr(src)]));
            }
            blk.insts
                .push(inst(X86Opcode::MovRI, vec![vr(one2), imm(1)]));
            blk.insts
                .push(inst(X86Opcode::AddRR, vec![vr(niv), vr(iv8), vr(one2)]));
            blk.insts
                .push(inst(X86Opcode::MovRR, vec![vr(iv), vr(niv)]));
            blk.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            blk.successors = vec![header];
        }
        // exit: Ret; trap: Ud2.
        func.blocks
            .get_mut(&exit)
            .unwrap()
            .insts
            .push(inst(X86Opcode::Ret, vec![]));
        func.blocks
            .get_mut(&trap)
            .unwrap()
            .insts
            .push(inst(X86Opcode::Ud2, vec![]));

        func.next_vreg = b.next;
        LoopShape { func, iv }
    }

    fn assert_runtime_fill_vectorized(mut func: X86ISelFunction, iv: VReg) {
        let blocks_before = func.block_order.len();
        let slots_before = func.stack_slots.len();
        assert!(
            X86Vectorize.run_on_function(&mut func),
            "should vectorize the runtime byte fill"
        );
        // Four new blocks (guard + vector preheader + header + body).
        assert_eq!(func.block_order.len(), blocks_before + 4);
        // One fresh 16-byte scratch slot for the packed broadcast.
        assert_eq!(func.stack_slots.len(), slots_before + 1);
        assert_eq!(func.stack_slots.last().unwrap().size, 16);
        // One packed store, one packed scratch load, no PSHUFD.
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 1);
        assert_eq!(count_op(&func, X86Opcode::MovdquRM), 1);
        assert_eq!(count_op(&func, X86Opcode::Pshufd), 0);
        // The broadcast is 16 covered byte stores; the scalar store survives
        // (16 + 1 = 17 total MovMR8).
        assert_eq!(count_op(&func, X86Opcode::MovMR8), 17);
        // The shared counter is advanced by the vector body (an AddRR reading iv).
        assert!(func.blocks.values().flat_map(|b| b.insts.iter()).any(|i| {
            i.opcode == X86Opcode::AddRR
                && i.operands.len() == 3
                && matches!(i.operands.get(1), Some(X86ISelOperand::VReg(s)) if *s == iv)
        }));
        // The preheader (Block 1) was redirected off the scalar header (Block 2).
        let pre = func.blocks.get(&Block(1)).unwrap();
        let jmp_target = pre
            .insts
            .iter()
            .rev()
            .find(|i| i.opcode == X86Opcode::Jmp)
            .and_then(|i| match i.operands.first() {
                Some(X86ISelOperand::Block(t)) => Some(*t),
                _ => None,
            })
            .unwrap();
        assert_ne!(
            jmp_target,
            Block(2),
            "preheader must be redirected off header"
        );
        // The guard block compares n against the lane count and fail-safes to
        // the scalar header.
        let guard = func.blocks.get(&jmp_target).unwrap();
        assert!(guard.insts.iter().any(|i| i.opcode == X86Opcode::CmpRI
            && matches!(i.operands.get(1), Some(X86ISelOperand::Imm(16)))));
        assert!(guard.successors.contains(&Block(2)));
    }

    #[test]
    fn vectorizes_runtime_byte_fill_helper_shape() {
        let LoopShape { func, iv } = build_runtime_byte_fill_loop(RtFill::Ok);
        assert_runtime_fill_vectorized(func, iv);
    }

    #[test]
    fn vectorizes_runtime_byte_fill_direct_jcc() {
        let LoopShape { func, iv } = build_runtime_byte_fill_loop(RtFill::OkDirectJcc);
        assert_runtime_fill_vectorized(func, iv);
    }

    #[test]
    fn rejects_runtime_fill_reversed_compare() {
        // `n <s iv` is NOT the fill trip semantics; must stay scalar.
        let LoopShape { mut func, .. } = build_runtime_byte_fill_loop(RtFill::ReversedCmp);
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
    }

    #[test]
    fn rejects_runtime_fill_ne_loop() {
        // A `!=`-terminated loop (divergent for `n < iv0`): must stay scalar.
        let LoopShape { mut func, .. } = build_runtime_byte_fill_loop(RtFill::NeLoop);
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
    }

    #[test]
    fn rejects_runtime_fill_base_defined_inside() {
        let LoopShape { mut func, .. } = build_runtime_byte_fill_loop(RtFill::BaseInLoop);
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
    }

    #[test]
    fn rejects_runtime_fill_value_defined_inside() {
        let LoopShape { mut func, .. } = build_runtime_byte_fill_loop(RtFill::ValueInLoop);
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
    }

    #[test]
    fn rejects_runtime_fill_second_store() {
        let LoopShape { mut func, .. } = build_runtime_byte_fill_loop(RtFill::SecondStore);
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
    }

    #[test]
    fn rejects_runtime_fill_load_in_body() {
        // A load makes it not a pure fill (and could observe the reordered
        // packed stores): must stay scalar.
        let LoopShape { mut func, .. } = build_runtime_byte_fill_loop(RtFill::LoadInBody);
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
    }

    #[test]
    fn rejects_runtime_fill_wide_store() {
        // Only the byte-fill slice is implemented; a 4-byte store with a
        // RUNTIME trip count must stay scalar.
        let LoopShape { mut func, .. } = build_runtime_byte_fill_loop(RtFill::WideStore);
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
    }

    #[test]
    fn rejects_runtime_fill_offchain_edge() {
        // Any off-chain edge (even a pure trap) is outside this slice's strict
        // shape: must stay scalar.
        let LoopShape { mut func, .. } = build_runtime_byte_fill_loop(RtFill::OffChainEdge);
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
    }

    /// RE-SCOPED (was `rejects_runtime_fill_multidef_n`).
    ///
    /// The old assertion encoded the old RULE, not a safety property: `n`'s
    /// second def is in the ENTRY block, outside the loop, so `n` cannot change
    /// while the loop runs and the value the vector preheader reads is exactly
    /// the value every scalar iteration sees. Rejecting it was pure lost
    /// coverage — the same over-conservatism that kept `v1_saxpy` scalar at
    /// 8.75x of LLVM. The property that actually matters is guarded by
    /// `rejects_runtime_fill_n_redefined_inside_loop` below.
    #[test]
    fn vectorizes_runtime_fill_multidef_n_all_defs_outside_loop() {
        let LoopShape { mut func, .. } = build_runtime_byte_fill_loop(RtFill::MultiDefN);
        assert!(
            X86Vectorize.run_on_function(&mut func),
            "multiple defs of `n`, ALL outside the loop, are still invariant"
        );
        assert!(count_op(&func, X86Opcode::MovdquMR) > 0);
    }

    /// THE property: a trip count redefined INSIDE the loop is not invariant,
    /// and the bound the vector loop computes at entry would be stale. Must stay
    /// scalar. This is what a wrong relaxation would break.
    #[test]
    fn rejects_runtime_fill_n_redefined_inside_loop() {
        let LoopShape { mut func, .. } = build_runtime_byte_fill_loop(RtFill::RedefinedNInLoop);
        assert!(
            !X86Vectorize.run_on_function(&mut func),
            "a trip count redefined inside the loop must not vectorize"
        );
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
    }

    // ------------------------------------------------------------------
    // Saxpy / element-wise FMA shape (`dest[i] = (k*x[i]) (+|-) y[i]`) over local
    // i32 arrays. `dest` may equal a source slot (same-index only). The positive
    // must vectorize to MOVDQU loads + PMULLD + PADDD/PSUBD + MOVDQU store; the
    // adversarials (non-invariant / IV-dependent k) must stay scalar.
    // ------------------------------------------------------------------
    #[derive(Clone, Copy)]
    enum SaxpyDest {
        /// dest is the multiplied source slot (`a[i] = a[i]*k + b[i]`).
        SameAsX,
        /// dest is the added source slot (`y[i] = x[i]*k + y[i]`).
        SameAsY,
        /// dest is a third distinct slot (`c[i] = x[i]*k + y[i]`).
        Distinct,
    }
    #[derive(Clone, Copy)]
    enum SaxpyK {
        /// k is a compile-time constant (materialized in the entry block).
        Const(i64),
        /// k is a runtime value computed ONCE in the entry block (single-def,
        /// dominates the preheader): provably loop-invariant — vectorizable.
        InvariantOutside,
        /// k is recomputed INSIDE the loop body each iteration (IV-dependent):
        /// NOT invariant — must stay scalar. THE critical adversarial.
        RedefinedInside,
        /// k IS the IV (multi-def, per-iteration varying) — must stay scalar.
        Iv,
    }

    /// Build `dest[i] = (k * x[i]) OP y[i]` (mul first) over three [i32;n] slots:
    /// slot0 = x, slot1 = y, slot2 = distinct c. `op` is AddRR/SubRR.
    fn build_saxpy_loop(n: i64, op: X86Opcode, dest: SaxpyDest, kind: SaxpyK) -> LoopShape {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("saxpy_test".to_string(), sig);
        func.stack_slots = vec![
            StackSlotInfo::new((n * 4) as u32, 4),
            StackSlotInfo::new((n * 4) as u32, 4),
            StackSlotInfo::new((n * 4) as u32, 4),
        ];
        let mut b = B { next: 0 };

        let bases = [b.g(), b.g(), b.g()];
        let iv = b.g();
        let kinv = b.g32(); // runtime-invariant k (entry-computed)
        let kone = b.g32(); // constant 1 (entry), used to build in-body/invariant k

        let entry = Block(0);
        let pre = Block(1);
        let header = Block(2);
        let b3 = Block(3);
        let b4 = Block(4);
        let b5 = Block(5);
        let latch = Block(6);
        let trap = Block(7);
        let exit = Block(8);
        for blk in [entry, pre, header, b3, b4, b5, latch, trap, exit] {
            func.ensure_block(blk);
        }

        let slot_of_dest = match dest {
            SaxpyDest::SameAsX => 0usize,
            SaxpyDest::SameAsY => 1,
            SaxpyDest::Distinct => 2,
        };

        // Entry: three Lea r,[StackSlot(k)] + set up invariant k (runtime OR-of-two).
        {
            let e = func.blocks.get_mut(&entry).unwrap();
            for (k, base) in bases.iter().enumerate() {
                e.insts.push(inst(
                    X86Opcode::Lea,
                    vec![
                        vr(*base),
                        X86ISelOperand::MemAddr {
                            base: Box::new(X86ISelOperand::StackSlot(k as u32)),
                            disp: 0,
                        },
                    ],
                ));
            }
            e.insts.push(inst(X86Opcode::MovRI, vec![vr(kone), imm(1)]));
            // kinv = 2 | 1  — a runtime value computed ONCE, outside the loop (its
            // def is an OrRR so it is not a compile-time constant through canon).
            let k2 = b.g32();
            e.insts.push(inst(X86Opcode::MovRI, vec![vr(k2), imm(2)]));
            e.insts
                .push(inst(X86Opcode::OrRR, vec![vr(kinv), vr(k2), vr(kone)]));
            e.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(pre)]));
            e.successors = vec![pre];
        }
        // Preheader: iv = 0.
        {
            let zero = b.g();
            let p = func.blocks.get_mut(&pre).unwrap();
            p.insts.push(inst(X86Opcode::MovRI, vec![vr(zero), imm(0)]));
            p.insts.push(inst(X86Opcode::MovRR, vec![vr(iv), vr(zero)]));
            p.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            p.successors = vec![header];
        }
        // Header: iv <u N ? b3 : exit.
        {
            let t = b.g();
            let nn = b.g();
            let h = func.blocks.get_mut(&header).unwrap();
            h.insts.push(inst(X86Opcode::MovRR, vec![vr(t), vr(iv)]));
            h.insts.push(inst(X86Opcode::MovRI, vec![vr(nn), imm(n)]));
            h.insts.push(inst(X86Opcode::CmpRR, vec![vr(t), vr(nn)]));
            h.insts.push(inst(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(b3),
                ],
            ));
            h.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(exit)]));
            h.successors = vec![b3, exit];
        }
        // b3: bounds-check for the x access. For RedefinedInside, ALSO recompute k
        // here (in-body, IV-dependent).
        let kmod = b.g32();
        {
            let mut checks = bounds_check(&mut b, iv, n, b4, trap);
            if let SaxpyK::RedefinedInside = kind {
                checks.insert(0, inst(X86Opcode::OrRR, vec![vr(kmod), vr(iv), vr(kone)]));
            }
            let blk = func.blocks.get_mut(&b3).unwrap();
            blk.insts.extend(checks);
            blk.successors = vec![b4, trap];
        }
        // The scalar factor register actually fed to the multiply.
        let k_reg = match kind {
            SaxpyK::Const(c) => {
                // Materialize the constant in b4 below; placeholder here.
                let _ = c;
                b.g32()
            }
            SaxpyK::InvariantOutside => kinv,
            SaxpyK::RedefinedInside => kmod,
            SaxpyK::Iv => iv,
        };
        // b4: load x[iv]; mul = x*k; bounds-check for the y access.
        let mul;
        {
            let (addr, mut stream) = addr_of(&mut b, bases[0], iv);
            let lx = b.g32();
            stream.push(inst(X86Opcode::MovRM32, vec![vr(lx), memaddr(addr)]));
            // For the Const kind, materialize k in-body as a MovRI immediate.
            let kv = if let SaxpyK::Const(c) = kind {
                stream.push(inst(X86Opcode::MovRI, vec![vr(k_reg), imm(c)]));
                k_reg
            } else {
                k_reg
            };
            mul = b.g32();
            stream.push(inst(X86Opcode::ImulRR, vec![vr(mul), vr(lx), vr(kv)]));
            stream.extend(bounds_check(&mut b, iv, n, b5, trap));
            let blk = func.blocks.get_mut(&b4).unwrap();
            blk.insts.extend(stream);
            blk.successors = vec![b5, trap];
        }
        // b5: load y[iv]; sum = mul OP y; bounds-check for the store.
        let sum;
        {
            let (addr, mut stream) = addr_of(&mut b, bases[1], iv);
            let ly = b.g32();
            stream.push(inst(X86Opcode::MovRM32, vec![vr(ly), memaddr(addr)]));
            sum = b.g32();
            stream.push(inst(op, vec![vr(sum), vr(mul), vr(ly)]));
            stream.extend(bounds_check(&mut b, iv, n, latch, trap));
            let blk = func.blocks.get_mut(&b5).unwrap();
            blk.insts.extend(stream);
            blk.successors = vec![latch, trap];
        }
        // latch: store dest[iv] = sum; iv += 1; back-edge.
        {
            let (addr, mut stream) = addr_of(&mut b, bases[slot_of_dest], iv);
            let sm = b.g32();
            stream.push(inst(X86Opcode::MovRR32, vec![vr(sm), vr(sum)]));
            stream.push(inst(X86Opcode::MovMR32, vec![memaddr(addr), vr(sm)]));
            let one = b.g();
            let niv = b.g();
            stream.push(inst(X86Opcode::MovRI, vec![vr(one), imm(1)]));
            stream.push(inst(X86Opcode::AddRR, vec![vr(niv), vr(iv), vr(one)]));
            stream.push(inst(X86Opcode::MovRR, vec![vr(iv), vr(niv)]));
            stream.push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            let blk = func.blocks.get_mut(&latch).unwrap();
            blk.insts.extend(stream);
            blk.successors = vec![header];
        }
        // trap: single Ud2.
        {
            func.blocks
                .get_mut(&trap)
                .unwrap()
                .insts
                .push(inst(X86Opcode::Ud2, vec![]));
        }
        // exit: Ret.
        {
            func.blocks
                .get_mut(&exit)
                .unwrap()
                .insts
                .push(inst(X86Opcode::Ret, vec![]));
        }

        func.next_vreg = b.next;
        LoopShape { func, iv }
    }

    /// Assert a saxpy loop vectorized to the packed FMA sequence.
    ///
    /// Counts cover BOTH vector tiers: the 4x-unrolled body (`VBU`) and the
    /// single-chunk drain (`VB`). `UNROLL = 4`, so each packed op appears
    /// `1 + 4` times and the loads `1 (kvec) + 2 (VB) + 2*4 (VBU)`.
    fn assert_saxpy_vectorized(func: &X86ISelFunction, packed_add: X86Opcode) {
        assert_eq!(
            count_op(func, X86Opcode::Pmulld),
            1 + 4,
            "packed multiply: 1 drain + 4 unrolled"
        );
        assert_eq!(
            count_op(func, packed_add),
            1 + 4,
            "packed add/sub: 1 drain + 4 unrolled"
        );
        assert_eq!(
            count_op(func, X86Opcode::MovdquRM),
            1 + 2 + 2 * 4,
            "[k;4] load + drain x/y + 4 unrolled x/y pairs"
        );
        assert_eq!(
            count_op(func, X86Opcode::MovdquMR),
            1 + 4,
            "packed store: 1 drain + 4 unrolled"
        );
        // THE POINT of the unrolled tier: ONE address triple serves all four
        // chunks, which are reached by constant displacement. Three LeaSib per
        // tier, not three per chunk — and at least one access at a non-zero
        // displacement proves the amortization actually happened.
        assert_eq!(
            count_op(func, X86Opcode::LeaSib),
            3 + 3,
            "one address triple per tier, NOT per chunk"
        );
        let displaced = func
            .blocks
            .values()
            .flat_map(|b| b.insts.iter())
            .filter(|i| {
                matches!(i.opcode, X86Opcode::MovdquRM | X86Opcode::MovdquMR)
                    && i.operands
                        .iter()
                        .any(|o| matches!(o, X86ISelOperand::MemAddr { disp, .. } if *disp != 0))
            })
            .count();
        assert_eq!(
            displaced,
            3 * (4 - 1),
            "chunks 1..3 of each unrolled triple reach data by displacement"
        );
        // No broadcast pseudo (covered-ops only).
        assert_eq!(count_op(func, X86Opcode::Pshufd), 0);
        // The original scalar loop survives untouched (2 scalar loads, 1 store).
        assert_eq!(count_op(func, X86Opcode::MovRM32), 2);
        assert_eq!(
            count_op(func, X86Opcode::MovMR32),
            1 + 4,
            "1 scalar + 4 scratch stores"
        );
    }

    #[test]
    fn vectorizes_saxpy_dest_equals_mul_source() {
        // The benchmark shape: a[i] = a[i]*k + b[i]  (dest == the mul source).
        let LoopShape { mut func, iv } = build_saxpy_loop(
            66,
            X86Opcode::AddRR,
            SaxpyDest::SameAsX,
            SaxpyK::InvariantOutside,
        );
        let blocks_before = func.block_order.len();
        let slots_before = func.stack_slots.len();
        assert!(X86Vectorize.run_on_function(&mut func), "should vectorize");
        assert_eq!(
            func.block_order.len(),
            blocks_before + 5,
            "VP + VHU + VBU + VH + VB"
        );
        assert_eq!(
            func.stack_slots.len(),
            slots_before + 1,
            "one [k;4] scratch slot"
        );
        assert_eq!(func.stack_slots.last().unwrap().size, 16);
        assert_saxpy_vectorized(&func, X86Opcode::Paddd);
        // Shared counter is reused; vector body steps it by 4.
        assert!(func.blocks.values().flat_map(|b| b.insts.iter()).any(|i| {
            i.opcode == X86Opcode::AddRR
                && matches!(i.operands.get(1), Some(X86ISelOperand::VReg(d)) if *d == iv)
                && i.operands.len() == 3
        }));
    }

    #[test]
    fn vectorizes_saxpy_dest_equals_add_source() {
        // The task's stated shape: y[i] = x[i]*k + y[i]  (dest == the add source).
        let LoopShape { mut func, .. } = build_saxpy_loop(
            80,
            X86Opcode::AddRR,
            SaxpyDest::SameAsY,
            SaxpyK::InvariantOutside,
        );
        assert!(X86Vectorize.run_on_function(&mut func), "should vectorize");
        assert_saxpy_vectorized(&func, X86Opcode::Paddd);
    }

    #[test]
    fn vectorizes_saxpy_distinct_dest() {
        // c[i] = x[i]*k + y[i]  (three distinct arrays; pure saxpy).
        let LoopShape { mut func, .. } = build_saxpy_loop(
            64,
            X86Opcode::AddRR,
            SaxpyDest::Distinct,
            SaxpyK::InvariantOutside,
        );
        assert!(X86Vectorize.run_on_function(&mut func), "should vectorize");
        assert_saxpy_vectorized(&func, X86Opcode::Paddd);
    }

    #[test]
    fn vectorizes_saxpy_sub_and_const_k() {
        // dest = (k*x) - y with a compile-time constant k -> PMULLD + PSUBD.
        let LoopShape { mut func, .. } =
            build_saxpy_loop(64, X86Opcode::SubRR, SaxpyDest::SameAsX, SaxpyK::Const(5));
        assert!(X86Vectorize.run_on_function(&mut func), "should vectorize");
        assert_saxpy_vectorized(&func, X86Opcode::Psubd);
    }

    #[test]
    fn rejects_saxpy_k_redefined_inside_loop() {
        // THE critical adversarial: k is recomputed every iteration inside the
        // loop body (IV-dependent) -> not loop-invariant -> MUST stay scalar.
        let LoopShape { mut func, .. } = build_saxpy_loop(
            64,
            X86Opcode::AddRR,
            SaxpyDest::SameAsX,
            SaxpyK::RedefinedInside,
        );
        assert!(
            !X86Vectorize.run_on_function(&mut func),
            "in-body k must not vectorize"
        );
        assert_eq!(count_op(&func, X86Opcode::Pmulld), 0);
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
    }

    #[test]
    fn rejects_saxpy_iv_dependent_k() {
        // k IS the IV (per-iteration varying, multi-def) -> must stay scalar.
        let LoopShape { mut func, .. } =
            build_saxpy_loop(64, X86Opcode::AddRR, SaxpyDest::SameAsX, SaxpyK::Iv);
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::Pmulld), 0);
    }

    #[test]
    fn rejects_saxpy_small_trip_count() {
        // N < lanes: no full vector iteration.
        let LoopShape { mut func, .. } = build_saxpy_loop(
            3,
            X86Opcode::AddRR,
            SaxpyDest::SameAsX,
            SaxpyK::InvariantOutside,
        );
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::Pmulld), 0);
    }

    // ------------------------------------------------------------------
    // Integer sum-reduction (`for k { acc += a[k] }` / `acc += a[k]*b[k] }`)
    // over local i32 arrays with a loop-carried Gpr32 register accumulator.
    // The positives must vectorize to a PADDD-accumulate loop + a covered
    // horizontal reduce (MOVDQU spill + scalar loads/adds, no PHADDD/PSHUFD).
    // The adversarials (float sum, non-add reduce, acc escaping to another
    // computation / to memory) MUST stay scalar+correct.
    // ------------------------------------------------------------------
    #[derive(Clone, Copy)]
    enum RedKind {
        /// `acc += a[k]` — vectorizable integer sum.
        Sum,
        /// `acc += a[k]*b[k]` — vectorizable integer dot-product.
        Dot,
        /// `acc -= a[k]` — a SubRR reduction (non-commutative): MUST stay scalar.
        SubReduce,
        /// `acc += fa[k]` over f32 (Fpr128 acc, MOVSS loads, ADDSS): non-
        /// associative — MUST stay scalar. THE critical adversarial.
        FloatSum,
        /// `acc += a[k]` but `acc` is ALSO read into a second value in-loop
        /// (escapes the reduction): MUST stay scalar.
        AccEscapes,
        /// `acc += a[k]` but `acc` is ALSO stored to memory mid-loop: MUST stay
        /// scalar (a reduction writes no memory in-loop).
        AccStored,
    }

    /// Build an integer (or, for FloatSum, float) reduction loop over two [i32;n]
    /// (or [f32;n]) slots. slot0 = a, slot1 = b (Dot only), slot2 = a spill
    /// target (AccStored only).
    fn build_reduction_loop(n: i64, kind: RedKind) -> LoopShape {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("reduce_test".to_string(), sig);
        func.stack_slots = vec![
            StackSlotInfo::new((n * 4) as u32, 4),
            StackSlotInfo::new((n * 4) as u32, 4),
            StackSlotInfo::new((n * 4) as u32, 4),
        ];
        let mut b = B { next: 0 };

        let is_float = matches!(kind, RedKind::FloatSum);
        let bases = [b.g(), b.g(), b.g()];
        let iv = b.g();
        // The loop-carried accumulator: Gpr32 (integer) or Fpr128 (float).
        let acc = if is_float {
            let v = VReg::new(b.next, RegClass::Fpr128);
            b.next += 1;
            v
        } else {
            b.g32()
        };

        let entry = Block(0);
        let pre = Block(1);
        let header = Block(2);
        let b3 = Block(3);
        let latch = Block(4);
        let trap = Block(5);
        let exit = Block(6);
        for blk in [entry, pre, header, b3, latch, trap, exit] {
            func.ensure_block(blk);
        }

        // Entry: base Leas.
        {
            let e = func.blocks.get_mut(&entry).unwrap();
            for (k, base) in bases.iter().enumerate() {
                e.insts.push(inst(
                    X86Opcode::Lea,
                    vec![
                        vr(*base),
                        X86ISelOperand::MemAddr {
                            base: Box::new(X86ISelOperand::StackSlot(k as u32)),
                            disp: 0,
                        },
                    ],
                ));
            }
            e.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(pre)]));
            e.successors = vec![pre];
        }
        // Preheader: iv = 0; acc = 0 (an outside-body init of the accumulator).
        {
            let zero = b.g();
            let p = func.blocks.get_mut(&pre).unwrap();
            p.insts.push(inst(X86Opcode::MovRI, vec![vr(zero), imm(0)]));
            p.insts.push(inst(X86Opcode::MovRR, vec![vr(iv), vr(zero)]));
            // acc init (outside the loop body): a Gpr32 0 (integer) / an XMM 0
            // (float). Its value is irrelevant to correctness (the transform folds
            // whatever `acc` holds at loop entry), but it must exist.
            if is_float {
                let fz = {
                    let v = VReg::new(b.next, RegClass::Fpr128);
                    b.next += 1;
                    v
                };
                p.insts
                    .push(inst(X86Opcode::Pxor, vec![vr(fz), vr(fz), vr(fz)]));
                p.insts
                    .push(inst(X86Opcode::MovssRR, vec![vr(acc), vr(fz)]));
            } else {
                p.insts.push(inst(X86Opcode::MovRI, vec![vr(acc), imm(0)]));
            }
            p.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            p.successors = vec![header];
        }
        // Header: iv <u N ? b3 : exit.
        {
            let t = b.g();
            let nn = b.g();
            let h = func.blocks.get_mut(&header).unwrap();
            h.insts.push(inst(X86Opcode::MovRR, vec![vr(t), vr(iv)]));
            h.insts.push(inst(X86Opcode::MovRI, vec![vr(nn), imm(n)]));
            h.insts.push(inst(X86Opcode::CmpRR, vec![vr(t), vr(nn)]));
            h.insts.push(inst(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(b3),
                ],
            ));
            h.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(exit)]));
            h.successors = vec![b3, exit];
        }
        // b3: bounds-check for the a access (iv <u N ? latch : trap).
        {
            let checks = bounds_check(&mut b, iv, n, latch, trap);
            let blk = func.blocks.get_mut(&b3).unwrap();
            blk.insts.extend(checks);
            blk.successors = vec![latch, trap];
        }
        // latch: load(s) + reduction + iv += 1 + back-edge.
        {
            let load_op = if is_float {
                X86Opcode::MovssRM
            } else {
                X86Opcode::MovRM32
            };
            let add_op = match kind {
                RedKind::SubReduce => X86Opcode::SubRR,
                RedKind::FloatSum => X86Opcode::Addss,
                _ => X86Opcode::AddRR,
            };
            let g_val = |b: &mut B| -> VReg {
                if is_float {
                    let v = VReg::new(b.next, RegClass::Fpr128);
                    b.next += 1;
                    v
                } else {
                    b.g32()
                }
            };

            let (addr_a, mut stream) = addr_of(&mut b, bases[0], iv);
            let la = g_val(&mut b);
            stream.push(inst(load_op, vec![vr(la), memaddr(addr_a)]));

            // The summed term.
            let term = match kind {
                RedKind::Dot => {
                    let (addr_b, sb) = addr_of(&mut b, bases[1], iv);
                    stream.extend(sb);
                    let lb = g_val(&mut b);
                    stream.push(inst(load_op, vec![vr(lb), memaddr(addr_b)]));
                    let m = g_val(&mut b);
                    stream.push(inst(X86Opcode::ImulRR, vec![vr(m), vr(la), vr(lb)]));
                    m
                }
                _ => la,
            };

            // acc_new = acc (+|-) term ; then a copy ; then the writeback — the
            // real isel emits the add's result through a MovRR32 copy before the
            // back-edge writeback, so this exercises the canon-through-copy path.
            let acc_new = g_val(&mut b);
            stream.push(inst(add_op, vec![vr(acc_new), vr(acc), vr(term)]));
            if is_float {
                stream.push(inst(X86Opcode::MovssRR, vec![vr(acc), vr(acc_new)]));
            } else {
                let tmp = b.g32();
                stream.push(inst(X86Opcode::MovRR32, vec![vr(tmp), vr(acc_new)]));
                stream.push(inst(X86Opcode::MovRR32, vec![vr(acc), vr(tmp)]));
            }

            // Adversarial escapes: a SECOND read of `acc` into another value.
            if let RedKind::AccEscapes = kind {
                let esc = b.g32();
                stream.push(inst(X86Opcode::MovRR, vec![vr(esc), vr(acc)]));
            }
            // Adversarial: store `acc` to memory (slot 2) mid-loop.
            if let RedKind::AccStored = kind {
                let (addr_c, sc) = addr_of(&mut b, bases[2], iv);
                stream.extend(sc);
                stream.push(inst(X86Opcode::MovMR32, vec![memaddr(addr_c), vr(acc)]));
            }

            let one = b.g();
            let niv = b.g();
            stream.push(inst(X86Opcode::MovRI, vec![vr(one), imm(1)]));
            stream.push(inst(X86Opcode::AddRR, vec![vr(niv), vr(iv), vr(one)]));
            stream.push(inst(X86Opcode::MovRR, vec![vr(iv), vr(niv)]));
            stream.push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            let blk = func.blocks.get_mut(&latch).unwrap();
            blk.insts.extend(stream);
            blk.successors = vec![header];
        }
        // trap: single Ud2.
        {
            func.blocks
                .get_mut(&trap)
                .unwrap()
                .insts
                .push(inst(X86Opcode::Ud2, vec![]));
        }
        // exit: Ret.
        {
            func.blocks
                .get_mut(&exit)
                .unwrap()
                .insts
                .push(inst(X86Opcode::Ret, vec![]));
        }

        func.next_vreg = b.next;
        LoopShape { func, iv }
    }

    /// Build a widening byte sum-reduction `for k in 0..n { acc += a[k] as u64 }`
    /// over a `[u8; n]` slot: the body is `MovRM8 dst32, [AddRR(base, iv)]` (a
    /// stride-1 byte load) → `Movzx wide64, dst32` → `AddRR acc, acc, wide64`,
    /// with a Gpr64 accumulator. Mirrors [`build_reduction_loop`]'s CFG.
    fn build_byte_sum_loop(n: i64) -> LoopShape {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("byte_sum_test".to_string(), sig);
        func.stack_slots = vec![StackSlotInfo::new(n as u32, 1)];
        let mut b = B { next: 0 };
        let base = b.g();
        let iv = b.g();
        let acc = b.g(); // Gpr64 accumulator

        let entry = Block(0);
        let pre = Block(1);
        let header = Block(2);
        let b3 = Block(3);
        let latch = Block(4);
        let trap = Block(5);
        let exit = Block(6);
        for blk in [entry, pre, header, b3, latch, trap, exit] {
            func.ensure_block(blk);
        }
        {
            let e = func.blocks.get_mut(&entry).unwrap();
            e.insts.push(inst(
                X86Opcode::Lea,
                vec![
                    vr(base),
                    X86ISelOperand::MemAddr {
                        base: Box::new(X86ISelOperand::StackSlot(0)),
                        disp: 0,
                    },
                ],
            ));
            e.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(pre)]));
            e.successors = vec![pre];
        }
        {
            let zero = b.g();
            let p = func.blocks.get_mut(&pre).unwrap();
            p.insts.push(inst(X86Opcode::MovRI, vec![vr(zero), imm(0)]));
            p.insts.push(inst(X86Opcode::MovRR, vec![vr(iv), vr(zero)]));
            p.insts.push(inst(X86Opcode::MovRI, vec![vr(acc), imm(0)]));
            p.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            p.successors = vec![header];
        }
        {
            let t = b.g();
            let nn = b.g();
            let h = func.blocks.get_mut(&header).unwrap();
            h.insts.push(inst(X86Opcode::MovRR, vec![vr(t), vr(iv)]));
            h.insts.push(inst(X86Opcode::MovRI, vec![vr(nn), imm(n)]));
            h.insts.push(inst(X86Opcode::CmpRR, vec![vr(t), vr(nn)]));
            h.insts.push(inst(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(b3),
                ],
            ));
            h.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(exit)]));
            h.successors = vec![b3, exit];
        }
        {
            let checks = bounds_check(&mut b, iv, n, latch, trap);
            let blk = func.blocks.get_mut(&b3).unwrap();
            blk.insts.extend(checks);
            blk.successors = vec![latch, trap];
        }
        {
            // addr = base + iv (stride-1 byte element address).
            let bp = b.g();
            let idx = b.g();
            let addr = b.g();
            let dst32 = b.g32();
            let wide = b.g();
            let acc_new = b.g();
            let tmp = b.g();
            let one = b.g();
            let niv = b.g();
            let mut stream = vec![
                inst(X86Opcode::MovRR, vec![vr(bp), vr(base)]),
                inst(X86Opcode::MovRR, vec![vr(idx), vr(iv)]),
                inst(X86Opcode::AddRR, vec![vr(addr), vr(bp), vr(idx)]),
                inst(X86Opcode::MovRM8, vec![vr(dst32), memaddr(addr)]),
                inst(X86Opcode::Movzx, vec![vr(wide), vr(dst32)]),
                inst(X86Opcode::AddRR, vec![vr(acc_new), vr(acc), vr(wide)]),
                inst(X86Opcode::MovRR, vec![vr(tmp), vr(acc_new)]),
                inst(X86Opcode::MovRR, vec![vr(acc), vr(tmp)]),
                inst(X86Opcode::MovRI, vec![vr(one), imm(1)]),
                inst(X86Opcode::AddRR, vec![vr(niv), vr(iv), vr(one)]),
                inst(X86Opcode::MovRR, vec![vr(iv), vr(niv)]),
                inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]),
            ];
            let blk = func.blocks.get_mut(&latch).unwrap();
            blk.insts.append(&mut stream);
            blk.successors = vec![header];
        }
        func.blocks
            .get_mut(&trap)
            .unwrap()
            .insts
            .push(inst(X86Opcode::Ud2, vec![]));
        func.blocks
            .get_mut(&exit)
            .unwrap()
            .insts
            .push(inst(X86Opcode::Ret, vec![]));
        func.next_vreg = b.next;
        LoopShape { func, iv }
    }

    fn build_kernighan_popcount_loop() -> X86ISelFunction {
        // 2-block loop: header tests x==0 -> exit else latch; latch does
        // x &= x-1 (SubRR with a register 1) + c += 1 + back-edge to header.
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I32],
        };
        let mut func = X86ISelFunction::new("pc_test".to_string(), sig);
        let mut b = B { next: 0 };
        let x0 = b.g(); // input x (Gpr64)
        let x = b.g(); // loop-carried x
        let c = b.g32(); // loop-carried c
        let (pre, header, latch, exit) = (Block(0), Block(1), Block(2), Block(3));
        for blk in [pre, header, latch, exit] {
            func.ensure_block(blk);
        }
        {
            let p = func.blocks.get_mut(&pre).unwrap();
            p.insts.push(inst(X86Opcode::MovRR, vec![vr(x), vr(x0)]));
            p.insts.push(inst(X86Opcode::MovRI, vec![vr(c), imm(0)]));
            p.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            p.successors = vec![header];
        }
        {
            let h = func.blocks.get_mut(&header).unwrap();
            h.insts.push(inst(X86Opcode::CmpRI, vec![vr(x), imm(0)]));
            h.insts.push(inst(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(exit),
                ],
            ));
            h.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(latch)]));
            h.successors = vec![exit, latch];
        }
        {
            let one = b.g();
            let t = b.g();
            let xn = b.g();
            let one2 = b.g32();
            let cn = b.g32();
            let l = func.blocks.get_mut(&latch).unwrap();
            l.insts.push(inst(X86Opcode::MovRI, vec![vr(one), imm(1)]));
            l.insts
                .push(inst(X86Opcode::SubRR, vec![vr(t), vr(x), vr(one)])); // x - 1
            l.insts
                .push(inst(X86Opcode::AndRR, vec![vr(xn), vr(x), vr(t)])); // x & (x-1)
            l.insts.push(inst(X86Opcode::MovRI, vec![vr(one2), imm(1)]));
            l.insts
                .push(inst(X86Opcode::AddRR, vec![vr(cn), vr(c), vr(one2)])); // c + 1
            l.insts.push(inst(X86Opcode::MovRR32, vec![vr(c), vr(cn)]));
            l.insts.push(inst(X86Opcode::MovRR, vec![vr(x), vr(xn)]));
            l.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            l.successors = vec![header];
        }
        func.blocks
            .get_mut(&exit)
            .unwrap()
            .insts
            .push(inst(X86Opcode::Ret, vec![]));
        func.next_vreg = b.next;
        func
    }

    #[test]
    fn crc_table_matches_reference_and_known_crc32() {
        // The compile-time table must equal the reference bit-loop AND the
        // standard CRC-32 (POLY 0xEDB88320) table (an INDEPENDENT cross-check:
        // T[0]=0, T[1]=0x77073096, T[255]=0x2D02EF8D are the canonical values).
        let t = crc_table_256(0xEDB8_8320);
        assert_eq!(t[0], 0x0000_0000, "T[0]");
        assert_eq!(t[1], 0x7707_3096, "T[1] canonical CRC-32");
        assert_eq!(t[2], 0xEE0E_612C, "T[2] canonical CRC-32");
        assert_eq!(t[255], 0x2D02_EF8D, "T[255] canonical CRC-32");
        // Re-derive every entry with an independent reference and compare.
        for b in 0..256u32 {
            let mut crc = b;
            for _ in 0..8 {
                crc = if crc & 1 != 0 {
                    (crc >> 1) ^ 0xEDB8_8320
                } else {
                    crc >> 1
                };
            }
            assert_eq!(t[b as usize], crc, "table[{b}] mismatch");
        }
    }

    #[test]
    fn kernighan_popcount_idiom_recognized_and_rewritten() {
        let env_scope = crate::env_lock::override_scope();
        let _default_on =
            crate::env_lock::ScopedEnvVar::unset(&env_scope, "TCG_NO_X86_POPCOUNT_IDIOM");
        // Kill switch: stays scalar.
        let mut off = build_kernighan_popcount_loop();
        let did_off = {
            let _kill_switch =
                crate::env_lock::ScopedEnvVar::set(&env_scope, "TCG_NO_X86_POPCOUNT_IDIOM", "1");
            X86Vectorize.run_on_function(&mut off)
        };
        assert!(!did_off, "kill switch: must not rewrite");
        assert_eq!(count_op(&off, X86Opcode::ImulRR), 0, "kill switch: no SWAR");

        // Default (on): rewritten to the branch-free SWAR (one ImulRR = the
        // byte-sum multiply step; the AndRR Kernighan core is gone from the
        // latch, replaced by the mask-ANDs; the latch loses its back-edge).
        let mut func = build_kernighan_popcount_loop();
        assert!(
            X86Vectorize.run_on_function(&mut func),
            "default-on: Kernighan popcount must rewrite"
        );
        assert_eq!(count_op(&func, X86Opcode::ImulRR), 1, "one SWAR multiply");
        // Latch (Block 2) now falls straight to the exit (no back-edge).
        let latch = func.blocks.get(&Block(2)).unwrap();
        assert_eq!(latch.successors, vec![Block(3)], "latch -> exit, loop gone");
    }

    fn build_bitrev_loop() -> X86ISelFunction {
        // 2-block loop: header tests i<64 -> latch else exit; latch does
        // r=(r<<1)|(x&1); x>>=1; i+=1; back-edge. Constant 1 register-materialized.
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("br_test".to_string(), sig);
        let mut b = B { next: 0 };
        let x0 = b.g();
        let r = b.g(); // loop-carried result (Gpr64)
        let x = b.g(); // loop-carried input (Gpr64)
        let i = b.g32(); // loop-carried trip counter (Gpr32)
        let (pre, header, latch, exit) = (Block(0), Block(1), Block(2), Block(3));
        for blk in [pre, header, latch, exit] {
            func.ensure_block(blk);
        }
        {
            let p = func.blocks.get_mut(&pre).unwrap();
            p.insts.push(inst(X86Opcode::MovRI, vec![vr(r), imm(0)]));
            p.insts.push(inst(X86Opcode::MovRR, vec![vr(x), vr(x0)]));
            p.insts.push(inst(X86Opcode::MovRI, vec![vr(i), imm(0)]));
            p.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            p.successors = vec![header];
        }
        {
            let h = func.blocks.get_mut(&header).unwrap();
            h.insts.push(inst(X86Opcode::CmpRI, vec![vr(i), imm(64)]));
            h.insts.push(inst(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::L),
                    X86ISelOperand::Block(latch),
                ],
            ));
            h.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(exit)]));
            h.successors = vec![exit, latch];
        }
        {
            let sl = b.g();
            let one = b.g();
            let ax = b.g();
            let rn = b.g();
            let xn = b.g();
            let one2 = b.g32();
            let in_ = b.g32();
            let l = func.blocks.get_mut(&latch).unwrap();
            l.insts
                .push(inst(X86Opcode::ShlRI, vec![vr(sl), vr(r), imm(1)])); // r<<1
            l.insts.push(inst(X86Opcode::MovRI, vec![vr(one), imm(1)]));
            l.insts
                .push(inst(X86Opcode::AndRR, vec![vr(ax), vr(x), vr(one)])); // x&1
            l.insts
                .push(inst(X86Opcode::OrRR, vec![vr(rn), vr(sl), vr(ax)])); // |
            l.insts
                .push(inst(X86Opcode::ShrRI, vec![vr(xn), vr(x), imm(1)])); // x>>1
            l.insts.push(inst(X86Opcode::MovRI, vec![vr(one2), imm(1)]));
            l.insts
                .push(inst(X86Opcode::AddRR, vec![vr(in_), vr(i), vr(one2)])); // i+1
            l.insts.push(inst(X86Opcode::MovRR, vec![vr(r), vr(rn)]));
            l.insts.push(inst(X86Opcode::MovRR, vec![vr(x), vr(xn)]));
            l.insts.push(inst(X86Opcode::MovRR32, vec![vr(i), vr(in_)]));
            l.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            l.successors = vec![header];
        }
        func.blocks
            .get_mut(&exit)
            .unwrap()
            .insts
            .push(inst(X86Opcode::Ret, vec![]));
        func.next_vreg = b.next;
        func
    }

    #[test]
    fn bitrev_idiom_recognized_and_rewritten() {
        let env_scope = crate::env_lock::override_scope();
        let _default_on =
            crate::env_lock::ScopedEnvVar::unset(&env_scope, "TCG_NO_X86_BITREV_IDIOM");
        let mut off = build_bitrev_loop();
        let did_off = {
            let _kill_switch =
                crate::env_lock::ScopedEnvVar::set(&env_scope, "TCG_NO_X86_BITREV_IDIOM", "1");
            X86Vectorize.run_on_function(&mut off)
        };
        assert!(!did_off, "kill switch: must not rewrite");

        let mut func = build_bitrev_loop();
        assert!(
            X86Vectorize.run_on_function(&mut func),
            "default-on: bit-reversal must rewrite"
        );
        // SWAR bit-reverse = 5 mask steps (each a ShrRI+MovRI+2×AndRR+ShlRI+OrRR)
        // + a final 32-bit swap (ShrRI+ShlRI+OrRR). 6 OrRR total; no back-edge.
        assert_eq!(count_op(&func, X86Opcode::OrRR), 6, "6 SWAR OR steps");
        assert_eq!(count_op(&func, X86Opcode::Bswap), 0, "no unproven BSWAP");
        let latch = func.blocks.get(&Block(2)).unwrap();
        assert_eq!(latch.successors, vec![Block(3)], "latch -> exit, loop gone");
    }

    #[test]
    fn byte_sum_reduction_gated_and_vectorizes() {
        let env_scope = crate::env_lock::override_scope();
        let _default_on = crate::env_lock::ScopedEnvVar::unset(&env_scope, "TCG_NO_X86_BYTE_SUM");
        // Kill switch (TCG_NO_X86_BYTE_SUM): the byte-sum loop stays scalar — no
        // PSADBW, no extra blocks.
        let LoopShape { mut func, .. } = build_byte_sum_loop(64);
        let blocks_before = func.block_order.len();
        let off = {
            let _kill_switch =
                crate::env_lock::ScopedEnvVar::set(&env_scope, "TCG_NO_X86_BYTE_SUM", "1");
            X86Vectorize.run_on_function(&mut func)
        };
        assert!(!off, "kill switch: must NOT vectorize");
        assert_eq!(
            count_op(&func, X86Opcode::Psadbw),
            0,
            "kill switch: no PSADBW"
        );
        assert_eq!(
            func.block_order.len(),
            blocks_before,
            "kill switch: no new blocks"
        );

        // Default (ON): vectorizes to a PSADBW-accumulate loop (VP+VH+VB+VR) with
        // one packed byte-sum, and the original scalar byte load survives as the
        // remainder.
        let LoopShape { mut func, .. } = build_byte_sum_loop(64);
        let blocks_before = func.block_order.len();
        let slots_before = func.stack_slots.len();
        let vectorized = X86Vectorize.run_on_function(&mut func);
        assert!(vectorized, "default-on: byte sum should vectorize");
        assert_eq!(
            count_op(&func, X86Opcode::Psadbw),
            1,
            "one PSADBW accumulate"
        );
        assert_eq!(
            count_op(&func, X86Opcode::Paddq),
            1,
            "one PADDQ lane accumulate"
        );
        assert_eq!(
            func.block_order.len(),
            blocks_before + 4,
            "VP + VH + VB + VR"
        );
        assert_eq!(func.stack_slots.len(), slots_before + 1, "one scratch slot");
        assert_eq!(
            count_op(&func, X86Opcode::MovRM8),
            1,
            "scalar byte load survives as the remainder"
        );
    }

    /// Rewrite the byte-sum loop's `Movzx wide64, b ; acc += wide64` reduction
    /// into the `count_ones()` shape rustc actually lowers
    /// `acc += (a[i] as u32).count_ones() as u64` to:
    ///
    /// ```text
    ///   MovRM8 b, [&a[iv]]
    ///   Movzx z32, b            ; u8 -> u32
    ///   MovRR32 w64, z32
    ///   MovRI k64, mask         ; the `as u32` truncation rustc keeps
    ///   AndRR m64, w64, k64
    ///   Popcnt p64, m64
    ///   acc += p64
    /// ```
    ///
    /// Note the widening `Movzx` lands in a Gpr32 here, exactly as in the real
    /// lowering — the Gpr64 value the accumulator consumes is POPCNT's result,
    /// not the zero-extended byte. `mask` is a parameter so a test can supply
    /// one that does NOT preserve the low byte.
    fn build_byte_sum_popcount_loop_masked(n: i64, mask: i64) -> LoopShape {
        let LoopShape { mut func, iv } = build_byte_sum_loop(n);
        let z = VReg::new(func.next_vreg, RegClass::Gpr32);
        let p = VReg::new(func.next_vreg + 1, RegClass::Gpr64);
        let w = VReg::new(func.next_vreg + 2, RegClass::Gpr64);
        let k = VReg::new(func.next_vreg + 3, RegClass::Gpr64);
        let m = VReg::new(func.next_vreg + 4, RegClass::Gpr64);
        func.next_vreg += 5;
        let blk = func.blocks.get_mut(&Block(4)).unwrap();
        let mzi = blk
            .insts
            .iter()
            .position(|i| i.opcode == X86Opcode::Movzx)
            .expect("byte-sum loop widens its load");
        let wide = match blk.insts[mzi].operands.first() {
            Some(X86ISelOperand::VReg(d)) => *d,
            _ => unreachable!("Movzx dst is a vreg"),
        };
        blk.insts[mzi].operands[0] = vr(z);
        let addi = blk
            .insts
            .iter()
            .position(|i| {
                i.opcode == X86Opcode::AddRR
                    && i.operands
                        .iter()
                        .any(|o| matches!(o, X86ISelOperand::VReg(v) if *v == wide))
            })
            .expect("byte-sum loop adds the widened byte");
        for op in blk.insts[addi].operands.iter_mut() {
            if matches!(op, X86ISelOperand::VReg(v) if *v == wide) {
                *op = vr(p);
            }
        }
        for (off, i) in [
            inst(X86Opcode::MovRR32, vec![vr(w), vr(z)]),
            inst(X86Opcode::MovRI, vec![vr(k), imm(mask)]),
            inst(X86Opcode::AndRR, vec![vr(m), vr(w), vr(k)]),
            inst(X86Opcode::Popcnt, vec![vr(p), vr(m)]),
        ]
        .into_iter()
        .enumerate()
        {
            blk.insts.insert(addi + off, i);
        }
        LoopShape { func, iv }
    }

    /// The shape rustc actually emits: `as u32` keeps a `0xffff_ffff` mask,
    /// which is the identity on a zero-extended byte.
    fn build_byte_sum_popcount_loop(n: i64) -> LoopShape {
        build_byte_sum_popcount_loop_masked(n, 0xffff_ffff)
    }

    #[test]
    fn byte_sum_popcount_reduction_vectorizes_with_swar() {
        let env_scope = crate::env_lock::override_scope();
        let _default_on = crate::env_lock::ScopedEnvVar::unset(&env_scope, "TCG_NO_X86_BYTE_SUM");

        // Kill switch (TCG_NO_X86_BYTE_SUM): stays scalar, no PSADBW.
        let LoopShape { mut func, .. } = build_byte_sum_popcount_loop(64);
        let off = {
            let _kill_switch =
                crate::env_lock::ScopedEnvVar::set(&env_scope, "TCG_NO_X86_BYTE_SUM", "1");
            X86Vectorize.run_on_function(&mut func)
        };
        assert!(!off, "kill switch: must NOT vectorize");
        assert_eq!(
            count_op(&func, X86Opcode::Psadbw),
            0,
            "kill switch: no PSADBW"
        );

        // Default (ON): the same PSADBW-accumulate loop as a plain byte sum,
        // with a per-byte SWAR population count folded in ahead of the SAD.
        let LoopShape { mut func, .. } = build_byte_sum_popcount_loop(64);
        let blocks_before = func.block_order.len();
        assert!(
            X86Vectorize.run_on_function(&mut func),
            "popcount byte sum should vectorize"
        );
        assert_eq!(
            count_op(&func, X86Opcode::Psadbw),
            1,
            "one PSADBW accumulate"
        );
        assert_eq!(
            count_op(&func, X86Opcode::Paddq),
            1,
            "one PADDQ lane accumulate"
        );
        assert_eq!(
            func.block_order.len(),
            blocks_before + 4,
            "VP + VH + VB + VR"
        );
        // The SWAR count itself — and it uses ONLY opcodes the x86 perimeter
        // already proves, with no lane-crossing shuffle.
        assert_eq!(count_op(&func, X86Opcode::Psrld), 3, "three SWAR shifts");
        assert_eq!(
            count_op(&func, X86Opcode::Psubb),
            1,
            "one SWAR byte subtract"
        );
        assert_eq!(count_op(&func, X86Opcode::Paddb), 2, "two SWAR byte adds");
        assert_eq!(count_op(&func, X86Opcode::Pand), 4, "four SWAR masks");
        // The packed body counts bits without POPCNT; the scalar remainder
        // still runs the original one for the `N % 16` tail.
        assert_eq!(
            count_op(&func, X86Opcode::Popcnt),
            1,
            "POPCNT survives only in the scalar remainder"
        );
        assert_eq!(
            count_op(&func, X86Opcode::MovRM8),
            1,
            "scalar byte load survives as the remainder"
        );
    }

    #[test]
    fn byte_sum_popcount_low_byte_destroying_mask_declines() {
        let env_scope = crate::env_lock::override_scope();
        let _default_on = crate::env_lock::ScopedEnvVar::unset(&env_scope, "TCG_NO_X86_BYTE_SUM");
        // `0xffff_ff00` clears the very bits the byte lives in, so the counted
        // value is NOT the loaded byte and the packed image would be wrong.
        // Only masks that leave all eight low bits set are the identity here.
        for mask in [0xffff_ff00_i64, 0xf0, 0x0f, 0x7f] {
            let LoopShape { mut func, .. } = build_byte_sum_popcount_loop_masked(64, mask);
            assert!(
                !X86Vectorize.run_on_function(&mut func),
                "mask {mask:#x} does not preserve the low byte and must decline"
            );
            assert_eq!(count_op(&func, X86Opcode::Psadbw), 0, "no PSADBW");
        }
    }

    #[test]
    fn byte_sum_popcount_second_popcnt_declines() {
        let env_scope = crate::env_lock::override_scope();
        let _default_on = crate::env_lock::ScopedEnvVar::unset(&env_scope, "TCG_NO_X86_BYTE_SUM");
        let LoopShape { mut func, .. } = build_byte_sum_popcount_loop(64);
        // A second POPCNT in the body has no packed image. Dropping it would be
        // a miscompile, so the recognizer must decline the whole loop.
        let extra = VReg::new(func.next_vreg, RegClass::Gpr64);
        func.next_vreg += 1;
        let blk = func.blocks.get_mut(&Block(4)).unwrap();
        let at = blk
            .insts
            .iter()
            .position(|i| i.opcode == X86Opcode::Popcnt)
            .expect("popcount loop has a POPCNT");
        let src = match blk.insts[at].operands.get(1) {
            Some(X86ISelOperand::VReg(v)) => *v,
            _ => unreachable!("POPCNT src is a vreg"),
        };
        blk.insts
            .insert(at + 1, inst(X86Opcode::Popcnt, vec![vr(extra), vr(src)]));
        assert!(
            !X86Vectorize.run_on_function(&mut func),
            "a second POPCNT must decline"
        );
        assert_eq!(count_op(&func, X86Opcode::Psadbw), 0, "no PSADBW");
    }

    #[test]
    fn byte_sum_popcount_mixed_with_direct_widening_declines() {
        let env_scope = crate::env_lock::override_scope();
        let _default_on = crate::env_lock::ScopedEnvVar::unset(&env_scope, "TCG_NO_X86_BYTE_SUM");
        let LoopShape { mut func, .. } = build_byte_sum_popcount_loop(64);
        // A loop that BOTH widens the byte straight to Gpr64 and counts its
        // bits carries two reduction terms; this recognizer claims neither.
        let w = VReg::new(func.next_vreg, RegClass::Gpr64);
        func.next_vreg += 1;
        let blk = func.blocks.get_mut(&Block(4)).unwrap();
        let li = blk
            .insts
            .iter()
            .position(|i| i.opcode == X86Opcode::MovRM8)
            .expect("popcount loop has a byte load");
        let load_dst = match blk.insts[li].operands.first() {
            Some(X86ISelOperand::VReg(d)) => *d,
            _ => unreachable!("MovRM8 dst is a vreg"),
        };
        blk.insts
            .insert(li + 1, inst(X86Opcode::Movzx, vec![vr(w), vr(load_dst)]));
        assert!(
            !X86Vectorize.run_on_function(&mut func),
            "mixed widening/popcount shape must decline"
        );
        assert_eq!(count_op(&func, X86Opcode::Psadbw), 0, "no PSADBW");
    }

    /// The predicated byte-equality COUNT shape, as a DIAMOND (what the bridge
    /// really emits — if-conversion cannot flatten it before the vectorizer
    /// runs, because the increment writes flags the `cmov` would need):
    ///
    /// ```text
    ///   header: iv <u n ? test : exit
    ///   test  : b = a[iv]; z = zext b; z == k ? inc : nop
    ///   inc   : merge = acc + 1        nop: merge = acc
    ///   latch : iv += 1; acc = merge
    /// ```
    ///
    /// `iv_init` is a parameter because this tier deliberately admits a
    /// NON-ZERO induction start, unlike every other tier here.
    fn build_byte_eq_count_loop(
        n: i64,
        k: i64,
        iv_init: i64,
        inc_delta: i64,
        eq_cc: X86CondCode,
    ) -> LoopShape {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("byte_eq_count_test".to_string(), sig);
        func.stack_slots = vec![StackSlotInfo::new(n as u32, 1)];
        let mut b = B { next: 0 };
        let base = b.g();
        let iv = b.g();
        let acc = b.g();
        let merge = b.g();
        let (entry, pre, header, test, inc, nop, latch, exit) = (
            Block(0),
            Block(1),
            Block(2),
            Block(3),
            Block(4),
            Block(5),
            Block(6),
            Block(7),
        );
        for blk in [entry, pre, header, test, inc, nop, latch, exit] {
            func.ensure_block(blk);
        }
        {
            let e = func.blocks.get_mut(&entry).unwrap();
            e.insts.push(inst(
                X86Opcode::Lea,
                vec![
                    vr(base),
                    X86ISelOperand::MemAddr {
                        base: Box::new(X86ISelOperand::StackSlot(0)),
                        disp: 0,
                    },
                ],
            ));
            e.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(pre)]));
            e.successors = vec![pre];
        }
        {
            let s0 = b.g();
            let p = func.blocks.get_mut(&pre).unwrap();
            p.insts
                .push(inst(X86Opcode::MovRI, vec![vr(s0), imm(iv_init)]));
            p.insts.push(inst(X86Opcode::MovRR, vec![vr(iv), vr(s0)]));
            p.insts.push(inst(X86Opcode::MovRI, vec![vr(acc), imm(0)]));
            p.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            p.successors = vec![header];
        }
        {
            let t = b.g();
            let nn = b.g();
            let h = func.blocks.get_mut(&header).unwrap();
            h.insts.push(inst(X86Opcode::MovRR, vec![vr(t), vr(iv)]));
            h.insts.push(inst(X86Opcode::MovRI, vec![vr(nn), imm(n)]));
            h.insts.push(inst(X86Opcode::CmpRR, vec![vr(t), vr(nn)]));
            h.insts.push(inst(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(test),
                ],
            ));
            h.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(exit)]));
            h.successors = vec![test, exit];
        }
        {
            let bp = b.g();
            let idx = b.g();
            let addr = b.g();
            let d8 = b.g32();
            let z = b.g();
            let blk = func.blocks.get_mut(&test).unwrap();
            blk.insts.extend([
                inst(X86Opcode::MovRR, vec![vr(bp), vr(base)]),
                inst(X86Opcode::MovRR, vec![vr(idx), vr(iv)]),
                inst(X86Opcode::AddRR, vec![vr(addr), vr(bp), vr(idx)]),
                inst(X86Opcode::MovRM8, vec![vr(d8), memaddr(addr)]),
                inst(X86Opcode::Movzx, vec![vr(z), vr(d8)]),
                inst(X86Opcode::CmpRI, vec![vr(z), imm(k)]),
                inst(
                    X86Opcode::Jcc,
                    vec![X86ISelOperand::CondCode(eq_cc), X86ISelOperand::Block(inc)],
                ),
                inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(nop)]),
            ]);
            blk.successors = vec![inc, nop];
        }
        {
            let one = b.g();
            let t = b.g();
            let blk = func.blocks.get_mut(&inc).unwrap();
            blk.insts.extend([
                inst(X86Opcode::MovRI, vec![vr(one), imm(inc_delta)]),
                inst(X86Opcode::AddRR, vec![vr(t), vr(acc), vr(one)]),
                inst(X86Opcode::MovRR, vec![vr(merge), vr(t)]),
                inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(latch)]),
            ]);
            blk.successors = vec![latch];
        }
        {
            let blk = func.blocks.get_mut(&nop).unwrap();
            blk.insts.extend([
                inst(X86Opcode::MovRR, vec![vr(merge), vr(acc)]),
                inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(latch)]),
            ]);
            blk.successors = vec![latch];
        }
        {
            let one = b.g();
            let niv = b.g();
            let blk = func.blocks.get_mut(&latch).unwrap();
            blk.insts.extend([
                inst(X86Opcode::MovRI, vec![vr(one), imm(1)]),
                inst(X86Opcode::AddRR, vec![vr(niv), vr(iv), vr(one)]),
                inst(X86Opcode::MovRR, vec![vr(iv), vr(niv)]),
                inst(X86Opcode::MovRR, vec![vr(acc), vr(merge)]),
                inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]),
            ]);
            blk.successors = vec![header];
        }
        func.blocks
            .get_mut(&exit)
            .unwrap()
            .insts
            .push(inst(X86Opcode::Ret, vec![]));
        func.next_vreg = b.next;
        LoopShape { func, iv }
    }

    #[test]
    fn byte_eq_count_gated_and_vectorizes() {
        let env_scope = crate::env_lock::override_scope();
        let _on = crate::env_lock::ScopedEnvVar::unset(&env_scope, "TCG_NO_X86_BYTE_EQ_COUNT");

        let LoopShape { mut func, .. } = build_byte_eq_count_loop(1024, 0, 0, 1, X86CondCode::E);
        let off = {
            let _kill =
                crate::env_lock::ScopedEnvVar::set(&env_scope, "TCG_NO_X86_BYTE_EQ_COUNT", "1");
            X86Vectorize.run_on_function(&mut func)
        };
        assert!(!off, "kill switch: must NOT vectorize");
        assert_eq!(
            count_op(&func, X86Opcode::Pcmpeqb),
            0,
            "kill switch: no PCMPEQB"
        );

        let LoopShape { mut func, .. } = build_byte_eq_count_loop(1024, 0, 0, 1, X86CondCode::E);
        let blocks_before = func.block_order.len();
        assert!(X86Vectorize.run_on_function(&mut func), "should vectorize");
        assert_eq!(count_op(&func, X86Opcode::Pcmpeqb), 1, "one PCMPEQB");
        assert_eq!(
            count_op(&func, X86Opcode::Psubb),
            1,
            "one PSUBB (0 - mask => 0/1)"
        );
        assert_eq!(count_op(&func, X86Opcode::Psadbw), 1, "one PSADBW");
        assert_eq!(count_op(&func, X86Opcode::Paddq), 1, "one PADDQ");
        assert_eq!(
            func.block_order.len(),
            blocks_before + 4,
            "VP + VH + VB + VR"
        );
        assert_eq!(
            count_op(&func, X86Opcode::MovRM8),
            1,
            "the scalar byte load survives as the remainder"
        );
    }

    /// The whole point of this tier's separate header analysis: every other
    /// tier requires the IV to start at literal 0.
    #[test]
    fn byte_eq_count_admits_a_nonzero_iv_start() {
        let env_scope = crate::env_lock::override_scope();
        let _on = crate::env_lock::ScopedEnvVar::unset(&env_scope, "TCG_NO_X86_BYTE_EQ_COUNT");
        for start in [1, 3, 7, 15] {
            let LoopShape { mut func, .. } =
                build_byte_eq_count_loop(1024, 0, start, 1, X86CondCode::E);
            assert!(
                X86Vectorize.run_on_function(&mut func),
                "IV starting at {start} must still vectorize"
            );
            assert_eq!(count_op(&func, X86Opcode::Pcmpeqb), 1);
        }
    }

    /// The guard is `iv < bound - 15`, so no chunk can read past the slot from
    /// ANY start. Pin the emitted bound rather than trusting the derivation.
    #[test]
    fn byte_eq_count_guard_keeps_every_chunk_in_slot() {
        let env_scope = crate::env_lock::override_scope();
        let _on = crate::env_lock::ScopedEnvVar::unset(&env_scope, "TCG_NO_X86_BYTE_EQ_COUNT");
        let LoopShape { mut func, .. } = build_byte_eq_count_loop(1024, 0, 3, 1, X86CondCode::E);
        assert!(X86Vectorize.run_on_function(&mut func));
        // Locate the VECTOR header: the block whose `Jcc` targets the block
        // holding the PCMPEQB. The ORIGINAL scalar header legitimately still
        // compares against 1024, so a function-wide scan proves nothing.
        let vb = *func
            .blocks
            .iter()
            .find(|(_, b)| b.insts.iter().any(|i| i.opcode == X86Opcode::Pcmpeqb))
            .expect("vectorized body exists")
            .0;
        let vh = func
            .blocks
            .values()
            .find(|b| {
                b.insts.iter().any(|i| {
                    i.opcode == X86Opcode::Jcc
                        && matches!(i.operands.get(1), Some(X86ISelOperand::Block(t)) if *t == vb)
                })
            })
            .expect("vector header exists");
        let limits: Vec<i64> = vh
            .insts
            .iter()
            .filter(|i| i.opcode == X86Opcode::MovRI)
            .filter_map(|i| match i.operands.get(1) {
                Some(X86ISelOperand::Imm(v)) => Some(*v),
                _ => None,
            })
            .collect();
        assert!(
            limits.contains(&1009),
            "vector guard must be `iv < bound - 15` = 1009, got {limits:?}"
        );
        assert!(
            !limits.contains(&1024),
            "a `iv < bound` guard would read past the slot from a non-zero start"
        );
    }

    #[test]
    fn byte_eq_count_declines_wrong_shapes() {
        let env_scope = crate::env_lock::override_scope();
        let _on = crate::env_lock::ScopedEnvVar::unset(&env_scope, "TCG_NO_X86_BYTE_EQ_COUNT");
        // Inverted polarity: the NOT-equal arm increments, so this counts
        // MISmatches — a different reduction, not claimed here.
        let LoopShape { mut func, .. } = build_byte_eq_count_loop(1024, 0, 0, 1, X86CondCode::NE);
        assert!(
            !X86Vectorize.run_on_function(&mut func),
            "inverted polarity must decline"
        );
        assert_eq!(count_op(&func, X86Opcode::Pcmpeqb), 0);

        // `count += 2` is not a count.
        let LoopShape { mut func, .. } = build_byte_eq_count_loop(1024, 0, 0, 2, X86CondCode::E);
        assert!(
            !X86Vectorize.run_on_function(&mut func),
            "non-unit increment must decline"
        );
        assert_eq!(count_op(&func, X86Opcode::Pcmpeqb), 0);

        // A bound below one full vector has no packed iteration.
        let LoopShape { mut func, .. } = build_byte_eq_count_loop(8, 0, 0, 1, X86CondCode::E);
        assert!(
            !X86Vectorize.run_on_function(&mut func),
            "bound < 16 must decline"
        );
        assert_eq!(count_op(&func, X86Opcode::Pcmpeqb), 0);
    }

    /// Rewrite the byte-sum loop's bounds check from the `Jcc->Ud2` trap-block
    /// diamond into the inline `TrapBoundsCheckExact [ic, ic, Imm(bound)]` proof
    /// carrier (the post-Sentinel-S5 lowering that b02_sieve now emits). When
    /// `index_is_iv` the carrier's index is a copy of the IV (the real,
    /// provably-safe shape); otherwise it is `iv+iv` (=2*iv, a non-IV index).
    /// `bound` is the carrier's immediate. Block(3) becomes the single-successor
    /// carrier block (no trap edge).
    fn build_byte_sum_loop_carrier(n: i64, index_is_iv: bool, bound: i64) -> LoopShape {
        let LoopShape { mut func, iv } = build_byte_sum_loop(n);
        let mut b = B {
            next: func.next_vreg,
        };
        let ic = b.g();
        let index_def = if index_is_iv {
            inst(X86Opcode::MovRR, vec![vr(ic), vr(iv)])
        } else {
            inst(X86Opcode::AddRR, vec![vr(ic), vr(iv), vr(iv)])
        };
        let carrier = vec![
            index_def,
            inst(
                X86Opcode::TrapBoundsCheckExact,
                vec![vr(ic), vr(ic), imm(bound)],
            ),
            inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(4))]),
        ];
        let blk = func.blocks.get_mut(&Block(3)).unwrap();
        blk.insts = carrier;
        blk.successors = vec![Block(4)]; // latch only — the carrier has no trap edge
        func.next_vreg = b.next;
        LoopShape { func, iv }
    }

    /// The inline `TrapBoundsCheckExact` carrier with `index==iv` and
    /// `bound>=n_trip` is a provably-in-bounds guard: the byte-sum recognizer
    /// admits it and vectorizes exactly as with the trap-block diamond. This is
    /// the b02_sieve shape after the Sentinel-S5 bounds-check lowering change.
    #[test]
    fn byte_sum_carrier_bounds_check_vectorizes() {
        crate::env_lock::with_env_overrides_removed(&["TCG_NO_X86_BYTE_SUM"], || {
            let LoopShape { mut func, .. } = build_byte_sum_loop_carrier(64, true, 64);
            let blocks_before = func.block_order.len();
            let vectorized = X86Vectorize.run_on_function(&mut func);
            assert!(vectorized, "carrier byte sum should vectorize");
            assert_eq!(
                count_op(&func, X86Opcode::Psadbw),
                1,
                "one PSADBW accumulate through the carrier"
            );
            assert_eq!(
                count_op(&func, X86Opcode::Paddq),
                1,
                "one PADDQ lane accumulate"
            );
            assert_eq!(
                func.block_order.len(),
                blocks_before + 4,
                "VP + VH + VB + VR"
            );
            // The carrier survives in the untouched scalar remainder.
            assert_eq!(
                count_op(&func, X86Opcode::TrapBoundsCheckExact),
                1,
                "carrier retained in the scalar remainder"
            );
        });
    }

    /// SOUNDNESS near-miss: a carrier whose `bound < n_trip` could trap inside the
    /// vectorized iteration range, so omitting it in the packed loop would drop a
    /// trap. The recognizer must DECLINE (fall back to the fully-checked scalar
    /// loop). Mirrors `block_has_iv_bound_compare`'s `c >= n_trip` discipline.
    #[test]
    fn byte_sum_carrier_bound_below_trip_declines() {
        crate::env_lock::with_env_overrides_removed(&["TCG_NO_X86_BYTE_SUM"], || {
            let LoopShape { mut func, .. } = build_byte_sum_loop_carrier(64, true, 63);
            let vectorized = X86Vectorize.run_on_function(&mut func);
            assert!(!vectorized, "bound < n_trip must NOT vectorize");
            assert_eq!(count_op(&func, X86Opcode::Psadbw), 0, "no PSADBW");
        });
    }

    /// SOUNDNESS near-miss: a carrier whose index is `2*iv` (not the bare IV) does
    /// not certify that the vectorized iterations `iv in [0, n_trip)` stay in
    /// bounds, so the recognizer must DECLINE.
    #[test]
    fn byte_sum_carrier_non_iv_index_declines() {
        crate::env_lock::with_env_overrides_removed(&["TCG_NO_X86_BYTE_SUM"], || {
            let LoopShape { mut func, .. } = build_byte_sum_loop_carrier(64, false, 64);
            let vectorized = X86Vectorize.run_on_function(&mut func);
            assert!(!vectorized, "non-IV carrier index must NOT vectorize");
            assert_eq!(count_op(&func, X86Opcode::Psadbw), 0, "no PSADBW");
        });
    }

    /// Assert a sum-reduction vectorized: one PADDD accumulate, no PMULLD, the
    /// vacc-init + xa MOVDQU loads, one MOVDQU spill, no shuffle/hadd pseudos,
    /// and the original scalar load survives.
    fn assert_sum_reduction_vectorized(func: &X86ISelFunction) {
        assert_eq!(count_op(func, X86Opcode::Paddd), 1, "one packed accumulate");
        assert_eq!(count_op(func, X86Opcode::Pmulld), 0, "sum has no multiply");
        assert_eq!(
            count_op(func, X86Opcode::MovdquRM),
            2,
            "vacc-init load + a load"
        );
        assert_eq!(
            count_op(func, X86Opcode::MovdquMR),
            1,
            "one vacc spill (h-reduce)"
        );
        // Covered horizontal reduce only — no shuffle pseudo.
        assert_eq!(count_op(func, X86Opcode::Pshufd), 0);
        // Original scalar load survives (2 loads: 4 h-reduce scalar loads + 1).
        assert_eq!(count_op(func, X86Opcode::MovRM32), 4 + 1);
    }

    #[test]
    fn vectorizes_integer_sum_reduction() {
        let LoopShape { mut func, iv } = build_reduction_loop(100, RedKind::Sum);
        let blocks_before = func.block_order.len();
        let slots_before = func.stack_slots.len();
        assert!(
            X86Vectorize.run_on_function(&mut func),
            "sum should vectorize"
        );
        assert_eq!(
            func.block_order.len(),
            blocks_before + 4,
            "VP + VH + VB + VR"
        );
        assert_eq!(func.stack_slots.len(), slots_before + 1, "one scratch slot");
        assert_eq!(func.stack_slots.last().unwrap().size, 16);
        assert_sum_reduction_vectorized(&func);
        // Shared counter reused; vector body steps it by 4.
        assert!(func.blocks.values().flat_map(|b| b.insts.iter()).any(|i| {
            i.opcode == X86Opcode::AddRR
                && matches!(i.operands.get(1), Some(X86ISelOperand::VReg(d)) if *d == iv)
                && i.operands.len() == 3
        }));
        // Preheader redirected off the scalar header.
        let pre = func.blocks.get(&Block(1)).unwrap();
        let jmp_target = pre
            .insts
            .iter()
            .rev()
            .find(|i| i.opcode == X86Opcode::Jmp)
            .and_then(|i| match i.operands.first() {
                Some(X86ISelOperand::Block(t)) => Some(*t),
                _ => None,
            })
            .unwrap();
        assert_ne!(
            jmp_target,
            Block(2),
            "preheader must be redirected off header"
        );
    }

    #[test]
    fn vectorizes_integer_dot_product() {
        let LoopShape { mut func, .. } = build_reduction_loop(64, RedKind::Dot);
        assert!(
            X86Vectorize.run_on_function(&mut func),
            "dot should vectorize"
        );
        assert_eq!(count_op(&func, X86Opcode::Pmulld), 1, "one packed multiply");
        assert_eq!(
            count_op(&func, X86Opcode::Paddd),
            1,
            "one packed accumulate"
        );
        // vacc-init + a load + b load.
        assert_eq!(count_op(&func, X86Opcode::MovdquRM), 3);
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 1, "one vacc spill");
        assert_eq!(count_op(&func, X86Opcode::Pshufd), 0);
        // 2 scalar loads survive + 4 h-reduce loads = 6.
        assert_eq!(count_op(&func, X86Opcode::MovRM32), 2 + 4);
    }

    #[test]
    fn rejects_float_sum_reduction() {
        // THE critical adversarial: a float sum is NOT associative, so lane-
        // partials + combine != the sequential sum. It MUST stay scalar. (Rejected
        // at the load opcode: MOVSS != MOVRM32; also the acc is Fpr128, not Gpr32,
        // and the add is ADDSS, not ADDRR — a triple fail-safe.)
        let LoopShape { mut func, .. } = build_reduction_loop(100, RedKind::FloatSum);
        assert!(
            !X86Vectorize.run_on_function(&mut func),
            "float sum must stay scalar"
        );
        assert_eq!(count_op(&func, X86Opcode::Paddd), 0);
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
    }

    #[test]
    fn rejects_subtraction_reduction() {
        // `acc -= a[k]` is a SubRR reduction — subtraction is not commutative, and
        // we only prove integer ADD associative/commutative. MUST stay scalar.
        let LoopShape { mut func, .. } = build_reduction_loop(64, RedKind::SubReduce);
        assert!(
            !X86Vectorize.run_on_function(&mut func),
            "sub-reduce must stay scalar"
        );
        assert_eq!(count_op(&func, X86Opcode::Paddd), 0);
    }

    #[test]
    fn rejects_accumulator_escaping_reduction() {
        // `acc` is read into a SECOND value inside the loop — a consumer would
        // observe the reordered partial sums. MUST stay scalar.
        let LoopShape { mut func, .. } = build_reduction_loop(64, RedKind::AccEscapes);
        assert!(
            !X86Vectorize.run_on_function(&mut func),
            "escaping acc must stay scalar"
        );
        assert_eq!(count_op(&func, X86Opcode::Paddd), 0);
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 0);
    }

    #[test]
    fn rejects_accumulator_stored_to_memory() {
        // `acc` is stored to memory mid-loop (it escapes). A reduction writes no
        // memory in-loop; any store disqualifies it. MUST stay scalar.
        let LoopShape { mut func, .. } = build_reduction_loop(64, RedKind::AccStored);
        assert!(
            !X86Vectorize.run_on_function(&mut func),
            "stored acc must stay scalar"
        );
        assert_eq!(count_op(&func, X86Opcode::Paddd), 0);
    }

    #[test]
    fn rejects_small_trip_reduction() {
        // N < lanes: no full vector iteration.
        let LoopShape { mut func, .. } = build_reduction_loop(3, RedKind::Sum);
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_eq!(count_op(&func, X86Opcode::Paddd), 0);
    }

    // ------------------------------------------------------------------
    // saxpy-Q (i64 RMW accumulate at invariant flat offsets — matmul's
    // inner loop). The builder replicates the EXACT raw-isel shape the
    // bridge emits for `c[i*N + j] += k * x[m*N + j]` over `[i64; _]`
    // locals: flat index = ImulRR(leaf, MovRI mult) + iv, per-access
    // Setcc(B)/Movzx/AndRI/CmpRI/Jcc(NE) guard diamonds against a FLAT
    // bound, 64-bit MovRM/MovMR through ImulRR*8+AddRR addresses.
    // ------------------------------------------------------------------

    /// Adversarial knobs for `build_saxpyq_loop`. `default()` is the exact
    /// accepted shape.
    struct QKnobs {
        n: i64,
        bound: i64,
        slot_bytes: u32,
        scale: i64,
        /// The store recomputes its flat index from a DIFFERENT leaf than the
        /// accumulate load (a would-be cross-element RMW).
        store_leaf_differs: bool,
        /// The multiply source reads the DESTINATION slot at a different
        /// invariant offset (a would-be loop-carried dependence).
        x_reads_dest_at_other_offset: bool,
        /// The offset leaf is redefined inside the body (not invariant).
        leaf_redefined_inside: bool,
        /// The scalar factor `k` is redefined inside the body.
        k_redefined_inside: bool,
        /// One guard block's compare is unclassifiable (guards an unrelated
        /// value) — no in-bounds evidence for the elision.
        unclassifiable_guard: bool,
        /// One side exit targets a non-trap block.
        non_trap_side_exit: bool,
        /// The multiply source reads the destination slot at the SAME flat
        /// offset (`c[f] += k*c[f]` — legal, read-before-write per iteration).
        x_is_dest_same_offset: bool,
    }

    impl QKnobs {
        fn default() -> Self {
            QKnobs {
                n: 6,
                bound: 32,
                slot_bytes: 32 * 8,
                scale: 8,
                store_leaf_differs: false,
                x_reads_dest_at_other_offset: false,
                leaf_redefined_inside: false,
                k_redefined_inside: false,
                unclassifiable_guard: false,
                non_trap_side_exit: false,
                x_is_dest_same_offset: false,
            }
        }
    }

    /// Emit `flat = leaf*mult + iv` in the raw-isel idiom.
    fn flat_of(b: &mut B, leaf: VReg, mult: i64, iv: VReg) -> (VReg, Vec<X86ISelInst>) {
        let lc = b.g();
        let m = b.g();
        let ml = b.g();
        let ivc = b.g();
        let fl = b.g();
        let insts = vec![
            inst(X86Opcode::MovRR, vec![vr(lc), vr(leaf)]),
            inst(X86Opcode::MovRI, vec![vr(m), imm(mult)]),
            inst(X86Opcode::ImulRR, vec![vr(ml), vr(lc), vr(m)]),
            inst(X86Opcode::MovRR, vec![vr(ivc), vr(iv)]),
            inst(X86Opcode::AddRR, vec![vr(fl), vr(ml), vr(ivc)]),
        ];
        (fl, insts)
    }

    /// Emit the raw-isel guard-diamond tail `flat <u bound ? cont : trap`
    /// (CmpRR + Setcc(B) + Movzx/Movzx/AndRI + CmpRI + Jcc(NE) + Jmp).
    fn guard_flat(b: &mut B, flat: VReg, bound: i64, cont: Block, trap: Block) -> Vec<X86ISelInst> {
        let bnd = b.g();
        let s32 = b.g32();
        let s64 = b.g();
        vec![
            inst(X86Opcode::MovRI, vec![vr(bnd), imm(bound)]),
            inst(X86Opcode::CmpRR, vec![vr(flat), vr(bnd)]),
            inst(
                X86Opcode::Setcc,
                vec![vr(s32), X86ISelOperand::CondCode(X86CondCode::B)],
            ),
            inst(X86Opcode::Movzx, vec![vr(s32), vr(s32)]),
            inst(X86Opcode::Movzx, vec![vr(s64), vr(s32)]),
            inst(X86Opcode::AndRI, vec![vr(s64), vr(s64), imm(1)]),
            inst(X86Opcode::CmpRI, vec![vr(s64), imm(0)]),
            inst(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(cont),
                ],
            ),
            inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(trap)]),
        ]
    }

    /// Build the saxpy-Q shape (see the section comment). Slot 0 = `c` (the
    /// RMW destination), slot 1 = `x` (the multiply source).
    fn build_saxpyq_loop(k: QKnobs) -> LoopShape {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("saxpyq_test".to_string(), sig);
        func.stack_slots = vec![
            StackSlotInfo::new(k.slot_bytes, 8),
            StackSlotInfo::new(k.slot_bytes, 8),
        ];
        let mut b = B { next: 0 };

        let base_c = b.g();
        let base_x = b.g();
        let iv = b.g();
        let leaf_c = b.g(); // outer-loop-counter stand-in (runtime, OrRR def)
        let leaf_x = b.g();
        let leaf_alt = b.g(); // for store_leaf_differs
        let kinv = b.g(); // the invariant i64 scalar factor

        let entry = Block(0);
        let pre = Block(1);
        let header = Block(2);
        let g1 = Block(3);
        let g2 = Block(4);
        let g3 = Block(5);
        let latch = Block(6);
        let trap = Block(7);
        let exit = Block(8);
        let nontrap = Block(9);
        for blk in [entry, pre, header, g1, g2, g3, latch, trap, exit, nontrap] {
            func.ensure_block(blk);
        }

        let mult = 4i64;

        // Entry: the two Lea slot bases + runtime leaves + invariant k.
        {
            let one = b.g();
            let two = b.g();
            let e = func.blocks.get_mut(&entry).unwrap();
            for (slot, base) in [(0u32, base_c), (1u32, base_x)] {
                e.insts.push(inst(
                    X86Opcode::Lea,
                    vec![
                        vr(base),
                        X86ISelOperand::MemAddr {
                            base: Box::new(X86ISelOperand::StackSlot(slot)),
                            disp: 0,
                        },
                    ],
                ));
            }
            e.insts.push(inst(X86Opcode::MovRI, vec![vr(one), imm(1)]));
            e.insts.push(inst(X86Opcode::MovRI, vec![vr(two), imm(2)]));
            // Runtime (non-const through canon) values: OrRR defs.
            e.insts
                .push(inst(X86Opcode::OrRR, vec![vr(leaf_c), vr(one), vr(two)]));
            e.insts
                .push(inst(X86Opcode::OrRR, vec![vr(leaf_x), vr(two), vr(one)]));
            e.insts
                .push(inst(X86Opcode::OrRR, vec![vr(leaf_alt), vr(one), vr(one)]));
            e.insts
                .push(inst(X86Opcode::OrRR, vec![vr(kinv), vr(two), vr(two)]));
            e.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(pre)]));
            e.successors = vec![pre];
        }
        // Preheader: iv = 0.
        {
            let zero = b.g();
            let p = func.blocks.get_mut(&pre).unwrap();
            p.insts.push(inst(X86Opcode::MovRI, vec![vr(zero), imm(0)]));
            p.insts.push(inst(X86Opcode::MovRR, vec![vr(iv), vr(zero)]));
            p.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            p.successors = vec![header];
        }
        // Header: iv <u N ? g1 : exit.
        {
            let t = b.g();
            let nn = b.g();
            let h = func.blocks.get_mut(&header).unwrap();
            h.insts.push(inst(X86Opcode::MovRR, vec![vr(t), vr(iv)]));
            h.insts.push(inst(X86Opcode::MovRI, vec![vr(nn), imm(k.n)]));
            h.insts.push(inst(X86Opcode::CmpRR, vec![vr(t), vr(nn)]));
            h.insts.push(inst(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(g1),
                ],
            ));
            h.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(exit)]));
            h.successors = vec![g1, exit];
        }

        // The x access's (slot, leaf, offset): normally slot 1 at leaf_x.
        let (x_base, x_leaf) = if k.x_is_dest_same_offset {
            (base_c, leaf_c)
        } else if k.x_reads_dest_at_other_offset {
            (base_c, leaf_x)
        } else {
            (base_x, leaf_x)
        };

        // g1: flat_c = leaf_c*mult + iv; guard; (knob: redefine leaf inside).
        let (flat_c, mut g1_insts) = flat_of(&mut b, leaf_c, mult, iv);
        if k.leaf_redefined_inside {
            // A def of leaf_c INSIDE the body — the offset is not invariant.
            let z = b.g();
            g1_insts.insert(0, inst(X86Opcode::MovRI, vec![vr(z), imm(7)]));
            g1_insts.insert(1, inst(X86Opcode::MovRR, vec![vr(leaf_c), vr(z)]));
        }
        if k.unclassifiable_guard {
            // Guard an UNRELATED value (still a trap diamond, but the compare
            // gives no in-bounds evidence for any classified index).
            let junk = b.g();
            g1_insts.push(inst(X86Opcode::MovRR, vec![vr(junk), vr(kinv)]));
            g1_insts.extend(guard_flat(&mut b, junk, k.bound, g2, trap));
        } else {
            g1_insts.extend(guard_flat(&mut b, flat_c, k.bound, g2, trap));
        }
        {
            let blk = func.blocks.get_mut(&g1).unwrap();
            blk.insts.extend(g1_insts);
            blk.successors = vec![g2, trap];
        }

        // g2: load c[flat_c]; flat_x = x_leaf*mult + iv; guard.
        let cval = b.g();
        {
            let (addr, mut stream) = addr_of_scale(&mut b, base_c, flat_c, k.scale);
            stream.push(inst(X86Opcode::MovRM, vec![vr(cval), memaddr(addr)]));
            let (flat_x, fx) = flat_of(&mut b, x_leaf, mult, iv);
            stream.extend(fx);
            let guard_target = if k.non_trap_side_exit { nontrap } else { trap };
            stream.extend(guard_flat(&mut b, flat_x, k.bound, g3, guard_target));
            let blk = func.blocks.get_mut(&g2).unwrap();
            blk.insts.extend(stream);
            blk.successors = vec![g3, guard_target];
            // Stash flat_x for g3 via a copy (single-def chain preserved).
            let blk_flat_x = flat_x;
            // g3: load x[flat_x]; prod = k*x; sum = c + prod; flat_c2; guard.
            let xval = b.g();
            let kreg = if k.k_redefined_inside {
                let km = b.g();
                // A def inside the body: km = iv | kinv (iv-dependent!).
                let blk3 = func.blocks.get_mut(&g3).unwrap();
                blk3.insts
                    .push(inst(X86Opcode::OrRR, vec![vr(km), vr(iv), vr(kinv)]));
                km
            } else {
                kinv
            };
            let (xaddr, mut s3) = addr_of_scale(&mut b, x_base, blk_flat_x, k.scale);
            s3.push(inst(X86Opcode::MovRM, vec![vr(xval), memaddr(xaddr)]));
            let prod = b.g();
            s3.push(inst(X86Opcode::ImulRR, vec![vr(prod), vr(kreg), vr(xval)]));
            let sum = b.g();
            s3.push(inst(X86Opcode::AddRR, vec![vr(sum), vr(cval), vr(prod)]));
            let store_leaf = if k.store_leaf_differs {
                leaf_alt
            } else {
                leaf_c
            };
            let (flat_c2, fc2) = flat_of(&mut b, store_leaf, mult, iv);
            s3.extend(fc2);
            s3.extend(guard_flat(&mut b, flat_c2, k.bound, latch, trap));
            let blk3 = func.blocks.get_mut(&g3).unwrap();
            blk3.insts.extend(s3);
            blk3.successors = vec![latch, trap];
            // latch: store c[flat_c2] = sum; iv += 1; back-edge.
            let (saddr, mut s4) = addr_of_scale(&mut b, base_c, flat_c2, k.scale);
            let sm = b.g();
            s4.push(inst(X86Opcode::MovRR, vec![vr(sm), vr(sum)]));
            s4.push(inst(X86Opcode::MovMR, vec![memaddr(saddr), vr(sm)]));
            let one = b.g();
            let niv = b.g();
            s4.push(inst(X86Opcode::MovRI, vec![vr(one), imm(1)]));
            s4.push(inst(X86Opcode::AddRR, vec![vr(niv), vr(iv), vr(one)]));
            s4.push(inst(X86Opcode::MovRR, vec![vr(iv), vr(niv)]));
            s4.push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            let blk4 = func.blocks.get_mut(&latch).unwrap();
            blk4.insts.extend(s4);
            blk4.successors = vec![header];
        }
        // trap: single Ud2. nontrap: Ud2 + something (NOT a pure trap block).
        {
            func.blocks
                .get_mut(&trap)
                .unwrap()
                .insts
                .push(inst(X86Opcode::Ud2, vec![]));
            let nt = func.blocks.get_mut(&nontrap).unwrap();
            let d = b.g();
            nt.insts.push(inst(X86Opcode::MovRI, vec![vr(d), imm(9)]));
            nt.insts.push(inst(X86Opcode::Ud2, vec![]));
        }
        // exit: Ret.
        {
            func.blocks
                .get_mut(&exit)
                .unwrap()
                .insts
                .push(inst(X86Opcode::Ret, vec![]));
        }

        func.next_vreg = b.next;
        LoopShape { func, iv }
    }

    fn assert_saxpyq_not_vectorized(func: &X86ISelFunction) {
        for op in [
            X86Opcode::Pmuludq,
            X86Opcode::Psllq,
            X86Opcode::Psrlq,
            X86Opcode::Paddq,
            X86Opcode::MovdquMR,
        ] {
            assert_eq!(count_op(func, op), 0, "{op:?} must not be emitted");
        }
    }

    #[test]
    fn vectorizes_saxpyq_matmul_inner_loop_shape() {
        let LoopShape { mut func, .. } = build_saxpyq_loop(QKnobs::default());
        assert!(
            X86Vectorize.run_on_function(&mut func),
            "the matmul inner-loop shape must vectorize"
        );
        // N=6: vn=6 packed elements = 3 two-lane groups. The body is unrolled
        // by 2 (one VBU iteration covering [0,4) = 2 groups) plus a single VBT
        // tail group covering [4,6). So the per-group PMULUDQ-compose op counts
        // are 3x the single-group shape.
        let groups = 3;
        // The exact packed 64-bit multiply compose, per group.
        assert_eq!(
            count_op(&func, X86Opcode::Pmuludq),
            3 * groups,
            "3 PMULUDQ partial products/group"
        );
        assert_eq!(
            count_op(&func, X86Opcode::Psrlq),
            groups + 1,
            "b_hi extract/group, PLUS one preheader PSRLQ deriving [K>>32;2] \
             from the [K;2] broadcast in-register"
        );
        assert_eq!(
            count_op(&func, X86Opcode::Psllq),
            groups,
            "cross-term << 32/group"
        );
        assert_eq!(
            count_op(&func, X86Opcode::Paddq),
            3 * groups,
            "t2+t3, t1+t5, c+prod per group"
        );
        // x load + c load per group; one packed store per group. Plus ONE
        // broadcast MOVDQU reload ([K;2]) from the scratch slot — the second
        // reload ([K>>32;2]) is gone: it is now derived in-register by PSRLQ,
        // which removes a store-to-load forwarding stall (8+8-byte stores
        // reloaded as a single 16-byte load).
        assert_eq!(count_op(&func, X86Opcode::MovdquRM), 2 * groups + 1);
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), groups);
        // Proof-covered scratch-slot broadcast: no shuffle/pack broadcast ops.
        assert_eq!(count_op(&func, X86Opcode::MovqToXmm), 0);
        assert_eq!(count_op(&func, X86Opcode::Punpcklqdq), 0);
        // No uncovered helper ops.
        assert_eq!(count_op(&func, X86Opcode::Pshufd), 0);
        assert_eq!(count_op(&func, X86Opcode::Pinsrq), 0);
        // Two runtime obligations ((leaf_c, 4) and (leaf_x, 4)): the fail-safe
        // check constant `bound - (n-1) = 32 - 5 = 27` is materialized twice.
        let check_consts = func
            .blocks
            .values()
            .flat_map(|b| b.insts.iter())
            .filter(|i| {
                i.opcode == X86Opcode::MovRI
                    && matches!(i.operands.get(1), Some(X86ISelOperand::Imm(27)))
            })
            .count();
        assert_eq!(
            check_consts, 2,
            "two runtime bound checks fail-safe to scalar"
        );
    }

    #[test]
    fn vectorizes_saxpyq_rmw_of_own_slot_same_offset() {
        // `c[f] += k * c[f]` — the multiply source IS the destination element.
        // Read-before-write per iteration; the packed body preserves it.
        let LoopShape { mut func, .. } = build_saxpyq_loop(QKnobs {
            x_is_dest_same_offset: true,
            ..QKnobs::default()
        });
        assert!(X86Vectorize.run_on_function(&mut func));
        // N=6 -> 3 two-lane groups (2 unrolled + 1 tail); 3 PMULUDQ per group.
        assert_eq!(count_op(&func, X86Opcode::Pmuludq), 9);
    }

    /// The x86 regalloc replay requires CONTIGUOUS block ids. The emitter
    /// conditionally omits the unrolled loop VBU (small `vn`) and/or the packed
    /// tail VBT (even `vn`), so its block-id assignment must never leave a hole.
    /// This asserts contiguity across the trip-count shapes that hit each path.
    fn assert_block_ids_contiguous(func: &X86ISelFunction) {
        let mut ids: Vec<u32> = func.blocks.keys().map(|b| b.0).collect();
        ids.sort_unstable();
        let min = *ids.first().unwrap();
        let max = *ids.last().unwrap();
        assert_eq!(
            ids.len() as u32,
            max - min + 1,
            "block ids must be contiguous (no gap); got {ids:?}"
        );
        // block_order must list exactly the emitted blocks (no dangling id).
        let mut order_ids: Vec<u32> = func.block_order.iter().map(|b| b.0).collect();
        order_ids.sort_unstable();
        assert_eq!(order_ids, ids, "block_order must match emitted blocks");
    }

    #[test]
    fn vectorizes_saxpyq_no_unroll_tail_only_small_n() {
        // N=3: vn=2 (< 4) so has_unrolled=false, has_tail=true — the VBT-only
        // path. Regression guard for the block-id-gap fail-close (REGALLOC-063):
        // vectorizes, no VBU, and block ids stay contiguous.
        let LoopShape { mut func, .. } = build_saxpyq_loop(QKnobs {
            n: 3,
            ..QKnobs::default()
        });
        assert!(
            X86Vectorize.run_on_function(&mut func),
            "N=3 must vectorize"
        );
        // Exactly one 2-lane group (the tail): 3 PMULUDQ, one packed store.
        assert_eq!(count_op(&func, X86Opcode::Pmuludq), 3);
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 1);
        assert_block_ids_contiguous(&func);
    }

    #[test]
    fn vectorizes_saxpyq_unroll_no_tail_even_multiple() {
        // N=4: vn=4, vn4=4 so has_unrolled=true, has_tail=false — VBU only, no
        // VBT. Two groups in the unrolled body; block ids contiguous.
        let LoopShape { mut func, .. } = build_saxpyq_loop(QKnobs {
            n: 4,
            ..QKnobs::default()
        });
        assert!(
            X86Vectorize.run_on_function(&mut func),
            "N=4 must vectorize"
        );
        assert_eq!(count_op(&func, X86Opcode::Pmuludq), 6, "2 unrolled groups");
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 2);
        assert_block_ids_contiguous(&func);
    }

    #[test]
    fn vectorizes_saxpyq_unroll_and_tail_odd_multiple() {
        // N=7: vn=6, vn4=4 so has_unrolled=true AND has_tail=true — VBU (2
        // groups) + VBT (1 group) + a 1-element scalar remainder. Full coverage;
        // block ids contiguous.
        let LoopShape { mut func, .. } = build_saxpyq_loop(QKnobs {
            n: 7,
            ..QKnobs::default()
        });
        assert!(
            X86Vectorize.run_on_function(&mut func),
            "N=7 must vectorize"
        );
        assert_eq!(
            count_op(&func, X86Opcode::Pmuludq),
            9,
            "3 groups (2 unrolled + 1 tail)"
        );
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 3);
        assert_block_ids_contiguous(&func);
    }

    #[test]
    fn rejects_saxpyq_wrong_element_scale() {
        // 4-byte elements under 64-bit loads: the address stride does not match
        // the access width. MUST stay scalar.
        let LoopShape { mut func, .. } = build_saxpyq_loop(QKnobs {
            scale: 4,
            ..QKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_saxpyq_not_vectorized(&func);
    }

    #[test]
    fn rejects_saxpyq_store_index_leaf_mismatch() {
        // The store's flat index uses a DIFFERENT leaf than the accumulate
        // load — a cross-element RMW (loop-carried dependence). MUST stay
        // scalar.
        let LoopShape { mut func, .. } = build_saxpyq_loop(QKnobs {
            store_leaf_differs: true,
            ..QKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_saxpyq_not_vectorized(&func);
    }

    #[test]
    fn rejects_saxpyq_mul_source_aliasing_dest_at_other_offset() {
        // x reads the DESTINATION slot at a different invariant offset: lane
        // `j` could read an element another iteration writes. MUST stay scalar.
        let LoopShape { mut func, .. } = build_saxpyq_loop(QKnobs {
            x_reads_dest_at_other_offset: true,
            ..QKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_saxpyq_not_vectorized(&func);
    }

    #[test]
    fn rejects_saxpyq_leaf_redefined_inside() {
        // The offset leaf is written inside the body — the flat offset is not
        // invariant, so neither the runtime check nor the folded base pointer
        // would track the scalar loop. MUST stay scalar.
        let LoopShape { mut func, .. } = build_saxpyq_loop(QKnobs {
            leaf_redefined_inside: true,
            ..QKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_saxpyq_not_vectorized(&func);
    }

    #[test]
    fn rejects_saxpyq_k_redefined_inside() {
        // The scalar factor is recomputed (iv-dependently) inside the loop.
        // MUST stay scalar.
        let LoopShape { mut func, .. } = build_saxpyq_loop(QKnobs {
            k_redefined_inside: true,
            ..QKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_saxpyq_not_vectorized(&func);
    }

    #[test]
    fn rejects_saxpyq_bound_smaller_than_trip() {
        // Guard bound B < N: even offset 0 could trap mid-loop; there is no
        // runtime check that proves all N iterations in-bounds. MUST stay
        // scalar.
        let LoopShape { mut func, .. } = build_saxpyq_loop(QKnobs {
            bound: 4, // < n == 6
            ..QKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_saxpyq_not_vectorized(&func);
    }

    #[test]
    fn rejects_saxpyq_slot_smaller_than_bound() {
        // slot_size < bound*8: an in-bounds-per-guard index could still leave
        // the slot (the guard bound is not evidence of slot fit). MUST stay
        // scalar.
        let LoopShape { mut func, .. } = build_saxpyq_loop(QKnobs {
            slot_bytes: 16 * 8, // < bound(32)*8
            ..QKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_saxpyq_not_vectorized(&func);
    }

    #[test]
    fn rejects_saxpyq_unclassifiable_guard() {
        // A trap diamond whose compare guards an unrelated value: no in-bounds
        // evidence for eliding it. MUST stay scalar.
        let LoopShape { mut func, .. } = build_saxpyq_loop(QKnobs {
            unclassifiable_guard: true,
            ..QKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_saxpyq_not_vectorized(&func);
    }

    #[test]
    fn rejects_saxpyq_non_trap_side_exit() {
        // An off-chain edge to a non-pure-trap block (an observable exit).
        // MUST stay scalar.
        let LoopShape { mut func, .. } = build_saxpyq_loop(QKnobs {
            non_trap_side_exit: true,
            ..QKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_saxpyq_not_vectorized(&func);
    }

    #[test]
    fn rejects_saxpyq_small_trip() {
        // N < 2 lanes: no full vector iteration.
        let LoopShape { mut func, .. } = build_saxpyq_loop(QKnobs {
            n: 1,
            ..QKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_saxpyq_not_vectorized(&func);
    }

    // ------------------------------------------------------------------
    // Heap-slice i64 sum reduction with a RUNTIME trip count
    // (`while k < v.len() { acc += v[k] }`). slot0 models the Vec home
    // (ptr @ +0, len @ +16), slot1 the slice-reborrow temp the body
    // re-stores (ptr, len) into. The positive must become a PADDQ-accumulate
    // loop with a runtime `vN = len & !1` gate; every adversarial knob MUST
    // stay scalar (a wrong admit here is a silent miscompile).
    // ------------------------------------------------------------------
    #[derive(Clone, Copy, Default)]
    struct HKnobs {
        /// The trap guard's bound loads `[P + 0]` (the ptr field) instead of
        /// the header's `[P + 16]`: bound values may differ — MUST stay scalar.
        guard_bound_other_field: bool,
        /// The second slice-temp store stores `acc` (not a field-load result):
        /// the accumulator escapes to memory — MUST stay scalar.
        store_acc: bool,
        /// The slice-temp stores target the Vec home slot itself (store slot
        /// == field-load slot): the invariance license dies — MUST stay scalar.
        stores_hit_vec_slot: bool,
        /// The element load is 32-bit (`MovRM32`, Gpr32): wrong lane width —
        /// MUST stay scalar.
        elem_load_32: bool,
        /// The element address uses stride 4 (`iv*4`), not the 8-byte element
        /// stride — MUST stay scalar.
        stride_4: bool,
        /// The data-pointer reload through the slice temp happens BEFORE the
        /// store that forwards it (reads a stale value on iteration 0) —
        /// MUST stay scalar.
        reload_before_store: bool,
        /// `acc` is additionally read by a second in-body computation (the
        /// reordered partials would be observable) — MUST stay scalar.
        acc_second_reader: bool,
        /// A `Call` in the body — MUST stay scalar.
        call_in_body: bool,
        /// The off-chain side exit is not a pure single-`Ud2` trap block —
        /// MUST stay scalar.
        non_trap_side_exit: bool,
    }

    /// Build the raw post-ISel heap-sum shape (mirroring the bridge's real
    /// output for `while k < v.len() { acc += v[k] }`, as dumped via
    /// `TCG_TRACE_VECTORIZE_DUMP`), with adversarial variations per `HKnobs`.
    fn build_heap_sumq_loop(k: HKnobs) -> LoopShape {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("heap_sumq_test".to_string(), sig);
        // slot0: the Vec home (ptr @ +0, cap @ +8, len @ +16); slot1: the
        // slice-reborrow temp (ptr @ +0, len @ +8).
        func.stack_slots = vec![StackSlotInfo::new(24, 8), StackSlotInfo::new(16, 8)];
        let mut b = B { next: 0 };

        let vp = b.g(); // &Vec (slot0 base)
        let vs = b.g(); // &slice temp (slot1 base)
        let iv = b.g();
        let acc = b.g();

        let entry = Block(0);
        let pre = Block(1);
        let header = Block(2);
        let guard = Block(3);
        let latch = Block(4);
        let trap = Block(5);
        let exit = Block(6);
        for blk in [entry, pre, header, guard, latch, trap, exit] {
            func.ensure_block(blk);
        }

        let vec_slot: u32 = 0;
        let temp_slot: u32 = if k.stores_hit_vec_slot { 0 } else { 1 };

        // Entry: slot base addresses + acc init.
        {
            let acc0 = b.g();
            let e = func.blocks.get_mut(&entry).unwrap();
            e.insts.push(inst(
                X86Opcode::Lea,
                vec![
                    vr(vp),
                    X86ISelOperand::MemAddr {
                        base: Box::new(X86ISelOperand::StackSlot(vec_slot)),
                        disp: 0,
                    },
                ],
            ));
            e.insts.push(inst(
                X86Opcode::Lea,
                vec![
                    vr(vs),
                    X86ISelOperand::MemAddr {
                        base: Box::new(X86ISelOperand::StackSlot(temp_slot)),
                        disp: 0,
                    },
                ],
            ));
            e.insts.push(inst(X86Opcode::MovRI, vec![vr(acc0), imm(7)]));
            e.insts
                .push(inst(X86Opcode::MovRR, vec![vr(acc), vr(acc0)]));
            e.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(pre)]));
            e.successors = vec![pre];
        }
        // Preheader: iv = 0.
        {
            let zero = b.g();
            let p = func.blocks.get_mut(&pre).unwrap();
            p.insts.push(inst(X86Opcode::MovRI, vec![vr(zero), imm(0)]));
            p.insts.push(inst(X86Opcode::MovRR, vec![vr(iv), vr(zero)]));
            p.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            p.successors = vec![header];
        }
        // The pinned `<u`-branch tail: CmpRR(lhs, rhs); Setcc B; Movzx; Movzx;
        // AndRI(1); CmpRI 0; Jcc NE taken; Jmp fallthrough.
        let below_branch_tail =
            |b: &mut B, lhs: VReg, rhs: VReg, taken: Block, fall: Block| -> Vec<X86ISelInst> {
                let t = b.g32();
                let t2 = b.g();
                vec![
                    inst(X86Opcode::CmpRR, vec![vr(lhs), vr(rhs)]),
                    inst(
                        X86Opcode::Setcc,
                        vec![vr(t), X86ISelOperand::CondCode(X86CondCode::B)],
                    ),
                    inst(X86Opcode::Movzx, vec![vr(t), vr(t)]),
                    inst(X86Opcode::Movzx, vec![vr(t2), vr(t)]),
                    inst(X86Opcode::AndRI, vec![vr(t2), vr(t2), imm(1)]),
                    inst(X86Opcode::CmpRI, vec![vr(t2), imm(0)]),
                    inst(
                        X86Opcode::Jcc,
                        vec![
                            X86ISelOperand::CondCode(X86CondCode::NE),
                            X86ISelOperand::Block(taken),
                        ],
                    ),
                    inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(fall)]),
                ]
            };
        // A 64-bit load of `[base + disp]` via the Lea+MovRM idiom.
        let field_load = |b: &mut B, base: VReg, disp: i32| -> (VReg, Vec<X86ISelInst>) {
            let a = b.g();
            let v = b.g();
            let insts = vec![
                inst(
                    X86Opcode::Lea,
                    vec![
                        vr(a),
                        X86ISelOperand::MemAddr {
                            base: Box::new(vr(base)),
                            disp,
                        },
                    ],
                ),
                inst(X86Opcode::MovRM, vec![vr(v), memaddr(a)]),
            ];
            (v, insts)
        };

        // Header: `iv <u [vp + 16]` (runtime bound), continue → guard, exit.
        {
            let ivc = b.g();
            let (len, mut insts) = field_load(&mut b, vp, 16);
            insts.insert(0, inst(X86Opcode::MovRR, vec![vr(ivc), vr(iv)]));
            insts.extend(below_branch_tail(&mut b, ivc, len, guard, exit));
            let h = func.blocks.get_mut(&header).unwrap();
            h.insts = insts;
            h.successors = vec![guard, exit];
        }
        // Guard block: load ptr + len, re-store the pair into the slice temp,
        // then `iv <u len2 ? latch : trap`.
        let ptr_reload: VReg;
        {
            let ivc2 = b.g();
            let mut insts = vec![inst(X86Opcode::MovRR, vec![vr(ivc2), vr(iv)])];
            let (ptr, ptr_insts) = field_load(&mut b, vp, 0);
            insts.extend(ptr_insts);
            let guard_field = if k.guard_bound_other_field { 0 } else { 16 };
            let (len2, len_insts) = field_load(&mut b, vp, guard_field);
            insts.extend(len_insts);
            // Optional adversarial: the reload through the temp BEFORE the
            // store it forwards from.
            let early_reload = if k.reload_before_store {
                let (r, r_insts) = field_load(&mut b, vs, 0);
                insts.extend(r_insts);
                Some(r)
            } else {
                None
            };
            // Store pair: [vs+0] = ptr; [vs+8] = len2 (or acc, adversarially).
            insts.push(inst(X86Opcode::MovMR, vec![memaddr(vs), vr(ptr)]));
            let s8 = b.g();
            insts.push(inst(
                X86Opcode::Lea,
                vec![
                    vr(s8),
                    X86ISelOperand::MemAddr {
                        base: Box::new(vr(vs)),
                        disp: 8,
                    },
                ],
            ));
            let stored2 = if k.store_acc { acc } else { len2 };
            insts.push(inst(X86Opcode::MovMR, vec![memaddr(s8), vr(stored2)]));
            if k.call_in_body {
                insts.push(inst(X86Opcode::Call, vec![]));
            }
            insts.extend(below_branch_tail(&mut b, ivc2, len2, latch, trap));
            // The latch reads the data pointer back through the temp (the
            // rustc shape), or uses the adversarial early reload.
            ptr_reload = early_reload.unwrap_or({
                // placeholder; the real reload is emitted in the latch below
                VReg::new(u32::MAX, RegClass::Gpr64)
            });
            let g = func.blocks.get_mut(&guard).unwrap();
            g.insts = insts;
            g.successors = vec![latch, trap];
        }
        // Latch: elem = [reload(vs+0) + iv*stride]; acc += elem; iv += 1.
        {
            let mut insts = Vec::new();
            let base_ptr = if k.reload_before_store {
                ptr_reload
            } else {
                let (r, r_insts) = field_load(&mut b, vs, 0);
                insts.extend(r_insts);
                r
            };
            let ivc3 = b.g();
            let stride = b.g();
            let off = b.g();
            let ea = b.g();
            let stride_v: i64 = if k.stride_4 { 4 } else { 8 };
            insts.push(inst(X86Opcode::MovRR, vec![vr(ivc3), vr(iv)]));
            insts.push(inst(X86Opcode::MovRI, vec![vr(stride), imm(stride_v)]));
            insts.push(inst(X86Opcode::ImulRR, vec![vr(off), vr(ivc3), vr(stride)]));
            insts.push(inst(X86Opcode::AddRR, vec![vr(ea), vr(base_ptr), vr(off)]));
            let (elem, nacc) = if k.elem_load_32 {
                let e32 = b.g32();
                insts.push(inst(X86Opcode::MovRM32, vec![vr(e32), memaddr(ea)]));
                let widened = b.g();
                insts.push(inst(X86Opcode::Movzx, vec![vr(widened), vr(e32)]));
                let nacc = b.g();
                insts.push(inst(X86Opcode::AddRR, vec![vr(nacc), vr(acc), vr(widened)]));
                (widened, nacc)
            } else {
                let elem = b.g();
                insts.push(inst(X86Opcode::MovRM, vec![vr(elem), memaddr(ea)]));
                let nacc = b.g();
                insts.push(inst(X86Opcode::AddRR, vec![vr(nacc), vr(acc), vr(elem)]));
                (elem, nacc)
            };
            let _ = elem;
            if k.acc_second_reader {
                let snoop = b.g();
                insts.push(inst(X86Opcode::MovRR, vec![vr(snoop), vr(acc)]));
            }
            let one = b.g();
            let niv = b.g();
            insts.push(inst(X86Opcode::MovRI, vec![vr(one), imm(1)]));
            insts.push(inst(X86Opcode::AddRR, vec![vr(niv), vr(iv), vr(one)]));
            insts.push(inst(X86Opcode::MovRR, vec![vr(acc), vr(nacc)]));
            insts.push(inst(X86Opcode::MovRR, vec![vr(iv), vr(niv)]));
            insts.push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            let l = func.blocks.get_mut(&latch).unwrap();
            l.insts = insts;
            l.successors = vec![header];
        }
        // Trap: a single Ud2 (or, adversarially, an impure side exit).
        {
            let t = func.blocks.get_mut(&trap).unwrap();
            if k.non_trap_side_exit {
                let x = b.g();
                t.insts.push(inst(X86Opcode::MovRI, vec![vr(x), imm(1)]));
            }
            t.insts.push(inst(X86Opcode::Ud2, vec![]));
            t.successors = vec![];
        }
        // Exit: reads only `acc` (the one sanctioned outside use).
        {
            let out = b.g();
            let e = func.blocks.get_mut(&exit).unwrap();
            e.insts.push(inst(X86Opcode::MovRR, vec![vr(out), vr(acc)]));
            e.insts.push(inst(X86Opcode::Ret, vec![]));
            e.successors = vec![];
        }
        func.block_order = vec![entry, pre, header, guard, latch, trap, exit];
        func.next_vreg = b.next;
        LoopShape { func, iv }
    }

    fn assert_heap_sumq_not_vectorized(func: &X86ISelFunction) {
        assert_eq!(count_op(func, X86Opcode::Paddq), 0);
        assert_eq!(count_op(func, X86Opcode::MovdquRM), 0);
        assert_eq!(count_op(func, X86Opcode::MovdquMR), 0);
    }

    #[test]
    fn vectorizes_heap_sumq_positive() {
        let LoopShape { mut func, .. } = build_heap_sumq_loop(HKnobs::default());
        assert!(X86Vectorize.run_on_function(&mut func));
        // A packed accumulate + a MOVDQU element load + the spill/reduce.
        assert_eq!(count_op(&func, X86Opcode::Paddq), 1);
        assert_eq!(count_op(&func, X86Opcode::MovdquRM), 2); // seed + element
        assert_eq!(count_op(&func, X86Opcode::MovdquMR), 1); // reduce spill
        // The runtime gate: len & !1 materialized via AndRI(-2).
        assert!(func.blocks.values().any(|blk| blk.insts.iter().any(|i| {
            i.opcode == X86Opcode::AndRI
                && matches!(i.operands.get(2), Some(X86ISelOperand::Imm(-2)))
        })));
        // The scalar loop remains intact as the epilogue (its element load
        // pattern — ImulRR by 8 — is still present).
        assert!(count_op(&func, X86Opcode::ImulRR) >= 1);
    }

    #[test]
    fn rejects_heap_sumq_guard_bound_other_field() {
        // The guard bound reads a DIFFERENT field than the header bound: the
        // guard is not provably dead — MUST stay scalar.
        let LoopShape { mut func, .. } = build_heap_sumq_loop(HKnobs {
            guard_bound_other_field: true,
            ..HKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_heap_sumq_not_vectorized(&func);
    }

    #[test]
    fn rejects_heap_sumq_acc_stored() {
        // The accumulator escapes to memory via the slice-temp store — the
        // reordered partials would be observable. MUST stay scalar.
        let LoopShape { mut func, .. } = build_heap_sumq_loop(HKnobs {
            store_acc: true,
            ..HKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_heap_sumq_not_vectorized(&func);
    }

    #[test]
    fn rejects_heap_sumq_stores_hit_vec_slot() {
        // The in-loop stores write the SAME slot the ptr/len fields are read
        // from: the invariance license (and thus guard elision) dies. MUST
        // stay scalar.
        let LoopShape { mut func, .. } = build_heap_sumq_loop(HKnobs {
            stores_hit_vec_slot: true,
            ..HKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_heap_sumq_not_vectorized(&func);
    }

    #[test]
    fn rejects_heap_sumq_elem_load_32() {
        // 32-bit element load: wrong lane width for the PADDQ slice. MUST
        // stay scalar.
        let LoopShape { mut func, .. } = build_heap_sumq_loop(HKnobs {
            elem_load_32: true,
            ..HKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_heap_sumq_not_vectorized(&func);
    }

    #[test]
    fn rejects_heap_sumq_stride_4() {
        // A 4-byte stride under a 64-bit load (`iv*4`): not the element
        // stride — packed lanes would misalign. MUST stay scalar.
        let LoopShape { mut func, .. } = build_heap_sumq_loop(HKnobs {
            stride_4: true,
            ..HKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_heap_sumq_not_vectorized(&func);
    }

    #[test]
    fn rejects_heap_sumq_reload_before_store() {
        // The data-pointer reload through the slice temp PRECEDES the store
        // that forwards it: iteration 0 would read a stale pointer. MUST
        // stay scalar.
        let LoopShape { mut func, .. } = build_heap_sumq_loop(HKnobs {
            reload_before_store: true,
            ..HKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_heap_sumq_not_vectorized(&func);
    }

    #[test]
    fn rejects_heap_sumq_acc_second_reader() {
        // `acc` is read by a second in-body computation: the intermediate
        // partial sums are observable. MUST stay scalar.
        let LoopShape { mut func, .. } = build_heap_sumq_loop(HKnobs {
            acc_second_reader: true,
            ..HKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_heap_sumq_not_vectorized(&func);
    }

    #[test]
    fn rejects_heap_sumq_call_in_body() {
        // A call could observe/clobber anything. MUST stay scalar.
        let LoopShape { mut func, .. } = build_heap_sumq_loop(HKnobs {
            call_in_body: true,
            ..HKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_heap_sumq_not_vectorized(&func);
    }

    #[test]
    fn rejects_heap_sumq_non_trap_side_exit() {
        // The side exit is not a pure single-`Ud2` block. MUST stay scalar.
        let LoopShape { mut func, .. } = build_heap_sumq_loop(HKnobs {
            non_trap_side_exit: true,
            ..HKnobs::default()
        });
        assert!(!X86Vectorize.run_on_function(&mut func));
        assert_heap_sumq_not_vectorized(&func);
    }

    // ------------------------------------------------------------------
    // Register-argument i64 sum reduction (recognize_regarg_sumq_loop). This
    // builder transcribes the EXACT post-ISel shape the bridge emits for the
    // inlined, SROA-promoted `for i in 0..s.len() { t += s[i] }` over a
    // register-held `&[i64]` (verified against a real O3 dump): the `(ptr, len)`
    // live in registers (here modelled as OrRR-defined loop-invariant vregs),
    // the header and per-element guard are chase_below_branch diamonds over the
    // SAME `len` register (own-length identity), the accumulator is threaded
    // through a MovRR copy before the reduction add, the element address is
    // `ImulRR(iv,8)+ptr`, and the body performs NO stores.
    // ------------------------------------------------------------------

    /// Adversarial knobs for `build_regarg_sumq_loop`. `default()` is the exact
    /// accepted shape.
    struct RKnobs {
        /// The per-element guard bound is a DIFFERENT invariant register than
        /// the header/trip-count bound (cross-length — own-length identity
        /// fails).
        cross_length: bool,
        /// The body stores to memory (not a pure reduction).
        has_store: bool,
        /// `len` is redefined inside the loop body (not loop-invariant).
        len_redefined_inside: bool,
        /// The summed term is `elem*elem` (`ImulRR(elem, elem)`) rather than the
        /// bare element (the Square reduction shape).
        square: bool,
        /// The summed term is `elem * OTHER` where OTHER is a distinct second
        /// element load (a genuine two-input product — NOT a self-square). MUST
        /// be rejected: the reg-arg tier packs only one element stream.
        cross_product: bool,
        /// The summed term is `x[iv] * y[iv]` — a SECOND element load from a
        /// second invariant pointer at the SAME index (the two-slice Dot shape).
        /// MUST vectorize (RegArgSumQKind::Dot).
        dot: bool,
    }
    impl RKnobs {
        fn default() -> Self {
            RKnobs {
                cross_length: false,
                has_store: false,
                len_redefined_inside: false,
                square: false,
                cross_product: false,
                dot: false,
            }
        }
    }

    /// Emit the chase_below_branch guard tail `lhs <u rhs ? cont : fall` in the
    /// exact raw-isel idiom (CmpRR + Setcc(B) + Movzx/Movzx + AndRI(_,1) + CmpRI
    /// + Jcc(NE, cont) + Jmp(fall)).
    fn chase_diamond(
        b: &mut B,
        lhs: VReg,
        rhs: VReg,
        cont: Block,
        fall: Block,
    ) -> Vec<X86ISelInst> {
        let s32 = b.g32();
        let s64 = b.g();
        vec![
            inst(X86Opcode::CmpRR, vec![vr(lhs), vr(rhs)]),
            inst(
                X86Opcode::Setcc,
                vec![vr(s32), X86ISelOperand::CondCode(X86CondCode::B)],
            ),
            inst(X86Opcode::Movzx, vec![vr(s32), vr(s32)]),
            inst(X86Opcode::Movzx, vec![vr(s64), vr(s32)]),
            inst(X86Opcode::AndRI, vec![vr(s64), vr(s64), imm(1)]),
            inst(X86Opcode::CmpRI, vec![vr(s64), imm(0)]),
            inst(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(cont),
                ],
            ),
            inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(fall)]),
        ]
    }

    fn build_regarg_sumq_loop(k: RKnobs) -> LoopShape {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("regarg_sumq_test".to_string(), sig);
        func.stack_slots = vec![StackSlotInfo::new(64, 8)]; // for the optional store
        let mut b = B { next: 0 };

        let ptr = b.g();
        let ptr2 = b.g(); // second invariant pointer (the Dot y-slice)
        let len = b.g();
        let len2 = b.g();
        let sbase = b.g();
        let acc = b.g();
        let iv = b.g();

        let entry = Block(0);
        let pre = Block(1);
        let header = Block(2);
        let guard = Block(3);
        let latch = Block(4);
        let trap = Block(5);
        let exit = Block(6);
        for blk in [entry, pre, header, guard, latch, trap, exit] {
            func.ensure_block(blk);
        }

        // Entry: runtime, loop-invariant (ptr, len[, len2]) via OrRR of imms.
        {
            let one = b.g();
            let two = b.g();
            let e = func.blocks.get_mut(&entry).unwrap();
            e.insts.push(inst(X86Opcode::MovRI, vec![vr(one), imm(1)]));
            e.insts.push(inst(X86Opcode::MovRI, vec![vr(two), imm(2)]));
            e.insts
                .push(inst(X86Opcode::OrRR, vec![vr(ptr), vr(one), vr(two)]));
            e.insts
                .push(inst(X86Opcode::OrRR, vec![vr(ptr2), vr(two), vr(two)]));
            e.insts
                .push(inst(X86Opcode::OrRR, vec![vr(len), vr(two), vr(one)]));
            e.insts
                .push(inst(X86Opcode::OrRR, vec![vr(len2), vr(one), vr(one)]));
            e.insts.push(inst(
                X86Opcode::Lea,
                vec![
                    vr(sbase),
                    X86ISelOperand::MemAddr {
                        base: Box::new(X86ISelOperand::StackSlot(0)),
                        disp: 0,
                    },
                ],
            ));
            e.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(pre)]));
            e.successors = vec![pre];
        }
        // Preheader: iv = 0; acc = 0.
        {
            let z0 = b.g();
            let z1 = b.g();
            let p = func.blocks.get_mut(&pre).unwrap();
            p.insts.push(inst(X86Opcode::MovRI, vec![vr(z0), imm(0)]));
            p.insts.push(inst(X86Opcode::MovRR, vec![vr(iv), vr(z0)]));
            p.insts.push(inst(X86Opcode::MovRI, vec![vr(z1), imm(0)]));
            p.insts.push(inst(X86Opcode::MovRR, vec![vr(acc), vr(z1)]));
            p.insts
                .push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            p.successors = vec![header];
        }
        // Header: iv <u len ? guard : exit (chase diamond over a copy of iv).
        {
            let ivh = b.g();
            let mut hs = vec![inst(X86Opcode::MovRR, vec![vr(ivh), vr(iv)])];
            hs.extend(chase_diamond(&mut b, ivh, len, guard, exit));
            let h = func.blocks.get_mut(&header).unwrap();
            h.insts.extend(hs);
            h.successors = vec![guard, exit];
        }
        // Guard: iv+1, acc copy, then iv <u len ? latch : trap.
        {
            let ivc = b.g();
            let one = b.g();
            let ivp1 = b.g();
            let accc = b.g();
            let guard_bound = if k.cross_length { len2 } else { len };
            let mut gs = vec![
                inst(X86Opcode::MovRR, vec![vr(ivc), vr(iv)]),
                inst(X86Opcode::MovRI, vec![vr(one), imm(1)]),
                inst(X86Opcode::AddRR, vec![vr(ivp1), vr(ivc), vr(one)]),
                inst(X86Opcode::MovRR, vec![vr(accc), vr(acc)]),
            ];
            gs.extend(chase_diamond(&mut b, ivc, guard_bound, latch, trap));
            let gblk = func.blocks.get_mut(&guard).unwrap();
            gblk.insts.extend(gs);
            gblk.successors = vec![latch, trap];
            // Stash the pieces the latch needs by recomputing them there.
            let _ = (ivp1, accc);
        }
        // Latch: elem = *(ptr + iv*8); acc = accc + elem; iv = iv+1.
        {
            // Recompute iv+1 and acc-copy locally (single-def per builder rule):
            // the guard's ivp1/accc are separate vregs; re-derive here to keep
            // the writeback self-contained and matching the real dump's latch.
            let (addc, addr_insts) = addr_of_scale(&mut b, ptr, iv, 8);
            let elem = b.g();
            let elemc = b.g();
            let accc2 = b.g();
            let accn = b.g();
            let one = b.g();
            let ivp1 = b.g();
            let mut ls = addr_insts;
            ls.push(inst(X86Opcode::MovRM, vec![vr(elem), memaddr(addc)]));
            ls.push(inst(X86Opcode::MovRR, vec![vr(elemc), vr(elem)]));
            ls.push(inst(X86Opcode::MovRR, vec![vr(accc2), vr(acc)]));
            // The summed term: bare element (Sum), its square `elem*elem`
            // (Square), the two-slice product `x[iv]*y[iv]` (Dot), or a
            // non-square product `elem*iv` (must be rejected).
            let term_reg = if k.square {
                let sq = b.g();
                ls.push(inst(X86Opcode::ImulRR, vec![vr(sq), vr(elemc), vr(elemc)]));
                sq
            } else if k.dot {
                let (addc2, addr2_insts) = addr_of_scale(&mut b, ptr2, iv, 8);
                let elem2 = b.g();
                let elem2c = b.g();
                let sq = b.g();
                ls.extend(addr2_insts);
                ls.push(inst(X86Opcode::MovRM, vec![vr(elem2), memaddr(addc2)]));
                ls.push(inst(X86Opcode::MovRR, vec![vr(elem2c), vr(elem2)]));
                ls.push(inst(X86Opcode::ImulRR, vec![vr(sq), vr(elemc), vr(elem2c)]));
                sq
            } else if k.cross_product {
                let sq = b.g();
                ls.push(inst(X86Opcode::ImulRR, vec![vr(sq), vr(elemc), vr(iv)]));
                sq
            } else {
                elemc
            };
            ls.push(inst(
                X86Opcode::AddRR,
                vec![vr(accn), vr(accc2), vr(term_reg)],
            ));
            if k.has_store {
                // A store into the (distinct) local slot — forfeits pure-reduce.
                ls.push(inst(X86Opcode::MovMR, vec![memaddr(sbase), vr(elem)]));
            }
            if k.len_redefined_inside {
                // Redefine `len` inside the loop — no longer invariant.
                let z = b.g();
                ls.push(inst(X86Opcode::MovRI, vec![vr(z), imm(9)]));
                ls.push(inst(X86Opcode::MovRR, vec![vr(len), vr(z)]));
            }
            ls.push(inst(X86Opcode::MovRR, vec![vr(acc), vr(accn)]));
            ls.push(inst(X86Opcode::MovRI, vec![vr(one), imm(1)]));
            ls.push(inst(X86Opcode::AddRR, vec![vr(ivp1), vr(iv), vr(one)]));
            ls.push(inst(X86Opcode::MovRR, vec![vr(iv), vr(ivp1)]));
            ls.push(inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(header)]));
            let lblk = func.blocks.get_mut(&latch).unwrap();
            lblk.insts.extend(ls);
            lblk.successors = vec![header];
        }
        // trap: single Ud2. exit: Ret.
        func.blocks
            .get_mut(&trap)
            .unwrap()
            .insts
            .push(inst(X86Opcode::Ud2, vec![]));
        func.blocks
            .get_mut(&exit)
            .unwrap()
            .insts
            .push(inst(X86Opcode::Ret, vec![]));

        func.next_vreg = b.next;
        LoopShape { func, iv }
    }

    #[test]
    fn vectorizes_regarg_i64_sum_reduction() {
        // K-way unrolled (default K=2): K independent PADDQ accumulators over
        // disjoint 2-lane groups + packed remainder + covered reduce + scalar
        // tail. Counts are derived from K so the test tracks the default.
        let k = super::regarg_unroll_k();
        let LoopShape { mut func, iv } = build_regarg_sumq_loop(RKnobs::default());
        let blocks_before = func.block_order.len();
        let slots_before = func.stack_slots.len();
        assert!(
            X86Vectorize.run_on_function(&mut func),
            "reg-arg i64 sum should vectorize"
        );
        // VP0 + VPS + VH + VB + RH + RB + CB.
        assert_eq!(
            func.block_order.len(),
            blocks_before + 7,
            "seven vector blocks"
        );
        assert_eq!(
            func.stack_slots.len(),
            slots_before + 1,
            "one 16-byte scratch slot"
        );
        assert_eq!(func.stack_slots.last().unwrap().size, 16);
        // PADDQ total = K (unrolled body) + 1 (remainder body) + (K-1) (combine).
        assert_eq!(
            count_op(&func, X86Opcode::Paddq),
            2 * k as usize,
            "K unrolled + 1 remainder + (K-1) combine PADDQ",
        );
        assert_eq!(count_op(&func, X86Opcode::Paddd), 0, "i64 lanes, not i32");
        // MovdquRM = K accumulator seeds + K unrolled loads + 1 remainder load.
        assert_eq!(
            count_op(&func, X86Opcode::MovdquRM),
            2 * k as usize + 1,
            "K seeds + K unrolled loads + 1 remainder load",
        );
        assert_eq!(
            count_op(&func, X86Opcode::MovdquMR),
            1,
            "one vacc0 spill (h-reduce)"
        );
        assert_eq!(
            count_op(&func, X86Opcode::Pshufd),
            0,
            "covered horizontal reduce only"
        );
        // The unrolled body block must hold EXACTLY K PADDQs (one per independent
        // accumulator/lane-group) and advance the shared counter by K*LANES_Q.
        let group = k * super::LANES_Q;
        let unrolled_body = func
            .blocks
            .values()
            .find(|bl| {
                bl.insts
                    .iter()
                    .filter(|i| i.opcode == X86Opcode::Paddq)
                    .count()
                    == k as usize
                    && bl.insts.iter().any(|i| i.opcode == X86Opcode::LeaSib)
            })
            .expect("a block with K PADDQs + a LeaSib group address (the unrolled body)");
        // It steps iv by a register that was loaded with the group constant.
        let steps_by_group = unrolled_body.insts.iter().any(|i| {
            i.opcode == X86Opcode::MovRI
                && matches!(i.operands.get(1), Some(X86ISelOperand::Imm(c)) if *c == group)
        }) && unrolled_body.insts.iter().any(|i| {
            i.opcode == X86Opcode::AddRR
                && matches!(i.operands.get(1), Some(X86ISelOperand::VReg(d)) if *d == iv)
        });
        assert!(
            steps_by_group,
            "unrolled body advances iv by K*LANES_Q = {group}"
        );
    }

    #[test]
    fn rejects_regarg_cross_length() {
        // CRITICAL: the per-element bound is a DIFFERENT register than the
        // trip-count bound. The own-length identity fails ⇒ MUST stay scalar
        // (a wrong vectorization here could read out of bounds).
        let LoopShape { mut func, .. } = build_regarg_sumq_loop(RKnobs {
            cross_length: true,
            ..RKnobs::default()
        });
        assert!(
            !X86Vectorize.run_on_function(&mut func),
            "cross-length must stay scalar"
        );
        assert_eq!(count_op(&func, X86Opcode::Paddq), 0);
    }

    #[test]
    fn rejects_regarg_body_store() {
        // A store in the body ⇒ not a pure reduction (aliasing + invariant-
        // reload soundness no longer hold). MUST stay scalar.
        let LoopShape { mut func, .. } = build_regarg_sumq_loop(RKnobs {
            has_store: true,
            ..RKnobs::default()
        });
        assert!(
            !X86Vectorize.run_on_function(&mut func),
            "store-bearing loop must stay scalar"
        );
        assert_eq!(count_op(&func, X86Opcode::Paddq), 0);
    }

    #[test]
    fn rejects_regarg_non_invariant_len() {
        // `len` is redefined inside the loop ⇒ not loop-invariant, so the
        // bound == trip-count identity is not established. MUST stay scalar.
        let LoopShape { mut func, .. } = build_regarg_sumq_loop(RKnobs {
            len_redefined_inside: true,
            ..RKnobs::default()
        });
        assert!(
            !X86Vectorize.run_on_function(&mut func),
            "non-invariant len must stay scalar"
        );
        assert_eq!(count_op(&func, X86Opcode::Paddq), 0);
    }

    #[test]
    fn vectorizes_regarg_i64_square_reduction() {
        // Square variant: term = ImulRR(elem, elem). Same packed PADDQ reduction
        // as Sum, plus a per-lane i64 packed multiply (PMULUDQ compose) inserted
        // between each load and the accumulate. Counts derive from K.
        let k = super::regarg_unroll_k() as usize;
        let LoopShape { mut func, .. } = build_regarg_sumq_loop(RKnobs {
            square: true,
            ..RKnobs::default()
        });
        assert!(
            X86Vectorize.run_on_function(&mut func),
            "reg-arg i64 square should vectorize"
        );
        // PADDQ = 2*K reduction (K unrolled + 1 remainder + K-1 combine) PLUS
        // 2 per packed square (the t2+t3 cross sum and the t1+cross final add);
        // there are K+1 packed squares (K unrolled + 1 remainder).
        assert_eq!(
            count_op(&func, X86Opcode::Paddq),
            2 * k + 2 * (k + 1),
            "reduction PADDQ + 2 per packed square",
        );
        // Each square multiply = 3 PMULUDQ; K unrolled + 1 remainder = K+1 muls.
        assert_eq!(
            count_op(&func, X86Opcode::Pmuludq),
            3 * (k + 1),
            "3 PMULUDQ per packed square (K unrolled + 1 remainder)",
        );
        // Two logical shifts (b_hi, a_hi) + one << 32 cross per packed square.
        assert_eq!(
            count_op(&func, X86Opcode::Psrlq),
            2 * (k + 1),
            "2 PSRLQ per square"
        );
        assert_eq!(
            count_op(&func, X86Opcode::Psllq),
            k + 1,
            "1 PSLLQ per square"
        );
    }

    #[test]
    fn vectorizes_regarg_i64_dot_reduction() {
        // Two-slice Dot variant: term = ImulRR(x[iv], y[iv]) of the loop's
        // EXACTLY-TWO element loads, each from its own invariant pointer. Same
        // packed PADDQ reduction + per-lane packed multiply as Square, plus one
        // extra MOVDQU y-load per multiply site (K unrolled + 1 remainder).
        let k = super::regarg_unroll_k() as usize;
        let LoopShape { mut func, .. } = build_regarg_sumq_loop(RKnobs {
            dot: true,
            ..RKnobs::default()
        });
        assert!(
            X86Vectorize.run_on_function(&mut func),
            "reg-arg i64 two-slice dot should vectorize"
        );
        // PADDQ = 2*K reduction (K unrolled + 1 remainder + K-1 combine) PLUS
        // 2 per packed multiply; K+1 multiply sites.
        assert_eq!(
            count_op(&func, X86Opcode::Paddq),
            2 * k + 2 * (k + 1),
            "reduction PADDQ + 2 per packed dot multiply",
        );
        // 3 PMULUDQ per packed multiply, K+1 sites — identical to Square.
        assert_eq!(
            count_op(&func, X86Opcode::Pmuludq),
            3 * (k + 1),
            "3 PMULUDQ per dot multiply"
        );
        // MovdquRM = K seeds + K x-loads + K y-loads + 1 remainder x + 1 remainder y.
        assert_eq!(
            count_op(&func, X86Opcode::MovdquRM),
            3 * k + 2,
            "K seeds + 2K unrolled loads + 2 remainder loads",
        );
    }

    #[test]
    fn rejects_regarg_non_square_product() {
        // A genuine two-input product `elem * iv` is NOT a self-square: the
        // reg-arg tier packs a single element stream, so it MUST stay scalar.
        let LoopShape { mut func, .. } = build_regarg_sumq_loop(RKnobs {
            cross_product: true,
            ..RKnobs::default()
        });
        assert!(
            !X86Vectorize.run_on_function(&mut func),
            "non-square product must stay scalar"
        );
        assert_eq!(count_op(&func, X86Opcode::Pmuludq), 0);
        assert_eq!(count_op(&func, X86Opcode::Paddq), 0);
    }
}
