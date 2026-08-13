// trust-cg-opt - Un-fuse serial FP-reduction FMADD chains
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Un-fuse `llvm.fmuladd`-derived `FmaddRR` on **runtime-trip latency-bound
//! serial FP reductions**, matching clang's fusion decision.
//!
//! `llvm.fmuladd` is fusion-LICENSED (fused single rounding OR un-fused
//! `fmul`+`fadd`). tcg lowers every one to fused `FmaddRR` (4-cycle latency). On
//! a serial reduction `acc = a*b + acc` carried across the back-edge, that
//! latency is on the critical path; un-fused `fmul`(3cy)+`fadd`(3cy) is shorter.
//! clang un-fuses exactly these — but only when the loop is **latency-bound**:
//!   * a runtime (or otherwise non-small) trip count — a genuine serial loop —
//!     NOT a small compile-time-constant trip, which clang fully unrolls into
//!     throughput ILP and keeps fused (Stanford FloatMM's `rowsize` inner dim,
//!     where un-fusing flips an observable full-precision digit vs clang), and
//!   * few parallel accumulator chains (matmul's many are throughput-bound).
//!
//! The decisive semantic gate is `InstFlags::FMULADD_MAY_UNFUSE`: strict
//! `llvm.fma` never carries it and therefore can never be split. Profitability
//! additionally requires the loop's trip bound to provably trace to a runtime
//! source (a function-argument register or a load) or a sufficiently large
//! constant. Unknown and small-constant bounds stay fused.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::{
    AArch64Opcode, InstFlags, InstId, MachFunction, MachInst, MachOperand, ProvenanceMap, RegClass,
    VReg,
};

use crate::dom::DomTree;
use crate::loops::{LoopAnalysis, NaturalLoop};
use crate::pass_manager::{AnalysisCache, MachinePass};

pub struct UnfuseSerialFma;

impl MachinePass for UnfuseSerialFma {
    fn name(&self) -> &str {
        "unfuse-serial-fma"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let dom = DomTree::compute(func);
        let loops = LoopAnalysis::compute(func, &dom);
        run_on_loops(func, &loops)
    }

    fn run_with_analyses(&mut self, func: &mut MachFunction, analyses: &mut AnalysisCache) -> bool {
        let loops = analyses.loop_analysis(func).clone();
        run_on_loops(func, &loops)
    }

    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        _provenance: &mut ProvenanceMap,
    ) -> bool {
        self.run(func)
    }

    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        analyses: &mut AnalysisCache,
        _provenance: &mut ProvenanceMap,
    ) -> bool {
        self.run_with_analyses(func, analyses)
    }
}

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

/// Whether serial-FMA un-fusing is globally enabled (the `TCG_NO_UNFUSE_SERIAL_FMA`
/// kill switch is NOT set). Shared with vectorizers that make the SAME fusion
/// decision inline for their own ordered drains (see `neon_fpred`).
pub(crate) fn serial_unfuse_enabled() -> bool {
    std::env::var("TCG_NO_UNFUSE_SERIAL_FMA").is_err()
}

/// The minimum provable-constant trip count at which a licensed serial FMADD
/// chain is un-fused (`TCG_UNFUSE_FMA_MIN_CONST_TRIP`, default 1024) — the
/// SINGLE source of truth for this pass AND for vectorizers that mirror its
/// decision inline (see `neon_fpred`'s ordered drain).
pub(crate) fn serial_unfuse_min_const_trip() -> i64 {
    i64::try_from(env_usize("TCG_UNFUSE_FMA_MIN_CONST_TRIP", 1024)).unwrap_or(i64::MAX)
}

fn run_on_loops(func: &mut MachFunction, loops: &LoopAnalysis) -> bool {
    // Default ON (kill switch TCG_NO_UNFUSE_SERIAL_FMA): validated bit-exact
    // across the SingleSource FP suite with ZERO divergences and net-positive
    // geomean; the runtime-bound gate matches clang's const-fuse/runtime-unfuse
    // decision so results stay bit-exact vs clang.
    if !serial_unfuse_enabled() || loops.is_empty() {
        return false;
    }
    let all: Vec<NaturalLoop> = loops.all_loops().cloned().collect();
    let max_chains = env_usize("TCG_UNFUSE_FMA_MAXCHAINS", 2);
    let fdefs = fn_def_map(func);
    let mut changed = false;
    for lp in &all {
        let has_inner = all
            .iter()
            .any(|o| o.header != lp.header && lp.body.contains(&o.header));
        if has_inner {
            continue;
        }
        // Latency-bound ONLY, matching clang's per-loop fusion decision so
        // results stay bit-exact vs clang:
        //   (a) the trip bound provably traces to a RUNTIME value, or
        //   (b) the trip bound is a provably LARGE constant (clang un-fuses
        //       those too — measured: it un-fused 17/18 of fp-convert's
        //       const-trip serial FMADDs — while the observed divergers are
        //       SMALL-const-trip kernels it unrolls-and-fuses: FloatMM's
        //       rowsize=40 inner product, himeno's stencil dims).
        // Unknown bounds stay FUSED — conservative.
        let min_const = serial_unfuse_min_const_trip();
        if !matches!(
            classify_loop_bound(func, lp, &fdefs, min_const),
            BoundClass::Runtime | BoundClass::LargeConst
        ) {
            continue;
        }
        changed |= unfuse_loop(func, lp, max_chains);
    }
    changed
}

/// Whole-function def-site map for the opcodes we trace.
fn fn_def_map(func: &MachFunction) -> HashMap<VReg, InstId> {
    use AArch64Opcode::*;
    let mut map = HashMap::new();
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            if matches!(
                inst.opcode,
                Movz | MovI
                    | MovR
                    | Copy
                    | AddRI
                    | SubRI
                    | Uxtw
                    | Sxtw
                    | LdrRI
                    | LdrRO
                    | FmaddRR
                    | FmovFprFpr
                    | FmulRR
                    | FaddRR
            ) && let Some(dst) = inst.operands.first().and_then(|o| o.as_vreg())
            {
                map.entry(dst).or_insert(inst_id);
            }
        }
    }
    map
}

/// Classify how a value ultimately originates.
#[derive(PartialEq, Clone, Copy)]
enum Origin {
    Const,   // Movz/MovI — compile-time constant bound
    Runtime, // function-argument register (Copy from PReg) or a load
    Unknown,
}

fn origin_of(func: &MachFunction, defs: &HashMap<VReg, InstId>, v: VReg, depth: u32) -> Origin {
    if depth > 64 {
        return Origin::Unknown;
    }
    let Some(&def_id) = defs.get(&v) else {
        return Origin::Unknown;
    };
    let inst = func.inst(def_id);
    use AArch64Opcode::*;
    match inst.opcode {
        Movz | MovI => Origin::Const,
        LdrRI | LdrRO => Origin::Runtime,
        MovR | Copy | Uxtw | Sxtw | AddRI | SubRI => {
            // A Copy whose source is a physical register is a function argument.
            match inst.operands.get(1) {
                Some(MachOperand::PReg(_)) => Origin::Runtime,
                Some(MachOperand::VReg(src)) => origin_of(func, defs, *src, depth + 1),
                _ => Origin::Unknown,
            }
        }
        _ => Origin::Unknown,
    }
}

/// Classification of the loop's trip-controlling bound.
#[derive(PartialEq, Clone, Copy)]
enum BoundClass {
    /// Provably a runtime value (arg / load) — clang un-fuses: un-fuse.
    Runtime,
    /// Provably a constant >= the large threshold — clang un-fuses: un-fuse.
    LargeConst,
    /// Small constant or unknown — keep fused (conservative).
    KeepFused,
}

/// Classify the loop's trip bound. The trip compare is a `CmpRR` in the header
/// or latch comparing a loop-defined value (the IV) against a loop-invariant
/// bound. For a Const bound, the value is read from its defining `Movz`/`MovI`
/// immediate; a possible later `Movk` only ADDS high bits (for shifts >= 16),
/// so `movz_imm >= min_const` is a monotone-safe LOWER bound on the true value
/// (a Movz #0 + Movk large constant reads as small and stays fused —
/// conservative, never unsound).
fn classify_loop_bound(
    func: &MachFunction,
    lp: &NaturalLoop,
    fdefs: &HashMap<VReg, InstId>,
    min_const: i64,
) -> BoundClass {
    let loop_defs: HashSet<VReg> = {
        let mut s = HashSet::new();
        for &b in &func.block_order {
            if !lp.body.contains(&b) {
                continue;
            }
            for &i in &func.block(b).insts {
                if let Some(d) = func.inst(i).operands.first().and_then(|o| o.as_vreg()) {
                    s.insert(d);
                }
            }
        }
        s
    };

    for &block in &[lp.header, lp.latch] {
        for &inst_id in &func.block(block).insts {
            let inst = func.inst(inst_id);
            if inst.opcode != AArch64Opcode::CmpRR {
                continue;
            }
            let (Some(x), Some(y)) = (
                inst.operands.first().and_then(|o| o.as_vreg()),
                inst.operands.get(1).and_then(|o| o.as_vreg()),
            ) else {
                continue;
            };
            // Trip compare: one operand IV-derived (loop-defined), the other the
            // loop-invariant bound.
            let bound = if loop_defs.contains(&x) && !loop_defs.contains(&y) {
                y
            } else if loop_defs.contains(&y) && !loop_defs.contains(&x) {
                x
            } else {
                continue;
            };
            match origin_of(func, fdefs, bound, 0) {
                Origin::Runtime => return BoundClass::Runtime,
                Origin::Const => {
                    // Read the constant's value from its defining move.
                    if let Some(v) = const_lower_bound(func, fdefs, bound, 0)
                        && v >= min_const
                    {
                        return BoundClass::LargeConst;
                    }
                    return BoundClass::KeepFused; // small/unreadable const trip
                }
                Origin::Unknown => continue,
            }
        }
    }
    BoundClass::KeepFused // conservative: no provable bound found
}

/// Lower bound on the constant value of `v`: trace copies to the defining
/// `Movz`/`MovI`, apply the exact `Uxtw`/`Sxtw` width conversion, and adjust
/// `AddRI`/`SubRI` with checked arithmetic.
fn const_lower_bound(
    func: &MachFunction,
    defs: &HashMap<VReg, InstId>,
    v: VReg,
    depth: u32,
) -> Option<i64> {
    if depth > 64 {
        return None;
    }
    let &def_id = defs.get(&v)?;
    let inst = func.inst(def_id);
    use AArch64Opcode::*;
    match inst.opcode {
        Movz => {
            let (dst, value) = crate::reaching_const::movz_value(inst)?;
            if dst != v {
                return None;
            }
            i64::try_from(value).ok()
        }
        MovI if inst.operands.len() == 2 => inst.operands.get(1)?.as_imm(),
        MovR | Copy => const_lower_bound(func, defs, inst.operands.get(1)?.as_vreg()?, depth + 1),
        Uxtw => Some(
            const_lower_bound(func, defs, inst.operands.get(1)?.as_vreg()?, depth + 1)? as u32
                as i64,
        ),
        Sxtw => Some(
            const_lower_bound(func, defs, inst.operands.get(1)?.as_vreg()?, depth + 1)? as i32
                as i64,
        ),
        AddRI => Some(
            const_lower_bound(func, defs, inst.operands.get(1)?.as_vreg()?, depth + 1)?
                .checked_add(inst.operands.get(2)?.as_imm()?)?,
        ),
        SubRI => Some(
            const_lower_bound(func, defs, inst.operands.get(1)?.as_vreg()?, depth + 1)?
                .checked_sub(inst.operands.get(2)?.as_imm()?)?,
        ),
        _ => None,
    }
}

fn body_def_map(func: &MachFunction, lp: &NaturalLoop) -> HashMap<VReg, InstId> {
    use AArch64Opcode::*;
    let mut map = HashMap::new();
    for &block_id in &func.block_order {
        if !lp.body.contains(&block_id) {
            continue;
        }
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            if matches!(inst.opcode, FmaddRR | FmovFprFpr | MovR | Copy)
                && let Some(dst) = inst.operands.first().and_then(|o| o.as_vreg())
            {
                map.entry(dst).or_insert(inst_id);
            }
        }
    }
    map
}

fn unfuse_loop(func: &mut MachFunction, lp: &NaturalLoop, max_chains: usize) -> bool {
    let defs = body_def_map(func, lp);
    let mut chains: Vec<Vec<InstId>> = Vec::new();
    for &inst_id in &func.block(lp.latch).insts {
        let inst = func.inst(inst_id);
        if !matches!(
            inst.opcode,
            AArch64Opcode::FmovFprFpr | AArch64Opcode::MovR | AArch64Opcode::Copy
        ) {
            continue;
        }
        let acc = match inst.operands.first().and_then(|o| o.as_vreg()) {
            Some(v) if matches!(v.class, RegClass::Fpr32 | RegClass::Fpr64) => v,
            _ => continue,
        };
        let src = match inst.operands.get(1).and_then(|o| o.as_vreg()) {
            Some(v) => v,
            None => continue,
        };
        if let Some(chain) = trace_fmadd_chain(func, &defs, acc, src)
            && !chain.is_empty()
        {
            chains.push(chain);
        }
    }

    // Second serial-accumulator form: IN-PLACE runs — `FmaddRR [acc, a, b, acc]`
    // (dst == addend) redefining one FP accumulator repeatedly within the loop
    // body, with no latch writeback copy. This is what the NEON vectorizers'
    // ORDERED-DRAIN emits (vector loads/converts, then a serial scalar FMADD
    // drain to preserve FP order — e.g. fp-convert's vectorized sum loop) and
    // it is exactly as latency-bound as the copy-based form. Group by
    // accumulator vreg; each distinct accumulator is one chain.
    let mut inplace: HashMap<VReg, Vec<InstId>> = HashMap::new();
    for &block_id in &func.block_order {
        if !lp.body.contains(&block_id) {
            continue;
        }
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            if inst.opcode == AArch64Opcode::FmaddRR
                && inst.flags.contains(InstFlags::FMULADD_MAY_UNFUSE)
                && inst.operands.len() >= 4
                && let (Some(d), Some(c)) = (inst.operands[0].as_vreg(), inst.operands[3].as_vreg())
                && d == c
                && matches!(d.class, RegClass::Fpr32 | RegClass::Fpr64)
            {
                inplace.entry(d).or_default().push(inst_id);
            }
        }
    }
    for (_acc, group) in inplace {
        chains.push(group);
    }

    if chains.is_empty() || chains.len() > max_chains {
        return false;
    }
    let to_unfuse: HashSet<InstId> = chains.iter().flatten().copied().collect();
    if to_unfuse.is_empty() {
        return false;
    }
    if std::env::var("TCG_UNFUSE_FMA_TRACE").is_ok() {
        eprintln!(
            "[unfuse-fma] {} header={:?}: {} chain(s), {} FMADD(s)",
            func.name,
            lp.header,
            chains.len(),
            to_unfuse.len()
        );
    }
    for &fmadd_id in &to_unfuse {
        split_fmadd(func, lp, fmadd_id);
    }
    true
}

fn trace_fmadd_chain(
    func: &MachFunction,
    defs: &HashMap<VReg, InstId>,
    acc: VReg,
    start: VReg,
) -> Option<Vec<InstId>> {
    let mut chain = Vec::new();
    let mut cur = start;
    for _ in 0..256 {
        if cur == acc {
            return Some(chain);
        }
        let def_id = *defs.get(&cur)?;
        let inst = func.inst(def_id);
        match inst.opcode {
            AArch64Opcode::FmaddRR => {
                if !inst.flags.contains(InstFlags::FMULADD_MAY_UNFUSE) {
                    return None;
                }
                let c = inst.operands.get(3).and_then(|o| o.as_vreg())?;
                chain.push(def_id);
                cur = c;
            }
            AArch64Opcode::FmovFprFpr | AArch64Opcode::MovR | AArch64Opcode::Copy => {
                cur = inst.operands.get(1).and_then(|o| o.as_vreg())?;
            }
            _ => return None,
        }
    }
    None
}

fn split_fmadd(func: &mut MachFunction, lp: &NaturalLoop, fmadd_id: InstId) {
    let (dst, a, b, c, source_loc) = {
        let inst = func.inst(fmadd_id);
        let g = |i: usize| inst.operands.get(i).and_then(|o| o.as_vreg());
        match (g(0), g(1), g(2), g(3)) {
            (Some(d), Some(a), Some(b), Some(c)) => (d, a, b, c, inst.source_loc),
            _ => return,
        }
    };
    let tmp = VReg::new(func.alloc_vreg(), dst.class);
    let mut fmul = MachInst::new(
        AArch64Opcode::FmulRR,
        vec![
            MachOperand::VReg(tmp),
            MachOperand::VReg(a),
            MachOperand::VReg(b),
        ],
    );
    fmul.source_loc = source_loc;
    let fmul_id = func.push_inst(fmul);
    {
        let inst = func.inst_mut(fmadd_id);
        inst.opcode = AArch64Opcode::FaddRR;
        inst.flags.remove(InstFlags::FMULADD_MAY_UNFUSE);
        inst.operands = vec![
            MachOperand::VReg(dst),
            MachOperand::VReg(tmp),
            MachOperand::VReg(c),
        ];
    }
    for &block_id in &lp.body {
        let insts = &func.block(block_id).insts;
        if let Some(pos) = insts.iter().position(|&i| i == fmadd_id) {
            func.block_mut(block_id).insts.insert(pos, fmul_id);
            return;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{BlockId, Signature};

    #[derive(Clone, Copy)]
    enum TestBound {
        Runtime,
        Constant(i64),
        Unknown,
        Uxtw(i64),
        Sxtw(i64),
    }

    fn g(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr64)
    }

    fn g32(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr32)
    }

    fn f(id: u32) -> VReg {
        VReg::new(id, RegClass::Fpr64)
    }

    fn push(
        func: &mut MachFunction,
        block: BlockId,
        opcode: AArch64Opcode,
        operands: Vec<MachOperand>,
    ) -> InstId {
        let id = func.push_inst(MachInst::new(opcode, operands));
        func.append_inst(block, id);
        id
    }

    /// Build a two-block natural loop with an in-place serial FMADD in its
    /// header and a `CmpRR` trip test in its latch. The shape directly exercises
    /// the ordered-drain form consumed by `UnfuseSerialFma`.
    fn build_inplace_loop(bound_kind: TestBound, licensed: bool) -> (MachFunction, InstId) {
        let mut func = MachFunction::new("serial_fma".into(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let header = func.create_block();
        let latch = func.create_block();
        let exit = func.create_block();

        let iv = g(1);
        let bound = g(2);
        let iv_next = g(4);
        push(
            &mut func,
            entry,
            AArch64Opcode::MovI,
            vec![MachOperand::VReg(iv), MachOperand::Imm(0)],
        );
        match bound_kind {
            TestBound::Runtime => {
                push(
                    &mut func,
                    entry,
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::VReg(bound),
                        MachOperand::VReg(g(90)),
                        MachOperand::Imm(0),
                    ],
                );
            }
            TestBound::Constant(value) => {
                push(
                    &mut func,
                    entry,
                    AArch64Opcode::MovI,
                    vec![MachOperand::VReg(bound), MachOperand::Imm(value)],
                );
            }
            TestBound::Unknown => {}
            TestBound::Uxtw(value) | TestBound::Sxtw(value) => {
                let raw = g32(3);
                push(
                    &mut func,
                    entry,
                    AArch64Opcode::MovI,
                    vec![MachOperand::VReg(raw), MachOperand::Imm(value)],
                );
                let opcode = if matches!(bound_kind, TestBound::Uxtw(_)) {
                    AArch64Opcode::Uxtw
                } else {
                    AArch64Opcode::Sxtw
                };
                push(
                    &mut func,
                    entry,
                    opcode,
                    vec![MachOperand::VReg(bound), MachOperand::VReg(raw)],
                );
            }
        }
        push(
            &mut func,
            entry,
            AArch64Opcode::B,
            vec![MachOperand::Block(header)],
        );

        let mut fmadd = MachInst::new(
            AArch64Opcode::FmaddRR,
            vec![
                MachOperand::VReg(f(10)),
                MachOperand::VReg(f(11)),
                MachOperand::VReg(f(12)),
                MachOperand::VReg(f(10)),
            ],
        );
        if licensed {
            fmadd.flags.insert(InstFlags::FMULADD_MAY_UNFUSE);
        }
        let fmadd_id = func.push_inst(fmadd);
        func.append_inst(header, fmadd_id);
        push(
            &mut func,
            header,
            AArch64Opcode::B,
            vec![MachOperand::Block(latch)],
        );

        push(
            &mut func,
            latch,
            AArch64Opcode::AddRI,
            vec![
                MachOperand::VReg(iv_next),
                MachOperand::VReg(iv),
                MachOperand::Imm(1),
            ],
        );
        push(
            &mut func,
            latch,
            AArch64Opcode::CmpRR,
            vec![MachOperand::VReg(iv_next), MachOperand::VReg(bound)],
        );
        push(
            &mut func,
            latch,
            AArch64Opcode::BCond,
            vec![MachOperand::Imm(11), MachOperand::Block(header)],
        );
        push(
            &mut func,
            latch,
            AArch64Opcode::B,
            vec![MachOperand::Block(exit)],
        );
        push(&mut func, exit, AArch64Opcode::Ret, vec![]);

        func.add_edge(entry, header);
        func.add_edge(header, latch);
        func.add_edge(latch, header);
        func.add_edge(latch, exit);
        func.next_vreg = 100;
        (func, fmadd_id)
    }

    fn linked_opcode_count(func: &MachFunction, opcode: AArch64Opcode) -> usize {
        func.block_order
            .iter()
            .flat_map(|&block| func.block(block).insts.iter().copied())
            .filter(|&id| func.inst(id).opcode == opcode)
            .count()
    }

    /// Convert the in-place accumulator into the other supported serial form:
    /// an FMADD result copied back to the accumulator in the latch.
    fn build_copy_carried_loop(licensed: bool) -> (MachFunction, InstId) {
        let (mut func, fmadd_id) = build_inplace_loop(TestBound::Runtime, licensed);
        func.inst_mut(fmadd_id).operands[0] = MachOperand::VReg(f(13));
        let writeback = func.push_inst(MachInst::new(
            AArch64Opcode::FmovFprFpr,
            vec![MachOperand::VReg(f(10)), MachOperand::VReg(f(13))],
        ));
        // `build_inplace_loop` creates entry/header/latch/exit in that order.
        func.block_mut(BlockId(2)).insts.insert(0, writeback);
        (func, fmadd_id)
    }

    fn classify_test_bound(bound: TestBound) -> BoundClass {
        let (func, _) = build_inplace_loop(bound, true);
        let dom = DomTree::compute(&func);
        let loops = LoopAnalysis::compute(&func, &dom);
        let natural_loop = loops.all_loops().next().expect("natural loop");
        classify_loop_bound(&func, natural_loop, &fn_def_map(&func), 1024)
    }

    #[test]
    fn licensed_runtime_inplace_fmuladd_is_split_and_consumes_license() {
        let (mut func, fmadd_id) = build_inplace_loop(TestBound::Runtime, true);
        let mut pass = UnfuseSerialFma;
        assert!(pass.run(&mut func));
        assert_eq!(linked_opcode_count(&func, AArch64Opcode::FmaddRR), 0);
        assert_eq!(linked_opcode_count(&func, AArch64Opcode::FmulRR), 1);
        assert_eq!(linked_opcode_count(&func, AArch64Opcode::FaddRR), 1);
        assert_eq!(func.inst(fmadd_id).opcode, AArch64Opcode::FaddRR);
        assert!(
            !func
                .inst(fmadd_id)
                .flags
                .contains(InstFlags::FMULADD_MAY_UNFUSE),
            "the source-only contract must not survive an opcode rewrite"
        );
    }

    #[test]
    fn strict_runtime_fma_stays_fused() {
        let (mut func, fmadd_id) = build_inplace_loop(TestBound::Runtime, false);
        let mut pass = UnfuseSerialFma;
        assert!(!pass.run(&mut func));
        assert_eq!(linked_opcode_count(&func, AArch64Opcode::FmaddRR), 1);
        assert_eq!(linked_opcode_count(&func, AArch64Opcode::FmulRR), 0);
        assert_eq!(func.inst(fmadd_id).opcode, AArch64Opcode::FmaddRR);
    }

    #[test]
    fn copy_carried_chain_also_requires_the_source_license() {
        for licensed in [false, true] {
            let (mut func, fmadd_id) = build_copy_carried_loop(licensed);
            let mut pass = UnfuseSerialFma;
            assert_eq!(pass.run(&mut func), licensed);
            assert_eq!(
                func.inst(fmadd_id).opcode,
                if licensed {
                    AArch64Opcode::FaddRR
                } else {
                    AArch64Opcode::FmaddRR
                }
            );
            assert_eq!(
                linked_opcode_count(&func, AArch64Opcode::FmulRR),
                licensed as usize
            );
        }
    }

    #[test]
    fn loop_bound_classification_is_exact_and_conservative() {
        assert!(matches!(
            classify_test_bound(TestBound::Runtime),
            BoundClass::Runtime
        ));
        assert!(matches!(
            classify_test_bound(TestBound::Constant(1024)),
            BoundClass::LargeConst
        ));
        assert!(matches!(
            classify_test_bound(TestBound::Constant(1023)),
            BoundClass::KeepFused
        ));
        assert!(matches!(
            classify_test_bound(TestBound::Unknown),
            BoundClass::KeepFused
        ));
        assert!(matches!(
            classify_test_bound(TestBound::Uxtw(0x1_0000_03ff)),
            BoundClass::KeepFused
        ));
        assert!(matches!(
            classify_test_bound(TestBound::Sxtw(0xffff_ffff)),
            BoundClass::KeepFused
        ));
    }

    #[test]
    fn fused_and_unfused_rounding_have_an_observable_witness() {
        let a = f64::from_bits(0x3ff0_0000_0000_0001);
        let rounded_product = a * a;
        let c = -rounded_product;
        let fused = a.mul_add(a, c);
        let unfused = rounded_product + c;

        assert_eq!(fused.to_bits(), 0x3970_0000_0000_0000);
        assert_eq!(unfused.to_bits(), 0);
        assert_ne!(fused.to_bits(), unfused.to_bits());
    }
}
