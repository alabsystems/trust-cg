// trust-cg-opt - Merge same-argument sin/cos libcalls into one __sincos_stret
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Fuse a same-argument `sin(x)` + `cos(x)` libcall pair into ONE Darwin
//! `___sincos_stret` call, matching clang -O3.
//!
//! On Apple arm64, clang lowers `sin(x)` and `cos(x)` with the **same** argument
//! into a single `___sincos_stret` call whose ABI returns `sin` in `d0` and
//! `cos` in `d1`, paying libm's expensive argument reduction ONCE. tcg's importer
//! lowers `llvm.sin.f64`/`llvm.cos.f64` to two independent `Bl sin` / `Bl cos`
//! calls, reducing the argument twice. This pass recognizes the pristine
//! post-ISel shape
//!
//! ```text
//!   Copy [d0, arg]          ; call-arg setup
//!   Bl   [Symbol("cos")]    ; (or "sin")
//!   Copy [cos_res, d0]      ; result read
//!   ... non-call, non-arg-clobbering instructions ...
//!   Copy [d0, arg]          ; SAME arg vreg
//!   Bl   [Symbol("sin")]    ; (or "cos")
//!   Copy [sin_res, d0]
//! ```
//!
//! and rewrites the earlier `Bl` to `Bl [Symbol("__sincos_stret")]` (the object
//! emitter prepends one `_`, yielding the Darwin symbol `___sincos_stret`),
//! feeding `sin_res <- d0` and `cos_res <- d1` from that single call and deleting
//! the second call's arg-setup / `Bl` / result-read.
//!
//! ## Soundness
//! * **Darwin only.** `___sincos_stret` and its `{d0=sin, d1=cos}` return ABI are
//!   Apple-specific; the ELF `sincos` has an incompatible pointer-out-parameter
//!   ABI. The pass is inert unless the caller confirms a Mach-O/Darwin target.
//! * **f64 only.** `sinf`/`cosf` would need `___sincosf_stret` with a distinct
//!   `{s0,s1}` return ABI; conservatively skipped.
//! * The merged call reuses the original `Bl`'s call-clobber `implicit_defs`
//!   (which already contain `v0`/`v1`, aliasing `d0`/`d1`) and its `d0`
//!   `implicit_uses`, so register allocation and the translation validator see it
//!   exactly like the existing single-result sin/cos calls (whose `d0` result is
//!   already read out of an aliasing `v0` def today).
//! * Runs PRE-scheduler: the scheduler legally reorders across the two calls, so
//!   the same-argument pair is only guaranteed adjacent before it runs.
//! * Fail-closed: any deviation from the exact expected shape skips the pair.
//!
//! Kill switches: `TCG_NO_SINCOS_MERGE`, `TRUST_CG_DISABLE_PASSES=sincosmerge`.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::regs::{D0, D1};
use trust_cg_ir::{AArch64Opcode, InstId, MachFunction, MachInst, MachOperand, PReg, VReg};

use crate::pass_manager::MachinePass;

/// The Darwin combined sin/cos entry point, WITHOUT the object emitter's leading
/// `_` (it prepends one, matching the "sin"/"cos" symbols the importer emits, to
/// yield the final `___sincos_stret`).
const SINCOS_STRET_SYMBOL: &str = "__sincos_stret";

pub struct SincosMerge {
    /// True only when the object target is Darwin/Mach-O arm64. Fail-closed:
    /// when false the pass is a no-op (see module docs — the stret ABI is
    /// Apple-specific).
    darwin: bool,
}

impl SincosMerge {
    pub fn new(darwin: bool) -> Self {
        Self { darwin }
    }
}

impl MachinePass for SincosMerge {
    fn name(&self) -> &str {
        "sincos-merge"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        if !self.darwin || std::env::var("TCG_NO_SINCOS_MERGE").is_ok() {
            return false;
        }
        run_pass(func)
    }
}

/// One recognized `sin`/`cos` call site with its pristine surrounding shape.
#[derive(Clone, Copy)]
struct CallSite {
    is_sin: bool,
    /// Index of the `Bl` within `block.insts`.
    bl_index: usize,
    bl_id: InstId,
    /// Index of the arg-setup `Copy [d0, arg]` (immediately precedes the `Bl`).
    arg_setup_index: usize,
    arg_setup_id: InstId,
    arg_vreg: VReg,
    /// The result-read `Copy [res, d0]` (immediately follows the `Bl`).
    res_copy_id: InstId,
    res_vreg: VReg,
}

fn run_pass(func: &mut MachFunction) -> bool {
    let trace = std::env::var("TCG_SINCOS_TRACE").is_ok();
    let mut changed = false;
    for bi in 0..func.block_order.len() {
        let block_id = func.block_order[bi];
        changed |= merge_in_block(func, block_id, trace);
    }
    changed
}

/// Recognize an arg-setup `Copy [d0, VReg]` at `idx` (the def of `d0` feeding a
/// call). Returns the source arg vreg.
fn arg_setup_vreg(func: &MachFunction, inst_id: InstId) -> Option<VReg> {
    let inst = func.inst(inst_id);
    if inst.opcode != AArch64Opcode::Copy {
        return None;
    }
    let dst = inst.operands.first()?.as_preg()?;
    if dst != D0 {
        return None;
    }
    inst.operands.get(1)?.as_vreg()
}

/// Recognize a result-read `Copy [VReg, d0]`. Returns the destination result
/// vreg.
fn result_read_vreg(func: &MachFunction, inst_id: InstId) -> Option<VReg> {
    let inst = func.inst(inst_id);
    if inst.opcode != AArch64Opcode::Copy {
        return None;
    }
    let src = inst.operands.get(1)?.as_preg()?;
    if src != D0 {
        return None;
    }
    inst.operands.first()?.as_vreg()
}

/// Collect the well-formed `sin`/`cos` call sites in a block. A site qualifies
/// only if it has the exact pristine shape: an immediately-preceding
/// `Copy [d0, arg]` arg-setup and an immediately-following `Copy [res, d0]`
/// result-read. Anything else is skipped (fail-closed).
fn collect_sites(func: &MachFunction, block_id: trust_cg_ir::BlockId) -> Vec<CallSite> {
    let insts = &func.block(block_id).insts;
    let mut sites = Vec::new();
    for (idx, &inst_id) in insts.iter().enumerate() {
        let inst = func.inst(inst_id);
        if inst.opcode != AArch64Opcode::Bl {
            continue;
        }
        let is_sin = match inst.operands.first().and_then(|o| o.as_symbol()) {
            Some("sin") => true,
            Some("cos") => false,
            _ => continue,
        };
        // The call must take its single f64 argument in d0 and nothing else in
        // an FP register (a plain scalar sin/cos). Anything richer -> skip.
        if idx == 0 || idx + 1 >= insts.len() {
            continue;
        }
        let arg_setup_index = idx - 1;
        let arg_setup_id = insts[arg_setup_index];
        let res_copy_id = insts[idx + 1];
        let (Some(arg_vreg), Some(res_vreg)) = (
            arg_setup_vreg(func, arg_setup_id),
            result_read_vreg(func, res_copy_id),
        ) else {
            continue;
        };
        sites.push(CallSite {
            is_sin,
            bl_index: idx,
            bl_id: inst_id,
            arg_setup_index,
            arg_setup_id,
            arg_vreg,
            res_copy_id,
            res_vreg,
        });
    }
    sites
}

/// True if any instruction in `insts[lo..=hi]` writes (defines) `vreg` in
/// operand-0 position. Used to prove the shared argument is not recomputed
/// between the two arg-setups.
fn arg_redefined_between(
    func: &MachFunction,
    insts: &[InstId],
    lo: usize,
    hi: usize,
    vreg: VReg,
) -> bool {
    for &inst_id in &insts[lo..=hi] {
        if let Some(def) = func
            .inst(inst_id)
            .operands
            .first()
            .and_then(|o| o.as_vreg())
            && def == vreg
        {
            return true;
        }
    }
    false
}

/// True if any `Bl` other than the pair endpoints appears strictly between the
/// two calls. A third call there would clobber d0/d1 — conservatively bail.
fn intervening_call(
    func: &MachFunction,
    insts: &[InstId],
    a_bl_index: usize,
    b_bl_index: usize,
) -> bool {
    for &inst_id in &insts[a_bl_index + 1..b_bl_index] {
        if func.inst(inst_id).is_call() {
            return true;
        }
    }
    false
}

fn merge_in_block(func: &mut MachFunction, block_id: trust_cg_ir::BlockId, trace: bool) -> bool {
    let sites = collect_sites(func, block_id);
    if sites.len() < 2 {
        return false;
    }

    // Group sites by argument vreg; a mergeable group is EXACTLY one sin + one
    // cos on the same argument. (Any other multiplicity is ambiguous -> skip.)
    let mut by_arg: HashMap<VReg, Vec<CallSite>> = HashMap::new();
    for s in &sites {
        by_arg.entry(s.arg_vreg).or_default().push(*s);
    }

    // Collect the mergeable (sin, cos) pairs and process them in deterministic
    // block order (by the earlier call's index). HashMap iteration order is
    // nondeterministic; sorting here keeps the InstIds we allocate below — and
    // therefore the whole compile — reproducible.
    let mut pairs: Vec<(CallSite, CallSite)> = by_arg
        .into_values()
        .filter(|g| g.len() == 2)
        .filter_map(|g| match (g[0].is_sin, g[1].is_sin) {
            (true, false) => Some((g[0], g[1])), // (sin, cos)
            (false, true) => Some((g[1], g[0])),
            _ => None, // two sins or two cos -> ambiguous, skip
        })
        .collect();
    pairs.sort_by_key(|(s, c)| s.bl_index.min(c.bl_index));

    // Plan all merges against the ORIGINAL instruction order, then apply once so
    // index bookkeeping stays valid across multiple pairs in one block.
    let insts_snapshot = func.block(block_id).insts.clone();
    let mut removals: HashSet<InstId> = HashSet::new();
    let mut retarget: Vec<InstId> = Vec::new();
    // anchor bl_id -> (sin_res, cos_res) to materialize d0/d1 reads after it.
    let mut inserts: Vec<(InstId, VReg, VReg)> = Vec::new();

    for (sin_site, cos_site) in pairs {
        // callA is the earlier call (kept, retargeted); callB the later (deleted).
        let (a, b) = if sin_site.bl_index < cos_site.bl_index {
            (sin_site, cos_site)
        } else {
            (cos_site, sin_site)
        };

        // Guard: no third call between them (would clobber d0/d1).
        if intervening_call(func, &insts_snapshot, a.bl_index, b.bl_index) {
            continue;
        }
        // Guard: the shared arg vreg must hold the same value at both setups,
        // i.e. it must not be redefined between the two arg-setups. (In SSA this
        // is automatic; checked explicitly to stay sound if SSA is ever relaxed.)
        if arg_redefined_between(
            func,
            &insts_snapshot,
            a.arg_setup_index,
            b.arg_setup_index,
            a.arg_vreg,
        ) {
            continue;
        }
        // Guard: don't touch an instruction already claimed by another pair
        // (defensive; disjoint by construction since each site has one arg vreg).
        let touched = [a.res_copy_id, b.arg_setup_id, b.bl_id, b.res_copy_id];
        if touched.iter().any(|id| removals.contains(id)) || retarget.contains(&a.bl_id) {
            continue;
        }

        if trace {
            eprintln!(
                "[sincos-merge] {} block {:?}: fuse sin(res={:?}) + cos(res={:?}) on arg {:?}; keep {:?} -> __sincos_stret, drop {:?}",
                func.name,
                block_id,
                sin_site.res_vreg,
                cos_site.res_vreg,
                a.arg_vreg,
                a.bl_id,
                b.bl_id
            );
        }

        // callA keeps its arg-setup + Bl; delete callA's own result-read and the
        // whole of callB. Fresh reads give sin<-d0, cos<-d1 from the merged call.
        removals.insert(a.res_copy_id);
        removals.insert(b.arg_setup_id);
        removals.insert(b.bl_id);
        removals.insert(b.res_copy_id);
        retarget.push(a.bl_id);
        inserts.push((a.bl_id, sin_site.res_vreg, cos_site.res_vreg));
    }

    if retarget.is_empty() {
        return false;
    }

    // Retarget each kept call to the combined entry point.
    for bl_id in &retarget {
        let inst = func.inst_mut(*bl_id);
        inst.operands[0] = MachOperand::Symbol(SINCOS_STRET_SYMBOL.to_string());
    }

    // Materialize the d0(sin)/d1(cos) result reads and remember their ids per
    // anchor so we can splice them in immediately after the retargeted call.
    let mut after: HashMap<InstId, [InstId; 2]> = HashMap::new();
    for (anchor_bl, sin_res, cos_res) in inserts {
        let sin_copy = mk_result_copy(func, sin_res, D0);
        let cos_copy = mk_result_copy(func, cos_res, D1);
        after.insert(anchor_bl, [sin_copy, cos_copy]);
    }

    // Rebuild the block instruction list: drop removed ids, splice the new
    // result copies right after each retargeted call.
    let old = std::mem::take(&mut func.block_mut(block_id).insts);
    let mut new_insts = Vec::with_capacity(old.len());
    for id in old {
        if removals.contains(&id) {
            continue;
        }
        new_insts.push(id);
        if let Some(copies) = after.get(&id) {
            new_insts.push(copies[0]);
            new_insts.push(copies[1]);
        }
    }
    func.block_mut(block_id).insts = new_insts;
    true
}

/// Build a `Copy [res, preg]` result-read (Fpr64 d0/d1), mirroring how ISel
/// reads a scalar FP call result out of its ABI return register.
fn mk_result_copy(func: &mut MachFunction, res: VReg, preg: PReg) -> InstId {
    let inst = MachInst::new(
        AArch64Opcode::Copy,
        vec![MachOperand::VReg(res), MachOperand::PReg(preg)],
    );
    func.push_inst(inst)
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::regs::{V0, V1};
    use trust_cg_ir::{BlockId, RegClass, Signature, Type};

    fn f64_vreg(id: u32) -> VReg {
        VReg::new(id, RegClass::Fpr64)
    }

    /// Call-clobber implicit_defs a real sin/cos `Bl` carries (v0/v1 alias
    /// d0/d1). The pass reuses this set verbatim on the merged call.
    const CALL_DEFS: &[PReg] = &[V0, V1];
    const CALL_USES: &[PReg] = &[D0];

    fn arg_setup(arg: u32) -> MachInst {
        MachInst::new(
            AArch64Opcode::Copy,
            vec![MachOperand::PReg(D0), MachOperand::VReg(f64_vreg(arg))],
        )
    }

    fn bl(sym: &str) -> MachInst {
        MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol(sym.to_string())],
        )
        .with_implicit_uses(CALL_USES)
        .with_implicit_defs(CALL_DEFS)
    }

    fn result_read(res: u32) -> MachInst {
        MachInst::new(
            AArch64Opcode::Copy,
            vec![MachOperand::VReg(f64_vreg(res)), MachOperand::PReg(D0)],
        )
    }

    /// A cheap non-call filler instruction (e.g. an intervening FP multiply).
    fn filler(dst: u32, a: u32, b: u32) -> MachInst {
        MachInst::new(
            AArch64Opcode::FmulRR,
            vec![
                MachOperand::VReg(f64_vreg(dst)),
                MachOperand::VReg(f64_vreg(a)),
                MachOperand::VReg(f64_vreg(b)),
            ],
        )
    }

    fn make_func(insts: Vec<MachInst>) -> MachFunction {
        let mut func = MachFunction::new(
            "test".to_string(),
            Signature::new(vec![Type::F64], vec![Type::F64]),
        );
        let entry = func.entry;
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(entry, id);
        }
        func
    }

    fn block_syms(func: &MachFunction, block: BlockId) -> Vec<String> {
        func.block(block)
            .insts
            .iter()
            .filter_map(|&id| {
                let inst = func.inst(id);
                (inst.opcode == AArch64Opcode::Bl)
                    .then(|| inst.operands[0].as_symbol().unwrap_or("?").to_string())
            })
            .collect()
    }

    /// The two result-reads after a merged call: (sin<-d0, cos<-d1) vregs.
    fn result_read_pregs(func: &MachFunction, block: BlockId) -> Vec<(u32, PReg)> {
        func.block(block)
            .insts
            .iter()
            .filter_map(|&id| {
                let inst = func.inst(id);
                if inst.opcode == AArch64Opcode::Copy
                    && let (Some(dst), Some(src)) = (
                        inst.operands.first().and_then(|o| o.as_vreg()),
                        inst.operands.get(1).and_then(|o| o.as_preg()),
                    )
                    && (src == D0 || src == D1)
                {
                    return Some((dst.id, src));
                }
                None
            })
            .collect()
    }

    /// cos(x) then sin(x) fuses to one __sincos_stret; sin<-d0, cos<-d1.
    #[test]
    fn fuses_cos_then_sin_same_arg() {
        // arg=10; cos result=20; sin result=21.
        let mut func = make_func(vec![
            arg_setup(10),
            bl("cos"),
            result_read(20),
            filler(30, 20, 20), // uses cos result
            arg_setup(10),
            bl("sin"),
            result_read(21),
            filler(31, 21, 30), // uses sin result
        ]);
        let entry = func.entry;
        assert!(run_pass(&mut func));
        assert_eq!(block_syms(&func, entry), vec!["__sincos_stret".to_string()]);
        let reads = result_read_pregs(&func, entry);
        // sin(21) <- d0, cos(20) <- d1
        assert!(
            reads.contains(&(21, D0)),
            "sin result must read d0: {reads:?}"
        );
        assert!(
            reads.contains(&(20, D1)),
            "cos result must read d1: {reads:?}"
        );
    }

    /// sin(x) then cos(x) (reversed order) also fuses, with the same d0/d1 map.
    #[test]
    fn fuses_sin_then_cos_same_arg() {
        let mut func = make_func(vec![
            arg_setup(10),
            bl("sin"),
            result_read(21),
            filler(30, 21, 21),
            arg_setup(10),
            bl("cos"),
            result_read(20),
        ]);
        let entry = func.entry;
        assert!(run_pass(&mut func));
        assert_eq!(block_syms(&func, entry), vec!["__sincos_stret".to_string()]);
        let reads = result_read_pregs(&func, entry);
        assert!(
            reads.contains(&(21, D0)),
            "sin result must read d0: {reads:?}"
        );
        assert!(
            reads.contains(&(20, D1)),
            "cos result must read d1: {reads:?}"
        );
    }

    /// Different arguments must NOT fuse — both calls stay.
    #[test]
    fn different_args_not_fused() {
        let mut func = make_func(vec![
            arg_setup(10),
            bl("cos"),
            result_read(20),
            arg_setup(11),
            bl("sin"),
            result_read(21),
        ]);
        let entry = func.entry;
        assert!(!run_pass(&mut func));
        assert_eq!(
            block_syms(&func, entry),
            vec!["cos".to_string(), "sin".to_string()]
        );
    }

    /// An intervening call clobbers d0/d1 — conservatively skip.
    #[test]
    fn intervening_call_not_fused() {
        let mut func = make_func(vec![
            arg_setup(10),
            bl("cos"),
            result_read(20),
            arg_setup(12),
            bl("exp"), // third call between the pair
            result_read(22),
            arg_setup(10),
            bl("sin"),
            result_read(21),
        ]);
        let entry = func.entry;
        assert!(!run_pass(&mut func));
        assert_eq!(
            block_syms(&func, entry),
            vec!["cos".to_string(), "exp".to_string(), "sin".to_string()]
        );
    }

    /// A lone sin (no matching cos) is left untouched.
    #[test]
    fn standalone_sin_not_fused() {
        let mut func = make_func(vec![arg_setup(10), bl("sin"), result_read(21)]);
        let entry = func.entry;
        assert!(!run_pass(&mut func));
        assert_eq!(block_syms(&func, entry), vec!["sin".to_string()]);
    }

    /// If the shared argument is recomputed between the two arg-setups, the
    /// values differ, so the pair must not fuse.
    #[test]
    fn arg_redefined_between_not_fused() {
        let mut func = make_func(vec![
            arg_setup(10),
            bl("cos"),
            result_read(20),
            // recompute vreg 10 between the setups -> different value for sin
            MachInst::new(
                AArch64Opcode::FaddRR,
                vec![
                    MachOperand::VReg(f64_vreg(10)),
                    MachOperand::VReg(f64_vreg(20)),
                    MachOperand::VReg(f64_vreg(20)),
                ],
            ),
            arg_setup(10),
            bl("sin"),
            result_read(21),
        ]);
        let entry = func.entry;
        assert!(!run_pass(&mut func));
        assert_eq!(
            block_syms(&func, entry),
            vec!["cos".to_string(), "sin".to_string()]
        );
    }

    /// The Darwin gate: with `darwin=false` the pass is a strict no-op.
    #[test]
    fn non_darwin_is_inert() {
        let insts = vec![
            arg_setup(10),
            bl("cos"),
            result_read(20),
            arg_setup(10),
            bl("sin"),
            result_read(21),
        ];
        let mut func = make_func(insts);
        let entry = func.entry;
        let mut pass = SincosMerge::new(false);
        assert!(!pass.run(&mut func));
        assert_eq!(
            block_syms(&func, entry),
            vec!["cos".to_string(), "sin".to_string()]
        );
    }

    /// The merged call keeps the original call-clobber implicit_defs (which
    /// already contain v0/v1 aliasing the d0/d1 results) so regalloc sees it as
    /// a normal two-result call.
    #[test]
    fn merged_call_retains_clobbers() {
        let mut func = make_func(vec![
            arg_setup(10),
            bl("cos"),
            result_read(20),
            arg_setup(10),
            bl("sin"),
            result_read(21),
        ]);
        let entry = func.entry;
        assert!(run_pass(&mut func));
        let bl_id = *func
            .block(entry)
            .insts
            .iter()
            .find(|&&id| func.inst(id).opcode == AArch64Opcode::Bl)
            .unwrap();
        let inst = func.inst(bl_id);
        assert_eq!(inst.operands[0].as_symbol(), Some("__sincos_stret"));
        assert!(inst.implicit_defs.contains(&V0));
        assert!(inst.implicit_defs.contains(&V1));
    }
}
