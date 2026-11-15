// Unit tests for the `neon-fill` array-fill store vectorizer.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use trust_cg_ir::MachInst;
use trust_cg_ir::Signature;

fn x(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn w(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}
fn i(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}
fn bl(b: BlockId) -> MachOperand {
    MachOperand::Block(b)
}
fn count_op(func: &MachFunction, op: AArch64Opcode) -> usize {
    func.blocks
        .iter()
        .flat_map(|blk| blk.insts.iter().copied())
        .filter(|&id| func.inst(id).opcode == op)
        .count()
}

/// How the stored value is produced.
#[derive(Clone, Copy, PartialEq)]
enum Val {
    /// A runtime-invariant register (the `__trustcg_array_fill` helper's `elem`).
    Invariant,
    /// A byte-replicable constant (every element byte equal) -> `MOVI`.
    ConstByte(i64),
    /// A general (non-byte-replicable) constant -> `Movz/Movk + DUP`.
    ConstGeneral(i64),
    /// The stored value is defined INSIDE the loop (must BAIL).
    InLoop,
}

/// The loop bound.
#[derive(Clone, Copy, PartialEq)]
enum BoundK {
    Runtime,
    Const(i64),
}

/// Negative-control mutations of the canonical fill loop.
#[derive(Clone, Copy, PartialEq)]
enum Variant {
    Good,
    /// A load in the body (read+fill) -> BAIL.
    WithLoad,
    /// Store stride != store width (byte store at base+iv*2) -> BAIL.
    WrongStride,
    /// Base defined inside the loop -> BAIL.
    BaseInLoop,
    /// A second store -> BAIL.
    SecondStore,
    /// A call in the body -> BAIL.
    WithCall,
    /// Reversed / non-forward header/latch compare -> BAIL.
    Reversed,
}

struct Cfg {
    elem_size: i64,
    bound: BoundK,
    val: Val,
    variant: Variant,
}

/// Build a ROTATED (do-while) fill loop matching the `__trustcg_array_fill_iN`
/// helper shape:
/// ```text
/// bb0:   setup; B guard
/// guard: cmp iv,bound; b.lt body; (fallthrough) exit      // entry guard
/// body:  addr = base + iv*es; *addr = val; iv1 = iv+1; B latch
/// latch: iv = iv1; cmp iv,bound; b.lt body; (fallthrough) exit
/// exit:  ret
/// ```
/// Register map: v0=base, v2=bound(runtime), v3/w3=value, v8=elem-size const,
/// v10=iv, v11=iv1, v20=addr.
fn build_fill(cfg: Cfg) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let guard = func.create_block();
    let body = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();

    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;
    let es = cfg.elem_size;
    // The transfer register class matches the store width.
    let val_is_x = es == 8;
    let vreg_val = |id: u32| if val_is_x { x(id) } else { w(id) };

    // --- bb0: setup (all loop-invariant, defs dominate the guard).
    push(&mut func, bb0, Copy, vec![x(0), x(0)]); // base (self-copy: invariant def)
    push(&mut func, bb0, Copy, vec![x(2), x(2)]); // runtime bound
    push(&mut func, bb0, Movz, vec![x(8), i(es)]); // elem-size constant
    // The stored value.
    match cfg.val {
        Val::Invariant => {
            // A non-const invariant (models `elem = trunc(value)`).
            push(&mut func, bb0, Uxtb, vec![vreg_val(3), w(1)]);
        }
        Val::ConstByte(k) | Val::ConstGeneral(k) => {
            push(&mut func, bb0, Movz, vec![vreg_val(3), i(k & 0xFFFF)]);
            if k > 0xFFFF {
                push(
                    &mut func,
                    bb0,
                    Movk,
                    vec![vreg_val(3), i((k >> 16) & 0xFFFF), i(16)],
                );
            }
        }
        Val::InLoop => { /* defined in the body below */ }
    }
    push(&mut func, bb0, Movz, vec![x(10), i(0)]); // iv = 0
    push(&mut func, bb0, B, vec![bl(guard)]);

    // --- guard: entry pre-test.
    let bound_rhs = match cfg.bound {
        BoundK::Runtime => x(2),
        BoundK::Const(_) => x(2), // v2 will be Movz'd below for the const case
    };
    if let BoundK::Const(n) = cfg.bound {
        // Materialize the const bound into v2 in bb0 so both compares agree.
        // (Insert right after the base/bound copies — simplest: overwrite via a
        // fresh Movz at block start of guard is not invariant-safe, so define in
        // bb0.) We instead use CmpRI against the immediate directly.
        let _ = n;
    }
    match cfg.bound {
        BoundK::Runtime => {
            push(&mut func, guard, CmpRR, vec![x(10), bound_rhs.clone()]);
        }
        BoundK::Const(n) => {
            push(&mut func, guard, CmpRI, vec![x(10), i(n)]);
        }
    }
    if cfg.variant == Variant::Reversed {
        // Reversed polarity: exit on `iv < bound` (b.lt -> exit), enter on ge.
        push(&mut func, guard, BCond, vec![i(CC_LT), bl(exit)]);
        push(&mut func, guard, B, vec![bl(body)]);
    } else {
        push(&mut func, guard, BCond, vec![i(CC_LT), bl(body)]);
        push(&mut func, guard, B, vec![bl(exit)]);
    }

    // --- body (header): address, store, iv+1.
    let store_stride = if cfg.variant == Variant::WrongStride {
        2
    } else {
        es
    };
    if cfg.variant == Variant::WithLoad {
        // A load in the body -> BAIL (read+fill).
        push(&mut func, body, LdrbRI, vec![w(30), x(0), i(0)]);
    }
    if cfg.variant == Variant::WithCall {
        push(&mut func, body, Bl, vec![i(0)]);
    }
    // addr = base + iv*store_stride.
    if store_stride == 1 && cfg.variant != Variant::WrongStride {
        push(&mut func, body, AddRR, vec![x(20), x(0), x(10)]);
    } else {
        push(&mut func, body, Movz, vec![x(21), i(store_stride)]);
        push(&mut func, body, Madd, vec![x(20), x(10), x(21), x(0)]);
    }
    // The stored value register.
    let val_reg = match cfg.val {
        Val::InLoop => {
            // iv-dependent value defined in the loop.
            push(&mut func, body, AddRI, vec![vreg_val(3), x(10), i(7)]);
            vreg_val(3)
        }
        _ => vreg_val(3),
    };
    // Base defined inside loop -> overwrite v0 in the body (BAIL control).
    if cfg.variant == Variant::BaseInLoop {
        push(&mut func, body, AddRI, vec![x(0), x(0), i(0)]);
    }
    let store_op = match es {
        1 => StrbRI,
        2 => StrhRI,
        _ => StrRI,
    };
    push(
        &mut func,
        body,
        store_op,
        vec![val_reg.clone(), x(20), i(0)],
    );
    if cfg.variant == Variant::SecondStore {
        push(&mut func, body, store_op, vec![val_reg, x(20), i(0)]);
    }
    push(&mut func, body, AddRI, vec![x(11), x(10), i(1)]); // iv1 = iv + 1
    push(&mut func, body, B, vec![bl(latch)]);

    // --- latch: iv = iv1; continue-test.
    push(&mut func, latch, AddRI, vec![x(10), x(11), i(0)]); // iv = copy(iv1)
    match cfg.bound {
        BoundK::Runtime => {
            push(&mut func, latch, CmpRR, vec![x(10), x(2)]);
        }
        BoundK::Const(n) => {
            push(&mut func, latch, CmpRI, vec![x(10), i(n)]);
        }
    }
    if cfg.variant == Variant::Reversed {
        push(&mut func, latch, BCond, vec![i(CC_LT), bl(exit)]);
    } else {
        push(&mut func, latch, BCond, vec![i(CC_LT), bl(body)]);
    }

    // --- exit.
    push(&mut func, exit, Ret, vec![]);

    func.add_edge(bb0, guard);
    func.add_edge(guard, body);
    func.add_edge(guard, exit);
    func.add_edge(body, latch);
    if cfg.variant == Variant::Reversed {
        func.add_edge(latch, exit);
        func.add_edge(latch, body); // keep it a loop so LoopAnalysis sees it
    } else {
        func.add_edge(latch, body);
        func.add_edge(latch, exit);
    }
    func
}

fn run(func: &mut MachFunction) -> (bool, usize) {
    let mut pass = NeonFillPass::new();
    let changed = pass.run(func);
    (changed, pass.fired())
}

// ---------------------------------------------------------------------------
// POSITIVE
// ---------------------------------------------------------------------------

/// The bridge's TOP-TESTED `for i in 0..N { a[i] = v }` shape (v2_memfill's
/// main: header holds the continue test, body stores, latch writes the iv
/// back) — the shape on which the pass re-fired on its own remainder. The
/// rotated `build_fill` shape happens not to re-fire, so it cannot pin the
/// guard; this one does.
/// ```text
/// bb0:    x10 = 0; w3 = val; B header
/// header: cmp x10, N; b.lt body; B exit
/// body:   x20 = x0 + x10; strb w3, [x20]; x11 = x10 + 1; B latch
/// latch:  x10 = x11 + 0; B header
/// exit:   ret
/// ```
fn build_fill_top_tested(n: i64) -> MachFunction {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let body = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();
    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;
    push(&mut func, bb0, Movz, vec![w(3), i(0x5a)]);
    push(&mut func, bb0, Movz, vec![x(10), i(0)]);
    push(&mut func, bb0, B, vec![bl(header)]);
    push(&mut func, header, CmpRI, vec![x(10), i(n)]);
    push(&mut func, header, BCond, vec![i(CC_LT), bl(body)]);
    push(&mut func, header, B, vec![bl(exit)]);
    push(&mut func, body, AddRR, vec![x(20), x(0), x(10)]);
    push(&mut func, body, StrbRI, vec![w(3), x(20), i(0)]);
    push(&mut func, body, AddRI, vec![x(11), x(10), i(1)]);
    push(&mut func, body, B, vec![bl(latch)]);
    push(&mut func, latch, AddRI, vec![x(10), x(11), i(0)]);
    push(&mut func, latch, B, vec![bl(header)]);
    push(&mut func, exit, Ret, vec![]);
    func.add_edge(bb0, header);
    func.add_edge(header, body);
    func.add_edge(header, exit);
    func.add_edge(body, latch);
    func.add_edge(latch, header);
    func
}

/// The pass must be IDEMPOTENT: `apply` keeps the scalar loop as the remainder
/// of the vector loop (same iv, advanced in place), and before the guard in
/// `recognize` that remainder was recognized AGAIN on every fixpoint iteration
/// (v2_memfill: +8 instructions per iteration, never converging). A second
/// run must change nothing.
fn assert_idempotent(mut func: MachFunction, label: &str) {
    let (changed, fired) = run(&mut func);
    assert!(changed && fired == 1, "{label}: first run should vectorize");
    let (insts, blocks) = (func.insts.len(), func.blocks.len());
    for again in 2..=4 {
        let (changed, fired) = run(&mut func);
        assert!(
            !changed && fired == 0,
            "{label}: run {again} re-vectorized the remainder loop"
        );
        assert_eq!(
            func.insts.len(),
            insts,
            "{label}: run {again} added instructions"
        );
        assert_eq!(
            func.blocks.len(),
            blocks,
            "{label}: run {again} added blocks"
        );
    }
}

/// Through the REAL O3 fixpoint (`run_to_fixpoint(.., 4)`, the pipeline the
/// bridge runs): the loop must converge — a non-idempotent vectorizer keeps
/// re-vectorizing its own remainder after cfg-simplify/gvn clean up, so the
/// fixpoint hits the 4-iteration cap and the function GROWS (v2_memfill
/// +8 / p7_sieve +44 instructions per iteration before the guards).
#[test]
fn o3_fixpoint_converges_without_regrowth() {
    use crate::pipeline::{OptLevel, OptimizationPipeline};
    let mut func = build_fill_top_tested(8192);
    let mut pm = OptimizationPipeline::new(OptLevel::O3).build_pass_manager();
    let stats = pm.run_to_fixpoint(&mut func, 4);
    assert!(
        stats.iterations < 4,
        "byte fill: O3 fixpoint hit the iteration cap ({} iterations) — a pass keeps re-firing",
        stats.iterations
    );
    // No nested vector loops: a single vectorized copy of the loop.
    let vector_headers = func
        .blocks
        .iter()
        .flat_map(|b| b.insts.iter())
        .filter(|&&id| matches!(func.inst(id).opcode, AArch64Opcode::NeonMovi))
        .count();
    assert!(
        vector_headers <= 8,
        "byte fill: {vector_headers} NeonMovi — nested vector loops"
    );
}

#[test]
fn second_run_is_a_no_op_runtime_bound() {
    assert_idempotent(
        build_fill(Cfg {
            elem_size: 1,
            bound: BoundK::Runtime,
            val: Val::Invariant,
            variant: Variant::Good,
        }),
        "runtime-bound byte fill",
    );
}

#[test]
fn second_run_is_a_no_op_top_tested() {
    assert_idempotent(
        build_fill_top_tested(8192),
        "top-tested byte fill (v2_memfill shape)",
    );
}

#[test]
fn second_run_is_a_no_op_const_bound() {
    assert_idempotent(
        build_fill(Cfg {
            elem_size: 4,
            bound: BoundK::Const(4096),
            val: Val::Invariant,
            variant: Variant::Good,
        }),
        "const-bound u32 fill",
    );
}

fn candidate_boundary_fixture() -> MachFunction {
    build_fill(Cfg {
        elem_size: 1,
        bound: BoundK::Runtime,
        val: Val::Invariant,
        variant: Variant::Good,
    })
}

fn candidate_boundary_plan(func: &MachFunction) -> Recognized {
    let dom = DomTree::compute(func);
    let loops = LoopAnalysis::compute(func, &dom);
    let def = build_def_map(func);
    let loop_state = LoopStateIndex::literal(func);
    loops
        .all_loops()
        .find_map(|lp| {
            Recognized::recognize(func, &dom, &def, &loop_state, lp.header, lp.latch, &lp.body)
        })
        .expect("unmodified control must be recognized")
}

fn candidate_boundary_refusal(func: &mut MachFunction, rec: &Recognized) {
    let before = format!("{func:?}");
    assert!(!apply(func, rec));
    assert_eq!(
        format!("{func:?}"),
        before,
        "refusal must preserve the whole function"
    );
}

#[test]
fn candidate_boundary_early_exhaustion() {
    let mut func = candidate_boundary_fixture();
    let rec = candidate_boundary_plan(&func);
    // Arm the boundary after immutable recognition; not a frontend repro.
    func.next_vreg = u32::MAX;
    candidate_boundary_refusal(&mut func, &rec);
}

#[test]
fn candidate_boundary_late_exhaustion() {
    let mut func = candidate_boundary_fixture();
    let rec = candidate_boundary_plan(&func);
    // Arm the boundary after immutable recognition; not a frontend repro.
    func.next_vreg = u32::MAX - 1;
    candidate_boundary_refusal(&mut func, &rec);
}

#[test]
fn candidate_boundary_metadata_exhaustion() {
    let mut func = candidate_boundary_fixture();
    let rec = candidate_boundary_plan(&func);
    // Arm the boundary after immutable recognition; not a frontend repro.
    func.noalias_params.push(u32::MAX);
    candidate_boundary_refusal(&mut func, &rec);
}

#[test]
fn candidate_boundary_splice_refusal() {
    let mut func = candidate_boundary_fixture();
    let rec = candidate_boundary_plan(&func);
    // Arm the boundary after immutable recognition; not a frontend repro.
    func.inst_mut(rec.preheader_term).operands.clear();
    candidate_boundary_refusal(&mut func, &rec);
}

#[test]
fn candidate_boundary_missing_setup() {
    let mut func = candidate_boundary_fixture();
    let rec = candidate_boundary_plan(&func);
    // Arm the boundary after immutable recognition; not a frontend repro.
    for block in &mut func.blocks {
        block.insts.retain(|id| *id != rec.preheader_term);
    }
    candidate_boundary_refusal(&mut func, &rec);
}

#[test]
fn candidate_boundary_missing_layout() {
    let mut func = candidate_boundary_fixture();
    let rec = candidate_boundary_plan(&func);
    // Arm the boundary after immutable recognition; not a frontend repro.
    func.block_order.retain(|id| *id != rec.header);
    candidate_boundary_refusal(&mut func, &rec);
}

#[test]
fn candidate_boundary_success_snapshot() {
    let mut func = candidate_boundary_fixture();
    let rec = candidate_boundary_plan(&func);
    assert!(apply(&mut func, &rec));
    println!("CANDIDATE_SNAPSHOT: {func:?}");
}

#[test]
fn candidate_boundary_public_entry_points_preserve_refusal() {
    let mut control = candidate_boundary_fixture();
    assert!(NeonFillPass::new().run(&mut control));
    let mut func = candidate_boundary_fixture();
    func.next_vreg = u32::MAX;
    let before = format!("{func:?}");
    let mut pass = NeonFillPass::new();
    let mut analyses = AnalysisCache::new();
    assert!(!pass.run(&mut func));
    assert!(!pass.run_with_analyses(&mut func, &mut analyses));
    assert_eq!(pass.fired(), 0);
    assert_eq!(format!("{func:?}"), before);
}

#[test]
fn candidate_boundary_sparse_ids_include_detached_and_noalias() {
    let mut func = candidate_boundary_fixture();
    let rec = candidate_boundary_plan(&func);
    let old_ids: HashSet<_> = func
        .insts
        .iter()
        .flat_map(|inst| &inst.operands)
        .filter_map(|op| op.as_vreg().map(|reg| reg.id))
        .collect();
    func.push_inst(MachInst::new(
        AArch64Opcode::MovR,
        vec![MachOperand::VReg(VReg::new(1_000_000_000, RegClass::Gpr64))],
    ));
    func.noalias_params.push(1_000_000_007);
    func.next_vreg = 0;
    let old_len = func.insts.len();
    assert!(apply(&mut func, &rec));
    let fresh: Vec<_> = func.insts[old_len..]
        .iter()
        .flat_map(|inst| &inst.operands)
        .filter_map(|op| op.as_vreg().map(|reg| reg.id))
        .filter(|id| !old_ids.contains(id))
        .collect();
    assert!(!fresh.is_empty());
    assert!(fresh.iter().all(|id| *id > 1_000_000_007));
    assert!(func.next_vreg > 1_000_000_007);
}

#[test]
fn candidate_boundary_last_representable_range_preserves_construction() {
    let original = candidate_boundary_fixture();
    let rec = candidate_boundary_plan(&original);
    let mut ordinary = original.clone();
    ordinary.try_sync_vreg_counter().unwrap();
    let first = ordinary.next_vreg;
    assert!(apply(&mut ordinary, &rec));
    let count = ordinary.next_vreg - first;
    assert!(count > 1);
    let mut boundary = original.clone();
    let boundary_first = u32::MAX - count;
    boundary.next_vreg = boundary_first;
    assert!(apply(&mut boundary, &rec));
    assert_eq!(boundary.next_vreg, u32::MAX);
    for inst in &mut boundary.insts[original.insts.len()..] {
        for operand in &mut inst.operands {
            if let MachOperand::VReg(reg) = operand
                && reg.id >= boundary_first
            {
                reg.id = first + (reg.id - boundary_first);
            }
        }
    }
    boundary.next_vreg = ordinary.next_vreg;
    assert_eq!(format!("{boundary:?}"), format!("{ordinary:?}"));
}

#[test]
fn fires_on_byte_fill_helper_shape() {
    let mut func = build_fill(Cfg {
        elem_size: 1,
        bound: BoundK::Runtime,
        val: Val::Invariant,
        variant: Variant::Good,
    });
    let strb_before = count_op(&func, AArch64Opcode::StrbRI);
    let (changed, fired) = run(&mut func);
    assert!(
        changed && fired == 1,
        "byte fill helper shape should vectorize"
    );
    // One DUP broadcast (element-size code 1 = B).
    assert_eq!(
        count_op(&func, AArch64Opcode::NeonDupGen),
        1,
        "one DUP broadcast"
    );
    assert_eq!(
        count_op(&func, AArch64Opcode::NeonMovi),
        0,
        "invariant value uses DUP not MOVI"
    );
    // STORE_PAIRS_PER_ITER paired stores; qb stored twice per pair (both
    // operands the same broadcast Q).
    assert_eq!(
        count_op(&func, AArch64Opcode::NeonStpQPost),
        super::STORE_PAIRS_PER_ITER as usize,
        "STORE_PAIRS_PER_ITER STP q,q stores per vector iteration"
    );
    let stp = func
        .blocks
        .iter()
        .flat_map(|b| b.insts.iter().copied())
        .find(|&id| func.inst(id).opcode == AArch64Opcode::NeonStpQPost)
        .unwrap();
    let ops = &func.inst(stp).operands;
    assert_eq!(
        ops[0].as_vreg(),
        ops[1].as_vreg(),
        "STP stores the SAME broadcast Q twice"
    );
    assert_eq!(ops[3].as_imm(), Some(32), "post-index is 32 bytes");
    // The scalar store is UNCHANGED (still present).
    assert_eq!(
        count_op(&func, AArch64Opcode::StrbRI),
        strb_before,
        "scalar store untouched"
    );
    // Rotated shape: an unsigned `iv>=bound` exit guard (b.hs) and a `n<W`
    // precheck (b.lt) were emitted.
    let hs = func
        .blocks
        .iter()
        .flat_map(|b| b.insts.iter().copied())
        .filter(|&id| func.inst(id).opcode == AArch64Opcode::BCond)
        .any(|id| func.inst(id).operands[0].as_imm() == Some(CC_HS));
    assert!(hs, "rotated do-while must emit the iv>=bound HS exit guard");
}

#[test]
fn fires_widths_h_s_d() {
    for (es, code) in [(2i64, 2i64), (4, 4), (8, 8)] {
        let mut func = build_fill(Cfg {
            elem_size: es,
            bound: BoundK::Runtime,
            val: Val::Invariant,
            variant: Variant::Good,
        });
        let (changed, fired) = run(&mut func);
        assert!(changed && fired == 1, "width {es} fill should vectorize");
        assert_eq!(count_op(&func, AArch64Opcode::NeonDupGen), 1, "one DUP");
        // The DUP element-size code equals the element size (2/4/8 = H/S/D).
        let dup = func
            .blocks
            .iter()
            .flat_map(|b| b.insts.iter().copied())
            .find(|&id| func.inst(id).opcode == AArch64Opcode::NeonDupGen)
            .unwrap();
        assert_eq!(
            func.inst(dup).operands[2].as_imm(),
            Some(code),
            "DUP element-size code"
        );
        // StpQPost imm is 32 in every case.
        let stp = func
            .blocks
            .iter()
            .flat_map(|b| b.insts.iter().copied())
            .find(|&id| func.inst(id).opcode == AArch64Opcode::NeonStpQPost)
            .unwrap();
        assert_eq!(
            func.inst(stp).operands[3].as_imm(),
            Some(32),
            "STP imm 32 for width {es}"
        );
    }
}

#[test]
fn const_byte_fill_uses_movi() {
    // Inline const byte-fill: a byte-replicable value -> MOVI Vd.16B (no DUP).
    let mut func = build_fill(Cfg {
        elem_size: 1,
        bound: BoundK::Const(1024),
        val: Val::ConstByte(0x41),
        variant: Variant::Good,
    });
    let (changed, fired) = run(&mut func);
    assert!(changed && fired == 1, "const byte fill should vectorize");
    assert_eq!(
        count_op(&func, AArch64Opcode::NeonMovi),
        1,
        "byte-replicable const uses MOVI"
    );
    assert_eq!(
        count_op(&func, AArch64Opcode::NeonDupGen),
        0,
        "no DUP for a MOVI const"
    );
    let movi = func
        .blocks
        .iter()
        .flat_map(|b| b.insts.iter().copied())
        .find(|&id| func.inst(id).opcode == AArch64Opcode::NeonMovi)
        .unwrap();
    assert_eq!(
        func.inst(movi).operands[1].as_imm(),
        Some(0x41),
        "MOVI immediate is the byte"
    );
}

#[test]
fn const_general_u32_uses_movz_dup() {
    // A non-byte-replicable u32 const -> Movz/Movk + NeonDupGen (NOT MOVI).
    let mut func = build_fill(Cfg {
        elem_size: 4,
        bound: BoundK::Const(1024),
        val: Val::ConstGeneral(0x1234_5678),
        variant: Variant::Good,
    });
    let (changed, fired) = run(&mut func);
    assert!(changed && fired == 1, "general const fill should vectorize");
    assert_eq!(
        count_op(&func, AArch64Opcode::NeonMovi),
        0,
        "non-byte-replicable const must NOT use MOVI"
    );
    assert_eq!(
        count_op(&func, AArch64Opcode::NeonDupGen),
        1,
        "general const broadcasts via DUP"
    );
}

#[test]
fn const_byte_replicable_wide_uses_movi() {
    // A u16 const whose two bytes are equal (0x0101) IS byte-replicable -> MOVI.
    let mut func = build_fill(Cfg {
        elem_size: 2,
        bound: BoundK::Const(512),
        val: Val::ConstByte(0x0101),
        variant: Variant::Good,
    });
    let (changed, fired) = run(&mut func);
    assert!(changed && fired == 1);
    assert_eq!(
        count_op(&func, AArch64Opcode::NeonMovi),
        1,
        "0x0101 is byte-replicable -> MOVI"
    );
    assert_eq!(count_op(&func, AArch64Opcode::NeonDupGen), 0);
}

// ---------------------------------------------------------------------------
// KEEP (fail-safe negative controls)
// ---------------------------------------------------------------------------

fn assert_bails(cfg: Cfg, why: &str) {
    let mut func = build_fill(cfg);
    let (changed, fired) = run(&mut func);
    assert!(!changed && fired == 0, "must BAIL: {why}");
    assert_eq!(
        count_op(&func, AArch64Opcode::NeonStpQPost),
        0,
        "no NEON store emitted: {why}"
    );
}

#[test]
fn bails_on_load() {
    assert_bails(
        Cfg {
            elem_size: 1,
            bound: BoundK::Runtime,
            val: Val::Invariant,
            variant: Variant::WithLoad,
        },
        "a load in the body (read+fill)",
    );
}

#[test]
fn bails_on_wrong_stride() {
    assert_bails(
        Cfg {
            elem_size: 1,
            bound: BoundK::Runtime,
            val: Val::Invariant,
            variant: Variant::WrongStride,
        },
        "byte store at base+iv*2 (stride != width)",
    );
}

#[test]
fn bails_on_value_in_loop() {
    assert_bails(
        Cfg {
            elem_size: 1,
            bound: BoundK::Runtime,
            val: Val::InLoop,
            variant: Variant::Good,
        },
        "stored value defined inside the loop / iv-dependent",
    );
}

#[test]
fn bails_on_base_in_loop() {
    assert_bails(
        Cfg {
            elem_size: 1,
            bound: BoundK::Runtime,
            val: Val::Invariant,
            variant: Variant::BaseInLoop,
        },
        "base defined inside the loop (not invariant)",
    );
}

#[test]
fn bails_on_second_store() {
    assert_bails(
        Cfg {
            elem_size: 1,
            bound: BoundK::Runtime,
            val: Val::Invariant,
            variant: Variant::SecondStore,
        },
        "a second store",
    );
}

#[test]
fn bails_on_call() {
    assert_bails(
        Cfg {
            elem_size: 1,
            bound: BoundK::Runtime,
            val: Val::Invariant,
            variant: Variant::WithCall,
        },
        "a call in the body",
    );
}

#[test]
fn bails_on_reversed_compare() {
    assert_bails(
        Cfg {
            elem_size: 1,
            bound: BoundK::Runtime,
            val: Val::Invariant,
            variant: Variant::Reversed,
        },
        "reversed / non-forward loop compare",
    );
}

#[test]
fn bails_on_small_const_bound() {
    // Const bound < WIDTH_ELEMS (32 for bytes) leaves the loop entirely scalar.
    assert_bails(
        Cfg {
            elem_size: 1,
            bound: BoundK::Const(16),
            val: Val::ConstByte(0),
            variant: Variant::Good,
        },
        "const bound below one full 32-byte block",
    );
}

// ---------------------------------------------------------------------------
// Helper unit checks
// ---------------------------------------------------------------------------

#[test]
fn byte_replicable_predicate() {
    assert!(byte_replicable(0x00, 1));
    assert!(byte_replicable(0x41, 1));
    assert!(byte_replicable(0x0101, 2));
    assert!(byte_replicable(0x0101_0101, 4));
    assert!(!byte_replicable(0x1234, 2));
    assert!(!byte_replicable(0x1234_5678, 4));
    assert_eq!(low_byte(0x1234_5678), 0x78);
}

// ---------------------------------------------------------------------------
// Transfer-register CLASS (the store width / DUP source are BOTH derived from
// it, so a non-GPR transfer must BAIL)
// ---------------------------------------------------------------------------

/// Retype every occurrence of vreg `id` to `class` — models an FP-typed stored
/// value (`Store F32/F64/F16`, which `trust-cg-lower::select_store` lowers to
/// `StrRI` with an `Fpr*` transfer register).
fn retype_vreg(func: &mut MachFunction, id: u32, class: RegClass) {
    for inst in func.insts.iter_mut() {
        for op in inst.operands.iter_mut() {
            if let MachOperand::VReg(v) = op
                && v.id == id
            {
                *v = VReg::new(id, class);
            }
        }
    }
}

#[test]
fn bails_on_fp_transfer_register() {
    // `Fpr32`: the derived width (4) happens to be right, but the stored value
    // would be broadcast with `DUP Vd.4S, Rn` reading the GPR bank — `V5` would
    // silently become `W5`.
    // `Fpr64` / `Fpr16`: `str d`/`str h` access 8/2 bytes while the arm derives
    // 4, so the vector fill would write the wrong bytes-per-element.
    for class in [RegClass::Fpr32, RegClass::Fpr64, RegClass::Fpr16] {
        let mut func = build_fill(Cfg {
            elem_size: 4,
            bound: BoundK::Runtime,
            val: Val::Invariant,
            variant: Variant::Good,
        });
        // v3 is the stored-value register in the canonical fill loop.
        retype_vreg(&mut func, 3, class);
        let (changed, fired) = run(&mut func);
        assert!(
            !changed && fired == 0,
            "must BAIL on a {class:?} transfer register"
        );
        assert_eq!(
            count_op(&func, AArch64Opcode::NeonStpQPost),
            0,
            "no NEON store emitted for a {class:?} transfer register"
        );
        assert_eq!(
            count_op(&func, AArch64Opcode::NeonDupGen),
            0,
            "no DUP-from-GPR emitted for a {class:?} transfer register"
        );
    }
}

#[test]
fn still_fires_on_gpr32_transfer_register() {
    // The gate must admit BOTH GPR widths: `StrRI` with a `Gpr32` transfer is
    // the ordinary 4-byte integer fill, and it must keep vectorizing.
    let mut func = build_fill(Cfg {
        elem_size: 4,
        bound: BoundK::Runtime,
        val: Val::Invariant,
        variant: Variant::Good,
    });
    let (changed, fired) = run(&mut func);
    assert!(changed && fired == 1, "Gpr32 4-byte fill must still fire");
}

/// A MERGE vreg — one def per predecessor, which is how the frontend lowers
/// every block parameter (`isel::select_copy` reuses the parameter's vreg for
/// each incoming edge) — must not resolve to a constant. The def map is
/// last-wins over the emitted layout, so it names whichever arm comes LAST.
///
/// Regression: `match k { 0 => 3, 1 => 5, _ => 7 }` used as a fill value made
/// the vectorized loop broadcast 7 on every path. On a 64-byte fill with k==0,
/// LLVM returned 192 and trust-cg returned 197 (= 64*7 mod 251), at -O2 and
/// -O3. The comment above the admitting predicate already promised this bail;
/// it was never implemented. End-to-end cover: `benchmarks/shape-coverage`
/// `s15_fill_merge_value`.
#[test]
fn const_value_declines_a_merge_vreg() {
    use AArch64Opcode::*;
    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };

    let mut func = MachFunction::new("m".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let arm_a = func.create_block();
    let arm_b = func.create_block();
    let join = func.create_block();
    push(&mut func, bb0, CmpRI, vec![w(1), i(0)]);
    push(&mut func, bb0, BCond, vec![i(1), bl(arm_a)]);
    push(&mut func, bb0, B, vec![bl(arm_b)]);
    // Both arms write the SAME vreg — the merge.
    push(&mut func, arm_a, Movz, vec![w(3), i(3)]);
    push(&mut func, arm_a, B, vec![bl(join)]);
    push(&mut func, arm_b, Movz, vec![w(3), i(7)]);
    push(&mut func, arm_b, B, vec![bl(join)]);
    push(&mut func, join, Ret, vec![]);

    let v3 = VReg::new(3, RegClass::Gpr32);
    assert_eq!(
        crate::effects::live_def_count(&func, 3),
        2,
        "both arms must be live defs of the merge vreg",
    );
    let def = build_def_map(&func);
    assert_eq!(
        copied_const(&func, &def, v3),
        None,
        "a merge vreg must not resolve to whichever arm comes last in layout",
    );
    assert_eq!(
        strip_copies(&func, &def, v3),
        v3,
        "and copy-stripping must stop at it rather than walk one arm's source",
    );

    // Control: a single-def constant still resolves, so the guard above is not
    // simply refusing everything.
    let mut single = MachFunction::new("s".to_string(), Signature::new(vec![], vec![]));
    let e = single.entry;
    push(&mut single, e, Movz, vec![w(3), i(3)]);
    push(&mut single, e, Ret, vec![]);
    let def1 = build_def_map(&single);
    assert_eq!(copied_const(&single, &def1, v3), Some(3));
}

// ---------------------------------------------------------------------------
// L14-P6: a function with many fill loops costs linearly in them
// ---------------------------------------------------------------------------

/// `loops` top-tested byte fills in sequence, each with its own induction,
/// value and address registers and its own constant bound, plus a detached
/// instruction and a block outside the layout that define registers too.
fn build_fill_chain(loops: usize) -> MachFunction {
    let mut func = MachFunction::new("chain".to_string(), Signature::new(vec![], vec![]));
    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;
    let mut current = func.entry;
    for k in 0..loops as u32 {
        let header = func.create_block();
        let body = func.create_block();
        let latch = func.create_block();
        let (value, iv, next, addr) = (100 + 4 * k, 101 + 4 * k, 102 + 4 * k, 103 + 4 * k);
        push(
            &mut func,
            current,
            Movz,
            vec![w(value), i(0x11 * i64::from(k % 7 + 1))],
        );
        push(&mut func, current, Movz, vec![x(iv), i(0)]);
        push(&mut func, current, B, vec![bl(header)]);
        func.add_edge(current, header);
        let exit = func.create_block();
        push(
            &mut func,
            header,
            CmpRI,
            vec![x(iv), i(64 + 16 * i64::from(k))],
        );
        push(&mut func, header, BCond, vec![i(CC_LT), bl(body)]);
        push(&mut func, header, B, vec![bl(exit)]);
        push(&mut func, body, AddRR, vec![x(addr), x(0), x(iv)]);
        push(&mut func, body, StrbRI, vec![w(value), x(addr), i(0)]);
        push(&mut func, body, AddRI, vec![x(next), x(iv), i(1)]);
        push(&mut func, body, B, vec![bl(latch)]);
        push(&mut func, latch, AddRI, vec![x(iv), x(next), i(0)]);
        push(&mut func, latch, B, vec![bl(header)]);
        func.add_edge(header, body);
        func.add_edge(header, exit);
        func.add_edge(body, latch);
        func.add_edge(latch, header);
        current = exit;
    }
    push(&mut func, current, Ret, vec![]);
    // Outside the layout: a detached instruction and a block not in
    // `block_order`, each defining a register the layout also defines.
    func.push_inst(MachInst::new(Movz, vec![x(0), i(1)]));
    let detached = func.create_block();
    push(&mut func, detached, Movz, vec![w(100), i(9)]);
    func.block_order.retain(|&b| b != detached);
    func
}

/// The recognition index answers exactly what the whole-function scans it
/// replaced answer, for every id, instruction and register of each fixture
/// (and some that are absent).
#[test]
fn def_index_answers_what_the_whole_function_scans_answer() {
    let fixtures = [
        build_fill_chain(1),
        build_fill_chain(4),
        build_fill_top_tested(100),
        build_fill(Cfg {
            elem_size: 4,
            bound: BoundK::Runtime,
            val: Val::Invariant,
            variant: Variant::Good,
        }),
    ];
    for func in &fixtures {
        let index = build_def_map(func);
        assert_eq!(index.reaching, crate::effects::build_reaching_def_map(func));
        let max_id = func
            .insts
            .iter()
            .flat_map(|inst| &inst.operands)
            .filter_map(|op| op.as_vreg().map(|reg| reg.id))
            .max()
            .unwrap_or(0);
        for id in 0..=max_id + 2 {
            assert_eq!(
                index.live_def_count(func, id),
                crate::effects::live_def_count(func, id),
                "id {id}"
            );
            for class in [RegClass::Gpr32, RegClass::Gpr64] {
                let v = VReg::new(id, class);
                let scanned = func.block_order.iter().any(|&bid| {
                    func.block(bid)
                        .insts
                        .iter()
                        .any(|&inst| crate::effects::inst_defines_vreg(func.inst(inst), v))
                });
                assert_eq!(index.defined_in_layout(func, v), scanned, "{v:?}");
            }
        }
        for raw in 0..func.insts.len() as u32 + 2 {
            assert_eq!(
                index.block_of_inst(func, InstId(raw)),
                block_of_inst(func, InstId(raw)),
                "inst {raw}"
            );
        }
        // The first questions were answered by the scans, the rest by the
        // indexes: both paths were compared.
        assert!(index.layout.get().is_some() && index.block_of.get().is_some());
    }
}

/// A function that asks few questions never builds the whole-layout indexes.
#[test]
fn a_def_index_asked_few_questions_builds_no_layout_index() {
    let func = build_fill_chain(4);
    let index = build_def_map(&func);
    for id in 0..LITERAL_QUESTIONS {
        assert_eq!(
            index.live_def_count(&func, id),
            crate::effects::live_def_count(&func, id)
        );
        assert_eq!(
            index.block_of_inst(&func, InstId(id)),
            block_of_inst(&func, InstId(id))
        );
    }
    assert!(index.layout.get().is_none() && index.block_of.get().is_none());
    index.live_def_count(&func, 0);
    index.block_of_inst(&func, InstId(0));
    assert!(index.layout.get().is_some() && index.block_of.get().is_some());
}

/// A function with several fill loops vectorizes them all through one
/// private candidate, and the result is exactly what applying them one at a
/// time gives.
#[test]
fn a_chain_of_fill_loops_applies_as_one_candidate_like_one_at_a_time() {
    for loops in [2, 3, 7] {
        let mut batched = build_fill_chain(loops);
        let mut per_plan = batched.clone();
        let (changed, fired) = run(&mut batched);
        FORCE_PER_PLAN.with(|force| force.set(true));
        let (changed_per_plan, fired_per_plan) = run(&mut per_plan);
        FORCE_PER_PLAN.with(|force| force.set(false));
        assert!(changed && changed_per_plan, "{loops} loops");
        assert_eq!(fired, loops);
        assert_eq!(fired_per_plan, loops);
        assert_eq!(
            format!("{batched:?}"),
            format!("{per_plan:?}"),
            "{loops} loops"
        );
    }
}

/// The loop-state checks of one recognition sweep share one index of the
/// function, so their liveness work grows with the function, not with the
/// function times its loops: each loop of a fill chain leaves a register dead
/// after it, whose literal walk visits the rest of the function. With a
/// literal (per-check) index the work reads 2,095, 32,959 and 525,055 blocks
/// at 16, 64 and 256 loops (x15.7 per step); with the shared one each 4x step
/// stays within x5.
#[test]
fn liveness_work_of_a_recognition_sweep_grows_linearly() {
    let work = |loops: usize| {
        let mut func = build_fill_chain(loops);
        let before = crate::loop_contract::liveness_work();
        let (changed, fired) = run(&mut func);
        assert!(changed && fired == loops, "{loops} loops: every fill fires");
        crate::loop_contract::liveness_work() - before
    };
    let sizes = [16usize, 64, 256];
    let costs: Vec<u64> = sizes.iter().map(|&n| work(n)).collect();
    for step in 0..2 {
        let ratio = costs[step + 1] as f64 / costs[step] as f64;
        assert!(
            ratio <= 5.0,
            "liveness work grew x{ratio:.2} from {} to {} loops ({costs:?})",
            sizes[step],
            sizes[step + 1]
        );
    }
}

/// Two recognized plans are valid, but only the first fits the remaining
/// register IDs. The batch must publish nothing when its second plan runs
/// out, and the public pass must retain exactly the old per-plan prefix.
#[test]
fn a_late_batch_exhaustion_rolls_back_then_preserves_the_per_plan_prefix() {
    let mut original = build_fill_chain(2);
    original.try_sync_vreg_counter().expect("fixture IDs fit");
    let dom = DomTree::compute(&original);
    let loops = LoopAnalysis::compute(&original, &dom);
    let def = build_def_map(&original);
    let loop_state = LoopStateIndex::amortized(&original);
    let plans: Vec<_> = loops
        .all_loops()
        .filter_map(|lp| {
            Recognized::recognize(
                &original,
                &dom,
                &def,
                &loop_state,
                lp.header,
                lp.latch,
                &lp.body,
            )
        })
        .collect();
    assert_eq!(plans.len(), 2, "both loops must be recognized");

    // Establish that both plans work with ordinary IDs, and measure the
    // first plan's actual allocation demand instead of hard-coding it.
    let mut control = original.clone();
    assert!(apply(&mut control, &plans[0]));
    let needed = control.next_vreg - original.next_vreg;
    assert!(needed > 0);
    assert!(apply(&mut control, &plans[1]));

    original.next_vreg = u32::MAX - needed;
    let before = format!("{original:?}");
    let mut batched = original.clone();
    assert!(!apply_all(&mut batched, &plans));
    assert_eq!(
        format!("{batched:?}"),
        before,
        "a late batch refusal must publish no earlier plan's edits"
    );

    // The previous path commits the first plan and refuses the second.
    // Its exact result includes the CFG, operands, metadata and counters.
    let mut per_plan = original.clone();
    assert!(apply(&mut per_plan, &plans[0]));
    assert_eq!(per_plan.next_vreg, u32::MAX);
    let prefix = format!("{per_plan:?}");
    assert!(!apply(&mut per_plan, &plans[1]));
    assert_eq!(format!("{per_plan:?}"), prefix);

    let mut public = original;
    let mut pass = NeonFillPass::new();
    assert!(pass.run(&mut public));
    assert_eq!(pass.fired(), 1, "only the first valid plan fits");
    assert_eq!(
        format!("{public:?}"),
        format!("{per_plan:?}"),
        "batch refusal and fallback must preserve the old per-plan result"
    );
}

// ---------------------------------------------------------------------------
// Loop-state contract (`crate::loop_contract`): the vector loop reproduces only
// `iv`, so any other carried or live-out register must refuse. The aarch64
// `fill_u8` / `zero_u32` rows with a carried accumulator and the `fill_last`
// row at N = 1024 were measured wrong through the whole bridge at O2/O3.
// ---------------------------------------------------------------------------

#[test]
fn every_fill_shape_refuses_skipped_register_state() {
    type Build = fn() -> MachFunction;
    let shapes: [(&str, Build); 4] = [
        ("rotated const byte fill", || {
            build_fill(Cfg {
                elem_size: 1,
                bound: BoundK::Const(1024),
                val: Val::ConstByte(7),
                variant: Variant::Good,
            })
        }),
        ("rotated const u32 zero fill", || {
            build_fill(Cfg {
                elem_size: 4,
                bound: BoundK::Const(1024),
                val: Val::ConstByte(0),
                variant: Variant::Good,
            })
        }),
        ("rotated runtime-bound invariant fill", || {
            build_fill(Cfg {
                elem_size: 1,
                bound: BoundK::Runtime,
                val: Val::Invariant,
                variant: Variant::Good,
            })
        }),
        ("top-tested byte fill", || build_fill_top_tested(8192)),
    ];
    let iv = VReg::new(10, RegClass::Gpr64);
    let mut wrong = Vec::new();
    for (name, build) in shapes {
        assert!(
            NeonFillPass::default().run(&mut build()),
            "{name}: plain fixture fires"
        );
        let mut carried = build();
        crate::loop_contract::test_support::add_second_accumulator(&mut carried, iv);
        if NeonFillPass::default().run(&mut carried) {
            wrong.push(format!("{name}: fired with a second accumulator"));
        }
        let mut live_out = build();
        crate::loop_contract::test_support::add_live_out(&mut live_out, iv);
        if NeonFillPass::default().run(&mut live_out) {
            wrong.push(format!("{name}: fired with a live-out-only register"));
        }
        // The control clause: before it this pass filled past a `break` (and
        // past a bounds check against a shorter slice), measured on aarch64 at
        // O2/O3.
        let mut early_exit = build();
        crate::loop_contract::test_support::add_early_exit(&mut early_exit, iv);
        if NeonFillPass::default().run(&mut early_exit) {
            wrong.push(format!("{name}: fired with an early exit"));
        }
    }
    assert!(
        wrong.is_empty(),
        "skipped register state or control:\n  {}",
        wrong.join("\n  ")
    );
}

/// The bridge's block-parameter form of a second recurrence beside the fill
/// (`let mut c = 0u64; for i in 0..128 { a[i] = 0x5a; c += 3 } c`): `c`'s
/// update sits in the body and its writeback is a latch copy next to the iv's,
/// the copy form `find_induction` scans and skips because its step is 3.
/// ```text
/// bb0:    w3 = 0x5a; x10 = 0; x12 = 0; B header
/// header: cmp x10, #128; b.lt body; B exit
/// body:   x20 = x0 + x10; strb w3, [x20]; x11 = x10 + 1; x13 = x12 + 3; B latch
/// latch:  x10 = x11 + 0; x12 = x13 + 0; B header
/// exit:   x21 = x12; ret
/// ```
/// The vector loop advances only `x10`: at N = 128 it consumes every
/// iteration, the scalar remainder runs zero times and `c` is returned as 0
/// instead of 384. The pass must decline and leave the function unchanged.
/// The refusing guard is the loop-state contract (`carried = [iv]`): `x12` is
/// live into the header. Listing `x12` as carried there makes this fire.
#[test]
fn top_tested_fill_with_a_block_parameter_recurrence_declines() {
    let mut func = MachFunction::new("k".to_string(), Signature::new(vec![], vec![]));
    let bb0 = func.entry;
    let header = func.create_block();
    let body = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();
    let push = |func: &mut MachFunction, blk: BlockId, op, ops| {
        let id = func.push_inst(MachInst::new(op, ops));
        func.append_inst(blk, id);
    };
    use AArch64Opcode::*;
    push(&mut func, bb0, Movz, vec![w(3), i(0x5a)]);
    push(&mut func, bb0, Movz, vec![x(10), i(0)]);
    push(&mut func, bb0, Movz, vec![x(12), i(0)]);
    push(&mut func, bb0, B, vec![bl(header)]);
    push(&mut func, header, CmpRI, vec![x(10), i(128)]);
    push(&mut func, header, BCond, vec![i(CC_LT), bl(body)]);
    push(&mut func, header, B, vec![bl(exit)]);
    push(&mut func, body, AddRR, vec![x(20), x(0), x(10)]);
    push(&mut func, body, StrbRI, vec![w(3), x(20), i(0)]);
    push(&mut func, body, AddRI, vec![x(11), x(10), i(1)]);
    push(&mut func, body, AddRI, vec![x(13), x(12), i(3)]);
    push(&mut func, body, B, vec![bl(latch)]);
    push(&mut func, latch, AddRI, vec![x(10), x(11), i(0)]);
    push(&mut func, latch, AddRI, vec![x(12), x(13), i(0)]);
    push(&mut func, latch, B, vec![bl(header)]);
    push(&mut func, exit, MovR, vec![x(21), x(12)]);
    push(&mut func, exit, Ret, vec![]);
    func.add_edge(bb0, header);
    func.add_edge(header, body);
    func.add_edge(header, exit);
    func.add_edge(body, latch);
    func.add_edge(latch, header);

    let before = format!("{func:?}");
    let (changed, fired) = run(&mut func);
    assert!(
        !changed && fired == 0,
        "vectorized a fill loop whose second recurrence x12 (c += 3) the vector loop never advances \
         (changed={changed}, fired={fired})"
    );
    assert_eq!(
        format!("{func:?}"),
        before,
        "a declined run must leave the function unchanged"
    );
}
