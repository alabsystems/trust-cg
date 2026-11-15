// trust-cg-verify/post_ra_spill_slots/tests.rs - frame dataflow net unit tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use trust_cg_ir::aarch64_regs::{D8, D9, SP, X0, X1, X9, X10, X11, X16, X19, X20, X29, X30, XZR};
use trust_cg_ir::{BlockId, InstFlags, InstId, Signature};

// ---------------------------------------------------------------------------
// Builders for the shapes frame lowering emits
// ---------------------------------------------------------------------------

static USES_X0: [PReg; 1] = [X0];
static USES_X9: [PReg; 1] = [X9];

fn inst(opcode: AArch64Opcode, operands: Vec<MachOperand>) -> MachInst {
    MachInst::new(opcode, operands)
}

fn r(p: PReg) -> MachOperand {
    MachOperand::PReg(p)
}

fn sp() -> MachOperand {
    MachOperand::Special(SpecialReg::SP)
}

fn imm(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}

fn stp_pre(a: PReg, b: PReg, off: i64) -> MachInst {
    inst(AArch64Opcode::StpPreIndex, vec![r(a), r(b), sp(), imm(off)])
}

fn stp(a: PReg, b: PReg, off: i64) -> MachInst {
    inst(AArch64Opcode::StpRI, vec![r(a), r(b), sp(), imm(off)])
}

fn ldp(a: PReg, b: PReg, off: i64) -> MachInst {
    inst(AArch64Opcode::LdpRI, vec![r(a), r(b), sp(), imm(off)])
}

fn ldp_post(a: PReg, b: PReg, off: i64) -> MachInst {
    inst(
        AArch64Opcode::LdpPostIndex,
        vec![r(a), r(b), sp(), imm(off)],
    )
}

fn add_fp_sp(k: i64) -> MachInst {
    inst(AArch64Opcode::AddRI, vec![r(X29), sp(), imm(k)])
}

fn sub_sp(k: i64) -> MachInst {
    inst(AArch64Opcode::SubRI, vec![sp(), sp(), imm(k)])
}

fn add_sp(k: i64) -> MachInst {
    inst(AArch64Opcode::AddRI, vec![sp(), sp(), imm(k)])
}

fn mov_sp_fp() -> MachInst {
    inst(AArch64Opcode::AddRI, vec![sp(), r(X29), imm(0)])
}

fn movz(dst: PReg, v: i64) -> MachInst {
    inst(AArch64Opcode::Movz, vec![r(dst), imm(v)])
}

fn add_rr(d: PReg, a: PReg, b: PReg) -> MachInst {
    inst(AArch64Opcode::AddRR, vec![r(d), r(a), r(b)])
}

fn add_ri(d: PReg, a: PReg, k: i64) -> MachInst {
    inst(AArch64Opcode::AddRI, vec![r(d), r(a), imm(k)])
}

fn spill(mut i: MachInst) -> MachInst {
    i.flags.insert(InstFlags::SPILL_SLOT_ACCESS);
    i
}

fn spill_store(data: PReg, base: PReg, offset: i64) -> MachInst {
    spill(inst(
        AArch64Opcode::StrRI,
        vec![r(data), MachOperand::MemOp { base, offset }],
    ))
}

fn spill_load(data: PReg, base: PReg, offset: i64) -> MachInst {
    spill(inst(
        AArch64Opcode::LdrRI,
        vec![r(data), MachOperand::MemOp { base, offset }],
    ))
}

fn plain_store(data: PReg, base: PReg, offset: i64) -> MachInst {
    inst(
        AArch64Opcode::StrRI,
        vec![r(data), MachOperand::MemOp { base, offset }],
    )
}

fn plain_load(data: PReg, base: PReg, offset: i64) -> MachInst {
    inst(
        AArch64Opcode::LdrRI,
        vec![r(data), MachOperand::MemOp { base, offset }],
    )
}

fn call(uses: &'static [PReg]) -> MachInst {
    inst(
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol("callee".to_string())],
    )
    .with_implicit_uses(uses)
}

fn ret(lanes: &'static [PReg]) -> MachInst {
    inst(AArch64Opcode::Ret, vec![r(X30)]).with_implicit_uses(lanes)
}

fn probe() -> MachInst {
    inst(AArch64Opcode::StrRI, vec![r(XZR), sp(), imm(0)])
}

fn single_block(name: &str, insts: Vec<MachInst>) -> MachFunction {
    let mut f = MachFunction::new(name.to_string(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    for i in insts {
        let id = f.push_inst(i);
        f.append_inst(entry, id);
    }
    f
}

fn push(f: &mut MachFunction, block: BlockId, insts: Vec<MachInst>) {
    for i in insts {
        let id = f.push_inst(i);
        f.append_inst(block, id);
    }
}

fn analyzed(f: &MachFunction) -> (Vec<SpillSlotViolation>, FrameNetStats) {
    match analyze_frame(f) {
        FrameNetOutcome::Analyzed { violations, stats } => (violations, stats),
        FrameNetOutcome::Declined(reason) => panic!("{}: declined ({})", f.name, reason.tag()),
    }
}

fn kinds(f: &MachFunction) -> Vec<SpillSlotViolationKind> {
    analyzed(f).0.iter().map(|v| v.kind).collect()
}

fn assert_clean(f: &MachFunction) -> FrameNetStats {
    let (violations, stats) = analyzed(f);
    assert!(violations.is_empty(), "{}: {violations:#?}", f.name);
    stats
}

fn assert_flags(f: &MachFunction, expected: SpillSlotViolationKind) {
    let found = kinds(f);
    assert!(
        found.contains(&expected),
        "{}: expected {expected:?}, found {found:?}",
        f.name
    );
    assert!(
        evaluate(f, PostRegallocRecheckMode::Enforce).is_some(),
        "{}: enforce must fail closed",
        f.name
    );
}

// ---------------------------------------------------------------------------
// The canonical framed, spilling, calling function
// ---------------------------------------------------------------------------

/// Prologue / body / epilogue in the shape `frame::emit_prologue` and
/// `frame::emit_epilogue` produce for an FP/LR + X19/X20 frame with a 32-byte
/// local/spill area: `x29 = CFA-16`, `SP_body = CFA-64`. Two values are spilled
/// across the call, one FP-relative (CFA-40) and one SP-relative (CFA-56).
fn framed_body() -> Vec<MachInst> {
    vec![
        stp_pre(X20, X19, -32),    // 0: save x20/x19 at CFA-32, SP=CFA-32
        stp(X29, X30, 16),         // 1: save FP/LR at CFA-16
        add_fp_sp(16),             // 2: x29 = CFA-16
        sub_sp(32),                // 3: SP = CFA-64
        movz(X19, 7),              // 4: body uses callee-saved x19
        movz(X9, 5),               // 5
        spill_store(X9, X29, -24), // 6: spill to CFA-40
        movz(X10, 6),              // 7
        spill_store(X10, SP, 8),   // 8: spill to CFA-56
        call(&USES_X0),            // 9: clobbers x9/x10
        spill_load(X9, X29, -24),  // 10: reload
        spill_load(X10, SP, 8),    // 11: reload
        add_rr(X0, X9, X10),       // 12
        add_rr(X0, X0, X19),       // 13
        add_sp(32),                // 14: SP = CFA-32 (teardown begins)
        ldp(X29, X30, 16),         // 15: restore FP/LR
        ldp_post(X20, X19, 32),    // 16: restore x20/x19, SP = CFA
        ret(&USES_X0),             // 17
    ]
}

fn framed(name: &str, edit: impl FnOnce(&mut Vec<MachInst>)) -> MachFunction {
    let mut body = framed_body();
    edit(&mut body);
    single_block(name, body)
}

#[test]
fn framed_spilling_function_is_modeled_and_clean() {
    let f = framed("framed_clean", |_| {});
    let stats = assert_clean(&f);
    assert!(stats.framed);
    assert_eq!(stats.spill_stores, 2);
    assert_eq!(stats.spill_reloads_checked, 2);
    assert_eq!(stats.exits_checked, 1);
    assert_eq!(stats.calls, 1);
    assert!(evaluate(&f, PostRegallocRecheckMode::Enforce).is_none());
}

#[test]
fn corrupt_altered_reload_offset_to_unwritten_cell() {
    // CFA-48 is never spill-stored.
    let f = framed("alter_reload_offset", |b| b[10] = spill_load(X9, X29, -32));
    assert_flags(&f, SpillSlotViolationKind::ReloadWithoutReachingStore);
}

#[test]
fn corrupt_altered_reload_offset_onto_save_cell() {
    // [x29,#0] is the saved FP: a non-spill (callee-save) cell.
    let f = framed("alter_reload_onto_save", |b| b[10] = spill_load(X9, X29, 0));
    assert_flags(&f, SpillSlotViolationKind::ReloadFromNonSpillStore);
}

#[test]
fn corrupt_altered_spill_store_offset() {
    let f = framed("alter_store_offset", |b| b[6] = spill_store(X9, X29, -32));
    assert_flags(&f, SpillSlotViolationKind::ReloadWithoutReachingStore);
}

#[test]
fn corrupt_altered_sp_relative_offset() {
    let f = framed("alter_sp_offset", |b| b[11] = spill_load(X10, SP, 16));
    assert_flags(&f, SpillSlotViolationKind::ReloadWithoutReachingStore);
}

#[test]
fn corrupt_deleted_spill_store() {
    let f = framed("delete_store", |b| {
        b.remove(8);
    });
    assert_flags(&f, SpillSlotViolationKind::ReloadWithoutReachingStore);
}

#[test]
fn corrupt_swapped_reload_register() {
    // The reload lands in x11, so the consumer reads the call-clobbered x9.
    let f = framed("swap_reload_reg", |b| b[10] = spill_load(X11, X29, -24));
    assert_flags(&f, SpillSlotViolationKind::ClobberedRegisterRead);
}

#[test]
fn corrupt_reload_hoisted_across_clobbering_call() {
    let f = framed("reload_across_call", |b| {
        let reload = b.remove(10);
        b.insert(9, reload);
    });
    assert_flags(&f, SpillSlotViolationKind::ClobberedRegisterRead);
}

#[test]
fn corrupt_value_kept_in_caller_saved_register_across_call() {
    // No spill at all: x9 is simply assumed to survive the call.
    let f = framed("no_spill_across_call", |b| {
        b[10] = movz(X11, 0);
    });
    assert_flags(&f, SpillSlotViolationKind::ClobberedRegisterRead);
}

#[test]
fn corrupt_dropped_callee_save_restore() {
    let f = framed("drop_restore", |b| b[16] = add_sp(32));
    assert_flags(&f, SpillSlotViolationKind::CalleeSavedNotRestored);
}

#[test]
fn corrupt_dropped_callee_save_save() {
    let f = framed("drop_save", |b| b[0] = sub_sp(32));
    assert_flags(&f, SpillSlotViolationKind::CalleeSavedNotRestored);
}

#[test]
fn corrupt_dropped_link_register_restore() {
    let f = framed("drop_lr_restore", |b| {
        b[15] = inst(
            AArch64Opcode::LdrRI,
            vec![
                r(X29),
                MachOperand::MemOp {
                    base: SP,
                    offset: 16,
                },
            ],
        )
    });
    assert_flags(&f, SpillSlotViolationKind::ReturnAddressNotRestored);
}

#[test]
fn corrupt_missing_sp_deallocation() {
    let f = framed("sp_not_restored", |b| {
        b.remove(14);
    });
    assert_flags(&f, SpillSlotViolationKind::StackPointerNotRestored);
}

#[test]
fn corrupt_return_lane_written_in_epilogue() {
    let f = framed("return_lane_epilogue", |b| b.insert(15, movz(X0, 0)));
    assert_flags(&f, SpillSlotViolationKind::ReturnLaneClobbered);
}

#[test]
fn corrupt_restore_misdirected_into_return_lane() {
    let f = framed("restore_into_x0", |b| b[16] = ldp_post(X20, X0, 32));
    assert_flags(&f, SpillSlotViolationKind::ReturnLaneHoldsCallerValue);
    assert_flags(&f, SpillSlotViolationKind::CalleeSavedNotRestored);
}

#[test]
fn corrupt_caller_callee_saved_value_read() {
    // x19 read before the body defines it.
    let f = framed("read_caller_x19", |b| b.insert(4, add_ri(X1, X19, 1)));
    assert_flags(&f, SpillSlotViolationKind::CallerSavedValueRead);
}

#[test]
fn corrupt_spill_cell_inside_outgoing_argument_area() {
    // A stack argument at [SP,#0] (CFA-64), then a spill into the same cell
    // before the call: the callee owns its incoming argument bytes.
    let f = framed("spill_in_arg_area", |b| {
        b.insert(9, plain_store(X1, SP, 0));
        b.insert(10, spill_store(X10, SP, 0));
        b[13] = spill_load(X10, SP, 0);
    });
    assert_flags(&f, SpillSlotViolationKind::ReloadOfCallClobberedSlot);
}

#[test]
fn corrupt_spill_cell_overwritten_by_non_spill_store() {
    let f = framed("local_overlaps_spill", |b| {
        b.insert(9, plain_store(X1, X29, -24))
    });
    assert_flags(&f, SpillSlotViolationKind::ReloadFromNonSpillStore);
}

#[test]
fn call_argument_register_must_not_be_clobbered() {
    // Passing x9 after an earlier call clobbered it.
    let f = single_block(
        "clobbered_arg",
        vec![
            stp_pre(X29, X30, -16),
            add_fp_sp(0),
            call(&USES_X0),
            call(&USES_X9),
            ldp_post(X29, X30, 16),
            ret(&USES_X0),
        ],
    );
    assert_flags(&f, SpillSlotViolationKind::ClobberedRegisterRead);
}

// ---------------------------------------------------------------------------
// Frame shapes
// ---------------------------------------------------------------------------

#[test]
fn frameless_leaf_is_modeled() {
    let f = single_block("leaf", vec![add_ri(X0, X0, 1), ret(&USES_X0)]);
    let stats = assert_clean(&f);
    assert!(!stats.framed);
    assert_eq!(stats.exits_checked, 1);
}

#[test]
fn callee_saved_fpr_pair_round_trip() {
    let body = |restore: bool| {
        let mut v = vec![
            stp_pre(D8, D9, -32),
            stp(X29, X30, 16),
            add_fp_sp(16),
            inst(AArch64Opcode::FmovImm, vec![r(D8), MachOperand::FImm(1.0)]),
            call(&USES_X0),
            add_ri(X0, X0, 1),
            ldp(X29, X30, 16),
        ];
        if restore {
            v.push(ldp_post(D8, D9, 32));
        } else {
            v.push(add_sp(32));
        }
        v.push(ret(&USES_X0));
        v
    };
    assert_clean(&single_block("fpr_saved", body(true)));
    assert_flags(
        &single_block("fpr_not_restored", body(false)),
        SpillSlotViolationKind::CalleeSavedNotRestored,
    );
}

#[test]
fn large_offset_scratch_materialization_is_resolved() {
    // movz x16,#300 ; sub x16,x29,x16 ; str/ldr [x16] reaches CFA-316.
    let mk = |reload_off: i64| {
        single_block(
            "large_offset",
            vec![
                stp_pre(X29, X30, -16),
                add_fp_sp(0),
                sub_sp(512),
                movz(X9, 1),
                movz(X16, 300),
                inst(AArch64Opcode::SubRR, vec![r(X16), r(X29), r(X16)]),
                spill_store(X9, X16, 0),
                movz(X16, reload_off),
                inst(AArch64Opcode::SubRR, vec![r(X16), r(X29), r(X16)]),
                spill_load(X9, X16, 0),
                add_rr(X0, X9, X9),
                add_sp(512),
                ldp_post(X29, X30, 16),
                ret(&USES_X0),
            ],
        )
    };
    let stats = assert_clean(&mk(300));
    assert_eq!(stats.spill_reloads_checked, 1);
    assert_flags(&mk(308), SpillSlotViolationKind::ReloadWithoutReachingStore);
}

/// Entry: saves + `movz x16,#n`; loop: `sub sp,#4096 ; str xzr,[sp] ; subs ;
/// b.ne`; body: residual allocation, an SP-relative spill pair and the epilogue.
fn probe_loop_function(reload_off: i64) -> MachFunction {
    let mut f = MachFunction::new("probe_loop".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let lp = f.create_block();
    let body = f.create_block();
    push(
        &mut f,
        entry,
        vec![stp_pre(X29, X30, -16), add_fp_sp(0), movz(X16, 5)],
    );
    push(
        &mut f,
        lp,
        vec![
            sub_sp(4096),
            probe(),
            inst(AArch64Opcode::SubsRI, vec![r(X16), r(X16), imm(1)]),
            inst(AArch64Opcode::BCond, vec![imm(1), MachOperand::Block(lp)]),
        ],
    );
    push(
        &mut f,
        body,
        vec![
            sub_sp(32),
            probe(),
            movz(X9, 3),
            spill_store(X9, SP, 8),
            call(&USES_X0),
            spill_load(X9, SP, reload_off),
            add_rr(X0, X0, X9),
            add_sp(4096),
            add_sp(4096),
            add_sp(4096),
            add_sp(4096),
            add_sp(4096),
            add_sp(32),
            ldp_post(X29, X30, 16),
            ret(&USES_X0),
        ],
    );
    f.add_edge(entry, lp);
    f.add_edge(lp, lp);
    f.add_edge(lp, body);
    f
}

#[test]
fn counted_stack_probe_loop_is_summarized() {
    let stats = assert_clean(&probe_loop_function(8));
    assert_eq!(stats.probe_loops, 1);
    assert_eq!(stats.spill_reloads_checked, 1);
    assert_flags(
        &probe_loop_function(16),
        SpillSlotViolationKind::ReloadWithoutReachingStore,
    );
}

#[test]
fn dynamic_frame_uses_fp_relative_spills_and_restores_sp_from_fp() {
    // A runtime-sized allocation leaves SP unknown; FP-relative spills stay
    // resolvable and `mov sp, x29` restores SP in the epilogue.
    let mk = |sp_relative_spill: bool| {
        let mut body = vec![
            stp_pre(X29, X30, -16),
            add_fp_sp(0),
            sub_sp(16),
            inst(AArch64Opcode::SubRR, vec![r(X1), r(X1), r(X0)]),
            inst(AArch64Opcode::AddRI, vec![sp(), r(X1), imm(0)]),
            movz(X9, 4),
        ];
        if sp_relative_spill {
            body.push(spill_store(X9, SP, 8));
            body.push(spill_load(X9, SP, 8));
        } else {
            body.push(spill_store(X9, X29, -8));
            body.push(call(&USES_X0));
            body.push(spill_load(X9, X29, -8));
        }
        body.extend([
            add_rr(X0, X0, X9),
            mov_sp_fp(),
            ldp_post(X29, X30, 16),
            ret(&USES_X0),
        ]);
        single_block("dynamic", body)
    };
    let stats = assert_clean(&mk(false));
    assert_eq!(stats.spill_reloads_checked, 1);
    assert!(matches!(
        analyze_frame(&mk(true)),
        FrameNetOutcome::Declined(DeclineReason::UnresolvedSpillAddress)
    ));
}

/// b0 -> {b1, b2} -> b3 in a framed function; `store_in_b2` controls whether
/// the second arm spills before the join reloads.
fn framed_diamond(store_in_b2: bool) -> MachFunction {
    let mut f = MachFunction::new("framed_diamond".into(), Signature::new(vec![], vec![]));
    let b0 = f.entry;
    let b1 = f.create_block();
    let b2 = f.create_block();
    let b3 = f.create_block();
    push(
        &mut f,
        b0,
        vec![
            stp_pre(X29, X30, -16),
            add_fp_sp(0),
            sub_sp(16),
            movz(X9, 1),
        ],
    );
    push(&mut f, b1, vec![spill_store(X9, X29, -8)]);
    if store_in_b2 {
        push(&mut f, b2, vec![spill_store(X9, X29, -8)]);
    }
    push(
        &mut f,
        b3,
        vec![
            call(&USES_X0),
            spill_load(X9, X29, -8),
            add_rr(X0, X0, X9),
            add_sp(16),
            ldp_post(X29, X30, 16),
            ret(&USES_X0),
        ],
    );
    f.add_edge(b0, b1);
    f.add_edge(b0, b2);
    f.add_edge(b1, b3);
    f.add_edge(b2, b3);
    f
}

#[test]
fn framed_diamond_requires_the_spill_on_every_path() {
    assert_clean(&framed_diamond(true));
    assert_flags(
        &framed_diamond(false),
        SpillSlotViolationKind::ReloadWithoutReachingStore,
    );
}

#[test]
fn framed_loop_with_back_edge_converges_clean() {
    let mut f = MachFunction::new("framed_loop".into(), Signature::new(vec![], vec![]));
    let b0 = f.entry;
    let header = f.create_block();
    let exit = f.create_block();
    push(
        &mut f,
        b0,
        vec![
            stp_pre(X20, X19, -32),
            stp(X29, X30, 16),
            add_fp_sp(16),
            sub_sp(16),
            movz(X19, 0),
            movz(X9, 1),
            spill_store(X9, SP, 0),
        ],
    );
    push(
        &mut f,
        header,
        vec![
            call(&USES_X0),
            spill_load(X9, SP, 0),
            add_ri(X9, X9, 1),
            spill_store(X9, SP, 0),
            add_ri(X19, X19, 1),
            inst(
                AArch64Opcode::Cbnz,
                vec![r(X19), MachOperand::Block(header)],
            ),
        ],
    );
    push(
        &mut f,
        exit,
        vec![
            add_rr(X0, X9, X19),
            add_sp(16),
            ldp(X29, X30, 16),
            ldp_post(X20, X19, 32),
            ret(&USES_X0),
        ],
    );
    f.add_edge(b0, header);
    f.add_edge(header, header);
    f.add_edge(header, exit);
    let stats = assert_clean(&f);
    assert_eq!(stats.spill_reloads_checked, 1);
}

// ---------------------------------------------------------------------------
// Declines
// ---------------------------------------------------------------------------

#[test]
fn flagged_pair_spill_declines_with_reason() {
    let f = single_block(
        "pair_spill",
        vec![spill(stp(X9, X10, -16)), spill_load(X9, SP, -16)],
    );
    assert!(matches!(
        analyze_frame(&f),
        FrameNetOutcome::Declined(DeclineReason::UnmodeledSpillAccess)
    ));
}

#[test]
fn flagged_spill_through_non_frame_base_declines() {
    // X29 is never established: it is the caller's frame pointer.
    let f = single_block(
        "fp_not_frame",
        vec![spill_store(X0, X29, -16), spill_load(X9, X29, -16)],
    );
    assert!(matches!(
        analyze_frame(&f),
        FrameNetOutcome::Declined(DeclineReason::UnresolvedSpillAddress)
    ));
    assert!(check(&f).is_empty());
}

#[test]
fn out_of_range_successor_declines() {
    let mut f = single_block("bad_edge", vec![spill_load(X9, SP, -16)]);
    f.blocks[f.entry.0 as usize].succs.push(BlockId(u32::MAX));
    assert!(matches!(
        analyze_frame(&f),
        FrameNetOutcome::Declined(DeclineReason::MalformedCfg)
    ));
}

#[test]
fn surviving_vreg_declines() {
    use trust_cg_ir::{RegClass, VReg};
    let f = single_block(
        "vreg",
        vec![
            inst(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                    MachOperand::MemOp {
                        base: SP,
                        offset: -16,
                    },
                ],
            ),
            spill_load(X9, SP, -16),
        ],
    );
    assert!(matches!(
        analyze_frame(&f),
        FrameNetOutcome::Declined(DeclineReason::NonFinalStream)
    ));
    assert!(check(&f).is_empty());
}

#[test]
fn decline_reasons_have_distinct_tags() {
    let mut tags: Vec<&str> = DeclineReason::ALL.iter().map(|r| r.tag()).collect();
    tags.sort_unstable();
    tags.dedup();
    assert_eq!(tags.len(), DeclineReason::ALL.len());
}

// ---------------------------------------------------------------------------
// Flagged reloads in frameless shapes (stronger than the legacy rule)
// ---------------------------------------------------------------------------

#[test]
fn flagged_reload_of_never_stored_cell_refutes() {
    let f = single_block("flagged_untracked", vec![spill_load(X9, SP, -16)]);
    assert_eq!(
        kinds(&f),
        vec![SpillSlotViolationKind::ReloadWithoutReachingStore]
    );
}

#[test]
fn stale_predecessors_cannot_hide_store_free_path() {
    let mut f = framed_diamond(false);
    let join = f.blocks[f.entry.0 as usize].succs[0];
    let join = f.blocks[join.0 as usize].succs[0];
    let storing_arm = f.blocks[f.entry.0 as usize].succs[0];
    f.blocks[join.0 as usize].preds = vec![storing_arm];
    assert!(kinds(&f).contains(&SpillSlotViolationKind::ReloadWithoutReachingStore));
}

#[test]
fn block_order_omission_cannot_hide_reload() {
    let mut f = single_block("omitted", vec![spill_load(X9, SP, -16)]);
    f.block_order.clear();
    assert_eq!(check(&f).len(), 1);
}

// ---------------------------------------------------------------------------
// Legacy frameless rule (unflagged SP-relative slots), preserved behavior
// ---------------------------------------------------------------------------

fn store(base: PReg, offset: i64) -> MachInst {
    plain_store(X0, base, offset)
}

fn load(base: PReg, offset: i64) -> MachInst {
    plain_load(X9, base, offset)
}

#[test]
fn legacy_store_then_reload_passes() {
    let f = single_block("good", vec![store(SP, -16), load(SP, -16)]);
    assert!(check(&f).is_empty());
    assert!(evaluate(&f, PostRegallocRecheckMode::Warn).is_none());
    assert!(evaluate(&f, PostRegallocRecheckMode::Enforce).is_none());
}

#[test]
fn legacy_reload_without_reaching_store_refutes() {
    let f = single_block("bad", vec![load(SP, -16), store(SP, -16)]);
    let vs = check(&f);
    assert_eq!(vs.len(), 1);
    assert_eq!(
        vs[0].kind,
        SpillSlotViolationKind::ReloadWithoutReachingStore
    );
    assert!(evaluate(&f, PostRegallocRecheckMode::Enforce).is_some());
    assert!(evaluate(&f, PostRegallocRecheckMode::Warn).is_none());
    assert!(evaluate(&f, PostRegallocRecheckMode::Off).is_none());
}

#[test]
fn legacy_wrong_offset_reload_refutes() {
    let f = single_block(
        "wrong_off",
        vec![store(SP, -16), load(SP, -8), store(SP, -8)],
    );
    assert_eq!(check(&f).len(), 1);
}

#[test]
fn legacy_reload_of_never_stored_slot_not_flagged() {
    let f = single_block("untracked", vec![load(SP, -16)]);
    assert!(check(&f).is_empty());
}

#[test]
fn legacy_rule_does_not_apply_to_fp_base() {
    let f = single_block("fp_frame", vec![load(X29, -16), store(X29, -16)]);
    assert!(check(&f).is_empty());
    let f_sp = single_block("sp_frame", vec![load(SP, -16), store(SP, -16)]);
    assert_eq!(check(&f_sp).len(), 1);
}

#[test]
fn unflagged_loads_in_framed_functions_are_not_initialization_checked() {
    // Locals may legitimately be read partially initialized or under a
    // dynamic guard; only flagged spill reloads carry the initialization rule.
    // [x29,#-32] is CFA-48, an unwritten local cell.
    let f = framed("unflagged_local_read", |b| {
        b.insert(4, plain_load(X1, X29, -32))
    });
    assert_clean(&f);
}

#[test]
fn mode_default_is_enforce() {
    assert_eq!(AARCH64_SPILL_SLOT_DEFAULT, PostRegallocRecheckMode::Enforce);
}

#[test]
fn inst_ids_are_stable_for_builders() {
    // Guards the builder helpers used above.
    let f = framed("ids", |_| {});
    assert_eq!(f.blocks[f.entry.0 as usize].insts[0], InstId(0));
}

fn mov(dst: PReg, src: PReg) -> MachInst {
    inst(AArch64Opcode::MovR, vec![r(dst), r(src)])
}

#[test]
fn caller_value_may_be_moved_but_not_consumed() {
    // Copying the caller's x19 (or `mov x19, x19`) is not a use of its value.
    assert_clean(&framed("move_caller_x19", |b| {
        b.insert(4, mov(X1, X19));
        b.insert(0, mov(X19, X19));
    }));
    // Computing with the copy is.
    assert_flags(
        &framed("consume_moved_caller_x19", |b| {
            b.insert(4, mov(X1, X19));
            b.insert(5, add_ri(X1, X1, 1));
        }),
        SpillSlotViolationKind::CallerSavedValueRead,
    );
}

#[test]
fn copy_of_a_clobbered_register_is_flagged_where_consumed() {
    // A copy only moves the garbage; the consumer of the copy is flagged.
    let f = framed("copy_clobbered", |b| {
        b[10] = mov(X11, X9);
        b.insert(11, spill_load(X9, X29, -24));
        b.insert(12, add_ri(X1, X11, 1));
    });
    let found = kinds(&f);
    assert_eq!(
        found,
        vec![SpillSlotViolationKind::ClobberedRegisterRead],
        "only the consumer of the copy is reported"
    );
}

#[test]
fn return_lane_copied_from_a_restored_callee_saved_register_is_flagged() {
    let f = framed("return_moved_caller_value", |b| b.insert(17, mov(X0, X19)));
    assert_flags(&f, SpillSlotViolationKind::ReturnLaneHoldsCallerValue);
}

/// b0 spills, calls (the invoke), then returns normally through its epilogue;
/// b1 is the landing pad, entered by unwinding from the call with the frame
/// intact, and reloads the spilled value before its own epilogue.
fn landing_pad_function(with_eh_metadata: bool) -> MachFunction {
    use trust_cg_ir::function::{EhCallSiteEntry, LandingPadEntry};
    let mut f = MachFunction::new("landing_pad".into(), Signature::new(vec![], vec![]));
    let b0 = f.entry;
    let pad = f.create_block();
    let epilogue = || vec![add_sp(16), ldp_post(X29, X30, 16), ret(&USES_X0)];
    let mut body0 = vec![
        stp_pre(X29, X30, -16),
        add_fp_sp(0),
        sub_sp(16),
        movz(X9, 1),
        spill_store(X9, X29, -8),
        call(&USES_X0),
        movz(X0, 0),
    ];
    body0.extend(epilogue());
    push(&mut f, b0, body0);
    let mut body1 = vec![call(&USES_X0), spill_load(X9, X29, -8), add_rr(X0, X0, X9)];
    body1.extend(epilogue());
    push(&mut f, pad, body1);
    f.add_edge(b0, pad);
    if with_eh_metadata {
        f.eh_metadata.add_landing_pad(LandingPadEntry {
            block: pad,
            offset: 0,
            catch_type_indices: vec![0],
            is_cleanup: false,
        });
        f.eh_metadata.add_call_site(EhCallSiteEntry {
            call_block: b0,
            start_offset: 0,
            length: 4,
            landing_pad_block: Some(pad),
        });
    }
    f
}

#[test]
fn landing_pad_is_entered_from_the_call_site_with_the_frame_intact() {
    let stats = assert_clean(&landing_pad_function(true));
    assert_eq!(stats.spill_reloads_checked, 1);
    assert_eq!(stats.exits_checked, 2);
    // Without the unwind metadata the same edge is an ordinary fallthrough
    // from b0's end, after its teardown restored the caller's FP: the pad's
    // FP-relative reload then has no frame address and the stream declines.
    assert!(matches!(
        analyze_frame(&landing_pad_function(false)),
        FrameNetOutcome::Declined(DeclineReason::UnresolvedSpillAddress)
    ));
}

/// Shrink-wrapped shape: b0 branches to a framed arm b1 (prologue, call,
/// epilogue, `b b3`) or a frameless arm b2; the shared return b3 computes the
/// return lane after the frame edge's teardown, which is frameless code by
/// design. `tail` is b3's body before its `ret`.
fn shrink_wrapped(tail: Vec<MachInst>) -> MachFunction {
    let mut f = MachFunction::new("shrink_wrapped".into(), Signature::new(vec![], vec![]));
    let b0 = f.entry;
    let framed_arm = f.create_block();
    let leaf_arm = f.create_block();
    let shared = f.create_block();
    push(
        &mut f,
        b0,
        vec![inst(
            AArch64Opcode::Cbz,
            vec![r(X0), MachOperand::Block(leaf_arm)],
        )],
    );
    push(
        &mut f,
        framed_arm,
        vec![
            stp_pre(X20, X19, -32),
            stp(X29, X30, 16),
            add_fp_sp(16),
            mov(X19, X0),
            call(&USES_X0),
            add_rr(X10, X0, X19),
            ldp(X29, X30, 16),
            ldp_post(X20, X19, 32),
            inst(AArch64Opcode::B, vec![MachOperand::Block(shared)]),
        ],
    );
    push(&mut f, leaf_arm, vec![movz(X10, 0)]);
    let mut body = tail;
    body.push(ret(&USES_X0));
    push(&mut f, shared, body);
    f.add_edge(b0, framed_arm);
    f.add_edge(b0, leaf_arm);
    f.add_edge(framed_arm, shared);
    f.add_edge(leaf_arm, shared);
    f
}

#[test]
fn shrink_wrapped_shared_return_after_frame_edge_teardown_is_clean() {
    assert_clean(&shrink_wrapped(vec![mov(X0, X10)]));
    assert_clean(&shrink_wrapped(vec![add_ri(X0, X10, 1)]));
    // An x0 write inside the framed arm's own epilogue is tainted there.
    let mut f = shrink_wrapped(vec![mov(X0, X10)]);
    let framed_arm = f.blocks[f.entry.0 as usize].succs[0];
    let id = f.push_inst(movz(X0, 0));
    f.blocks[framed_arm.0 as usize].insts.insert(7, id);
    // x0 is then overwritten by the shared block's copy, so the exit is clean:
    // only a write that REACHES the return lane is a clobber.
    assert_clean(&f);
}

// ---------------------------------------------------------------------------
// Reload offsets shifted within or across adjacent spill cells
// ---------------------------------------------------------------------------

/// [`framed_body`] with a third spill cell directly below x9's: x9 is spilled
/// to CFA-40 (`[x29,#-24]`) and x11 to CFA-48 (`[x29,#-32]`), both before the
/// call, so every byte of CFA-48..CFA-32 is spill-stored on every path.
fn adjacent_spill_cells(reload: MachInst) -> MachFunction {
    framed("adjacent_spill_cells", |b| {
        b.insert(8, movz(X11, 9));
        b.insert(9, spill_store(X11, X29, -32));
        // b[12] is the x9 reload after the call.
        b[12] = reload;
    })
}

#[test]
fn adjacent_spill_cells_baseline_is_clean() {
    let stats = assert_clean(&adjacent_spill_cells(spill_load(X9, X29, -24)));
    assert_eq!(stats.spill_stores, 3);
}

#[test]
fn corrupt_reload_offset_shifted_across_two_spill_cells() {
    // [x29,#-28] reads the top half of x11's cell and the bottom half of x9's:
    // every byte is spill-stored, but by two different spill stores.
    assert_flags(
        &adjacent_spill_cells(spill_load(X9, X29, -28)),
        SpillSlotViolationKind::ReloadMisalignedWithSpillStore,
    );
}

#[test]
fn corrupt_reload_reads_the_upper_half_of_a_spill_cell() {
    use trust_cg_ir::aarch64_regs::W9;
    // A 4-byte reload of the upper half of x9's 8-byte spill cell.
    assert_flags(
        &adjacent_spill_cells(spill_load(W9, X29, -20)),
        SpillSlotViolationKind::ReloadMisalignedWithSpillStore,
    );
}

#[test]
fn corrupt_reload_width_differs_from_its_spill_store() {
    use trust_cg_ir::aarch64_regs::W9;
    // A 4-byte reload of an 8-byte spill store at the same offset.
    assert_flags(
        &adjacent_spill_cells(spill_load(W9, X29, -24)),
        SpillSlotViolationKind::ReloadMisalignedWithSpillStore,
    );
}

/// Evidence boundary, not a desired property: a reload shifted by exactly one
/// slot onto ANOTHER spill cell that a same-width spill store wrote on every
/// path reads a well-formed spill value, and the final stream carries no
/// spill-slot identity to tell the two apart. The net cannot reject it; this
/// test pins the gap so a future slot-identity check flips it deliberately.
#[test]
fn known_gap_reload_shifted_onto_another_whole_spill_cell_is_not_detected() {
    let shifted = adjacent_spill_cells(spill_load(X9, X29, -32));
    assert_clean(&shifted);
}

// ---------------------------------------------------------------------------
// A frame-model decline keeps the legacy rule's coverage of flagged reloads
// ---------------------------------------------------------------------------

#[test]
fn frame_model_decline_leaves_flagged_reloads_to_the_legacy_rule() {
    // Frameless and SP-invariant (the legacy shape). The flagged access through
    // x1, which is not a frame address, makes the frame model decline; the
    // flagged reload of [sp,#8] before its only store must still be refuted.
    let f = single_block(
        "decline_keeps_legacy",
        vec![
            spill_load(X10, SP, 8),
            spill_load(X11, X1, 0),
            movz(X9, 1),
            spill_store(X9, SP, 8),
        ],
    );
    assert!(matches!(
        analyze_frame(&f),
        FrameNetOutcome::Declined(DeclineReason::UnresolvedSpillAddress)
    ));
    let violations = check(&f);
    assert_eq!(violations.len(), 1, "{violations:#?}");
    assert_eq!(
        violations[0].kind,
        SpillSlotViolationKind::ReloadWithoutReachingStore
    );
    assert!(evaluate(&f, PostRegallocRecheckMode::Enforce).is_some());
}

// ---------------------------------------------------------------------------
// Malformed public input: extreme frame addresses are a decline, not a panic
// ---------------------------------------------------------------------------

#[test]
fn extreme_frame_addresses_never_panic() {
    // `add x9, sp, #(i64::MAX - 8)` makes x9 a frame address at the top of the
    // i64 range; an 8-byte access at +8 would end past i64::MAX.
    for (offset, flagged) in [(8, false), (8, true), (0, false), (i64::MIN, false)] {
        let sub_min = single_block(
            "sub_i64_min",
            vec![inst(AArch64Opcode::SubRI, vec![r(X9), sp(), imm(i64::MIN)])],
        );
        let _ = analyze_frame(&sub_min);
        let access = |load: bool| {
            let mut i = if load {
                plain_load(X10, X9, offset)
            } else {
                plain_store(X0, X9, offset)
            };
            if flagged {
                i.flags.insert(InstFlags::SPILL_SLOT_ACCESS);
            }
            i
        };
        let f = single_block(
            "extreme_frame_address",
            vec![
                add_ri(X9, X29, 0),
                inst(AArch64Opcode::AddRI, vec![r(X9), sp(), imm(i64::MAX - 8)]),
                access(false),
                access(true),
                plain_load(X11, X9, 7),
                ret(&USES_X0),
            ],
        );
        // A frame access that would end past i64::MAX declines (too large);
        // anything else is modeled. Neither panics.
        match analyze_frame(&f) {
            FrameNetOutcome::Declined(reason) => assert_eq!(reason, DeclineReason::TooLarge),
            FrameNetOutcome::Analyzed { .. } => assert_eq!(offset, 0, "{offset}"),
        }
        let _ = check(&f);
    }
}

// ---------------------------------------------------------------------------
// 128-bit (Q-register) spill cells and the V8-V15 upper halves
// ---------------------------------------------------------------------------

static USES_V0: [PReg; 1] = [trust_cg_ir::aarch64_regs::V0];

fn neon_add(d: PReg, a: PReg, b: PReg) -> MachInst {
    inst(AArch64Opcode::NeonAddV, vec![r(d), r(a), r(b), imm(5)])
}

/// A framed function that keeps two 128-bit values live across a call in
/// 16-byte spill cells: `x29 = CFA-16`, `SP_body = CFA-96`, Q cell A at
/// `[x29,#-32]` (CFA-48..CFA-32) and Q cell B at `[x29,#-48]`
/// (CFA-64..CFA-48), directly below the x20/x19 save cell (CFA-32..CFA-16).
fn framed_q_body() -> Vec<MachInst> {
    use trust_cg_ir::aarch64_regs::{V0, V16, V17, V18, V19};
    vec![
        stp_pre(X20, X19, -32),     // 0
        stp(X29, X30, 16),          // 1
        add_fp_sp(16),              // 2: x29 = CFA-16
        sub_sp(64),                 // 3: SP = CFA-96
        plain_load(V18, X0, 0),     // 4: q18 = *x0
        plain_load(V19, X0, 16),    // 5: q19 = *(x0+16)
        spill_store(V18, X29, -32), // 6: cell A
        spill_store(V19, X29, -48), // 7: cell B
        call(&USES_X0),             // 8: clobbers v16-v31
        spill_load(V16, X29, -32),  // 9: reload A
        spill_load(V17, X29, -48),  // 10: reload B
        neon_add(V0, V16, V17),     // 11
        add_sp(64),                 // 12: teardown
        ldp(X29, X30, 16),          // 13
        ldp_post(X20, X19, 32),     // 14
        ret(&USES_V0),              // 15
    ]
}

fn framed_q(name: &str, edit: impl FnOnce(&mut Vec<MachInst>)) -> MachFunction {
    let mut body = framed_q_body();
    edit(&mut body);
    single_block(name, body)
}

#[test]
fn q_spill_cells_are_modeled_and_clean() {
    let stats = assert_clean(&framed_q("q_clean", |_| {}));
    assert_eq!(stats.spill_stores, 2);
    assert_eq!(stats.spill_reloads_checked, 2);
    assert_eq!(stats.calls, 1);
}

#[test]
fn corrupt_deleted_q_spill_store() {
    let f = framed_q("q_delete_store", |b| {
        b.remove(7);
    });
    assert_flags(&f, SpillSlotViolationKind::ReloadWithoutReachingStore);
}

#[test]
fn corrupt_q_reload_shifted_by_half_a_cell_across_two_q_cells() {
    use trust_cg_ir::aarch64_regs::V16;
    // CFA-56..CFA-40: the upper half of cell B and the lower half of cell A,
    // every byte spill-stored, but by two different Q spill stores.
    let f = framed_q("q_half_shift_inside", |b| b[9] = spill_load(V16, X29, -40));
    assert_flags(&f, SpillSlotViolationKind::ReloadMisalignedWithSpillStore);
}

#[test]
fn corrupt_q_reload_half_overlapping_the_callee_save_cell() {
    use trust_cg_ir::aarch64_regs::V16;
    // CFA-40..CFA-24: the upper half of cell A and the x20 save slot.
    let f = framed_q("q_half_overlap_save", |b| b[9] = spill_load(V16, X29, -24));
    assert_flags(&f, SpillSlotViolationKind::ReloadFromNonSpillStore);
}

#[test]
fn corrupt_q_reload_shifted_onto_an_unwritten_cell() {
    use trust_cg_ir::aarch64_regs::V17;
    // CFA-80..CFA-64 is inside the frame but never spill-stored.
    let f = framed_q("q_shift_unwritten", |b| b[10] = spill_load(V17, X29, -64));
    assert_flags(&f, SpillSlotViolationKind::ReloadWithoutReachingStore);
}

#[test]
fn corrupt_q_reload_into_the_wrong_register() {
    use trust_cg_ir::aarch64_regs::V20;
    // The reload lands in v20, so the consumer reads the call-clobbered v16.
    let f = framed_q("q_wrong_register", |b| b[9] = spill_load(V20, X29, -32));
    assert_flags(&f, SpillSlotViolationKind::ClobberedRegisterRead);
}

#[test]
fn corrupt_q_reload_width_differs_from_its_q_spill_store() {
    use trust_cg_ir::aarch64_regs::D16;
    // An 8-byte D reload of a 16-byte Q spill cell ...
    let narrow = framed_q("q_reload_as_d", |b| b[9] = spill_load(D16, X29, -32));
    assert_flags(
        &narrow,
        SpillSlotViolationKind::ReloadMisalignedWithSpillStore,
    );
    // ... and a Q reload of a cell two 8-byte D spill stores wrote.
    let split = framed_q("q_from_two_d_stores", |b| {
        b[6] = spill_store(D8, X29, -32);
        b.insert(7, spill_store(D9, X29, -24));
    });
    assert_flags(
        &split,
        SpillSlotViolationKind::ReloadMisalignedWithSpillStore,
    );
}

/// Evidence boundary, as for 8-byte cells: a Q reload moved by one whole cell
/// onto the other Q cell reads a well-formed Q spill value, and the final
/// stream carries no slot identity to tell them apart.
#[test]
fn known_gap_q_reload_shifted_onto_the_other_whole_q_cell_is_not_detected() {
    use trust_cg_ir::aarch64_regs::V16;
    assert_clean(&framed_q("q_whole_shift", |b| {
        b[9] = spill_load(V16, X29, -48)
    }));
}

/// A 128-bit value kept in V8 across the call instead of being spilled: the
/// low half survives (V8's D view is callee-saved), the upper half does not.
fn q_value_in_v8_across_call(read_after: MachInst) -> MachFunction {
    use trust_cg_ir::aarch64_regs::V8;
    single_block(
        "q_in_v8",
        vec![
            stp_pre(D8, D9, -32),
            stp(X29, X30, 16),
            add_fp_sp(16),
            plain_load(V8, X0, 0),
            call(&USES_X0),
            read_after,
            ldp(X29, X30, 16),
            ldp_post(D8, D9, 32),
            ret(&USES_V0),
        ],
    )
}

#[test]
fn corrupt_q_value_kept_in_v8_across_a_call_reads_a_clobbered_upper_half() {
    use trust_cg_ir::aarch64_regs::{V0, V8};
    let f = q_value_in_v8_across_call(neon_add(V0, V8, V8));
    assert_flags(&f, SpillSlotViolationKind::UpperHalfClobberedRead);
    // A 128-bit spill store of it after the call carries the clobbered half.
    let stored = q_value_in_v8_across_call(spill_store(V8, SP, 0));
    assert!(kinds(&stored).contains(&SpillSlotViolationKind::UpperHalfClobberedRead));
}

#[test]
fn v8_low_half_and_redefined_q_after_a_call_are_not_upper_half_reads() {
    use trust_cg_ir::aarch64_regs::{D0, V0, V8};
    // The D view (the callee-saved low half) survives the call.
    let low = q_value_in_v8_across_call(inst(AArch64Opcode::FaddRR, vec![r(D0), r(D8), r(D8)]));
    assert!(!kinds(&low).contains(&SpillSlotViolationKind::UpperHalfClobberedRead));
    // Redefining v8 after the call (here by a Q load) ends the clobber.
    let redefined = single_block(
        "q_v8_redefined",
        vec![
            stp_pre(D8, D9, -32),
            stp(X29, X30, 16),
            add_fp_sp(16),
            call(&USES_X0),
            plain_load(V8, X19, 0),
            neon_add(V0, V8, V8),
            ldp(X29, X30, 16),
            ldp_post(D8, D9, 32),
            ret(&USES_V0),
        ],
    );
    let found = kinds(&redefined);
    assert!(
        !found.contains(&SpillSlotViolationKind::UpperHalfClobberedRead),
        "{found:?}"
    );
}

#[test]
fn upper_half_clobber_merges_across_paths() {
    use trust_cg_ir::aarch64_regs::{V0, V8};
    // entry -> {call arm, plain arm} -> join reads q8: the call arm leaves the
    // upper half clobbered on one path, which is enough.
    let mut f = MachFunction::new("q_v8_diamond".to_string(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let call_arm = f.create_block();
    let plain_arm = f.create_block();
    let join = f.create_block();
    push(
        &mut f,
        entry,
        vec![
            stp_pre(D8, D9, -32),
            stp(X29, X30, 16),
            add_fp_sp(16),
            plain_load(V8, X0, 0),
        ],
    );
    push(&mut f, call_arm, vec![call(&USES_X0)]);
    push(&mut f, plain_arm, vec![movz(X1, 0)]);
    push(
        &mut f,
        join,
        vec![
            neon_add(V0, V8, V8),
            ldp(X29, X30, 16),
            ldp_post(D8, D9, 32),
            ret(&USES_V0),
        ],
    );
    f.add_edge(entry, call_arm);
    f.add_edge(entry, plain_arm);
    f.add_edge(call_arm, join);
    f.add_edge(plain_arm, join);
    assert_flags(&f, SpillSlotViolationKind::UpperHalfClobberedRead);
}

/// The derivation `written_upper_bits` replaced: operand roles for every
/// instruction. The gated version must return the same mask for every shape.
fn written_upper_bits_ungated(inst: &MachInst, shape: &MemShape) -> u8 {
    let roles = crate::post_ra_reaching_def::operand_roles(inst);
    let mut bits = 0u8;
    for (pos, operand) in inst.operands.iter().enumerate() {
        if let MachOperand::PReg(p) = operand
            && roles.get(pos).is_some_and(|role| role.is_def())
        {
            bits |= fpr_upper_bit(*p);
        }
    }
    if let MemShape::Access(access) = shape
        && access.is_load
    {
        for &data in &access.data {
            bits |= fpr_upper_bit(data);
        }
    }
    for &p in inst.implicit_defs {
        bits |= fpr_upper_bit(p);
    }
    bits
}

#[test]
fn written_upper_bits_equals_the_ungated_derivation() {
    use trust_cg_ir::aarch64_regs::{D10, S8, V0, V8, V9, V10, V15, V16};
    let cases = vec![
        // GPR-only forms (the overwhelming majority): no role derivation.
        add_rr(X9, X10, X11),
        add_ri(X9, X10, 16),
        movz(X1, 7),
        spill_store(X19, X29, -16),
        spill_load(X19, X29, -16),
        plain_load(X9, X0, 8),
        stp(X29, X30, 16),
        ldp(X29, X30, 16),
        // V8-V15 definitions in every view, as a destination and as loaded data.
        neon_add(V8, V9, V10),
        neon_add(V0, V8, V8),
        neon_add(V15, V16, V16),
        neon_add(V16, V8, V15),
        inst(AArch64Opcode::FaddRR, vec![r(D8), r(D9), r(D10)]),
        inst(AArch64Opcode::FaddRR, vec![r(S8), r(S8), r(S8)]),
        plain_load(V8, X0, 0),
        plain_load(V16, X0, 0),
        spill_load(V9, X29, -32),
        spill_store(V9, X29, -32),
        ldp(D8, D9, 16),
        stp(D8, D9, 16),
        ldp_post(D8, D9, 32),
        stp_pre(D8, D9, -32),
    ];
    let mut nonzero = 0;
    for inst in &cases {
        let shape = decode_memory(inst);
        let gated = Analyzer::written_upper_bits(inst, &shape);
        assert_eq!(
            gated,
            written_upper_bits_ungated(inst, &shape),
            "{:?} {:?}",
            inst.opcode,
            inst.operands
        );
        nonzero += usize::from(gated != 0);
    }
    // The comparison is not vacuous: V8-V15 definitions set bits.
    assert!(nonzero >= 6, "{nonzero}");
}

#[test]
fn a_site_renders_as_the_eager_location_string_did() {
    let site = Site {
        block: 3,
        pos: 17,
        opcode: AArch64Opcode::LdrRI,
    };
    assert_eq!(
        site.to_string(),
        format!("block {} inst #{} ({:?})", 3, 17, AArch64Opcode::LdrRI)
    );
    assert_eq!(site.to_string(), "block 3 inst #17 (LdrRI)");
}

/// The `merge_cells` this file shipped before the ordered sweep, verbatim: a
/// sort of every bound and a `cell_covering` range search per elementary
/// interval. The sweep must produce the same map for every pair of maps.
fn merge_cells_reference(a: &Cells, b: &Cells) -> Cells {
    if a == b {
        return a.clone();
    }
    let mut bounds: Vec<i64> = Vec::with_capacity(2 * (a.len() + b.len()) + 1);
    for (&start, cell) in a.iter().chain(b.iter()) {
        bounds.push(start);
        bounds.push(cell.end);
    }
    bounds.push(0);
    bounds.sort_unstable();
    bounds.dedup();
    let mut out = Cells::new();
    let mut i = 0;
    while i + 1 < bounds.len() {
        let lo = bounds[i];
        let hi = bounds[i + 1];
        let ca = cell_covering(a, lo);
        let cb = cell_covering(b, lo);
        if ca.is_none() && cb.is_none() {
            i += 1;
            continue;
        }
        if let (Some((sa, xa)), Some((sb, xb))) = (ca, cb)
            && sa == lo
            && sb == lo
            && xa.end == xb.end
        {
            out.insert(
                lo,
                Cell {
                    end: xa.end,
                    kinds: xa.kinds | xb.kinds,
                    val: xa.val.merge(xb.val),
                },
            );
            while i < bounds.len() && bounds[i] < xa.end {
                i += 1;
            }
            continue;
        }
        let ka = ca.map_or_else(|| implicit_kinds(lo, hi), |(_, c)| c.kinds);
        let kb = cb.map_or_else(|| implicit_kinds(lo, hi), |(_, c)| c.kinds);
        let taint = ca.map_or(0, |(_, c)| c.val.taint) | cb.map_or(0, |(_, c)| c.val.taint);
        out.insert(
            lo,
            Cell {
                end: hi,
                kinds: ka | kb,
                val: AbsVal::opaque(taint),
            },
        );
        i += 1;
    }
    out
}

/// Deterministic xorshift64*, so the differential corpus is reproducible.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn random_val(rng: &mut Rng) -> AbsVal {
    let val = match rng.below(4) {
        0 => Val::Frame(rng.below(64) as i64 - 48),
        1 => Val::Const(rng.below(4) as i64),
        2 => Val::Entry(rng.below(64) as u8),
        _ => Val::Opaque,
    };
    AbsVal {
        val,
        taint: rng.below(8) as u8,
    }
}

/// Disjoint, non-empty cells in `[-96, 32)` (straddling the CFA), as the
/// state's `store` / `mark_written` maintain them.
fn random_cells(rng: &mut Rng) -> Cells {
    let mut cells = Cells::new();
    let mut pos = -96 + rng.below(8) as i64;
    while pos < 32 && cells.len() < 12 {
        pos += rng.below(3) as i64 * 4;
        let width = [1, 2, 4, 8, 8, 16][rng.below(6) as usize];
        if pos + width > 32 {
            break;
        }
        cells.insert(
            pos,
            Cell {
                end: pos + width,
                kinds: 1 + rng.below(15) as u8,
                val: random_val(rng),
            },
        );
        pos += width;
    }
    cells
}

/// A variant of `cells` sharing most cells (the common case at a join).
fn perturb(rng: &mut Rng, cells: &Cells) -> Cells {
    let mut out = cells.clone();
    let keys: Vec<i64> = out.keys().copied().collect();
    for key in keys {
        match rng.below(6) {
            0 => {
                out.remove(&key);
            }
            1 => {
                if let Some(cell) = out.get_mut(&key) {
                    cell.kinds |= 1 << rng.below(4);
                    cell.val = random_val(rng);
                }
            }
            2 => {
                // Split a cell in two at an interior byte.
                if let Some(cell) = out.get(&key).cloned()
                    && cell.end - key > 1
                {
                    let mid = key + 1 + rng.below((cell.end - key - 1) as u64) as i64;
                    out.insert(
                        key,
                        Cell {
                            end: mid,
                            ..cell.clone()
                        },
                    );
                    out.insert(mid, cell);
                }
            }
            _ => {}
        }
    }
    out
}

#[test]
fn merge_cells_sweep_equals_the_sorted_bound_reference() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let empty = Cells::new();
    let mut distinct = 0;
    for round in 0..20_000 {
        let a = random_cells(&mut rng);
        let b = if round % 3 == 0 {
            random_cells(&mut rng)
        } else {
            perturb(&mut rng, &a)
        };
        for (x, y) in [(&a, &b), (&b, &a), (&a, &a), (&a, &empty), (&empty, &b)] {
            let swept = merge_cells(x, y);
            assert_eq!(swept, merge_cells_reference(x, y), "a={x:?}\nb={y:?}");
            distinct += usize::from(x != y);
        }
    }
    assert!(distinct > 50_000, "{distinct}");
}

#[test]
fn merge_cells_sweep_handles_bounds_on_and_around_the_cfa() {
    let cell = |end: i64, kinds: u8, val: AbsVal| Cell { end, kinds, val };
    let v = AbsVal::new(Val::Const(1));
    let w = AbsVal::new(Val::Const(2));
    let cases: Vec<(Cells, Cells)> = vec![
        // One map straddles the CFA, the other stops at it.
        (
            Cells::from([(-8, cell(8, K_OTHER, v))]),
            Cells::from([(-8, cell(0, K_SPILL, v))]),
        ),
        // Same interval, different values: the joined value is kept per cell.
        (
            Cells::from([(-16, cell(-8, K_SPILL, v))]),
            Cells::from([(-16, cell(-8, K_SPILL, w))]),
        ),
        // Touching cells in one map, one covering cell in the other.
        (
            Cells::from([(-16, cell(-8, K_SPILL, v)), (-8, cell(0, K_SPILL, w))]),
            Cells::from([(-16, cell(0, K_OTHER, v))]),
        ),
        // Only above the CFA (caller's area) on one side.
        (Cells::from([(0, cell(16, K_OTHER, v))]), Cells::new()),
    ];
    for (a, b) in &cases {
        assert_eq!(merge_cells(a, b), merge_cells_reference(a, b));
        assert_eq!(merge_cells(b, a), merge_cells_reference(b, a));
    }
}

// ---------------------------------------------------------------------------
// The sorted-vector cells and the in-place join against the map they replaced
// ---------------------------------------------------------------------------

/// The ordered-map cell operations this file shipped before the sorted
/// vector, verbatim, as the oracle for `State::store`, `State::load` and
/// `State::mark_written`.
#[derive(Default)]
struct MapCells(std::collections::BTreeMap<i64, Cell>);

impl MapCells {
    fn store(&mut self, addr: i64, width: i64, kinds: u8, val: AbsVal) {
        let end = addr + width;
        let overlapping: Vec<i64> = self
            .0
            .range(..end)
            .rev()
            .take_while(|(_, cell)| cell.end > addr)
            .map(|(&start, _)| start)
            .collect();
        for start in overlapping {
            let Some(cell) = self.0.remove(&start) else {
                continue;
            };
            if start < addr {
                self.0.insert(
                    start,
                    Cell {
                        end: addr,
                        kinds: cell.kinds,
                        val: AbsVal::opaque(cell.val.taint),
                    },
                );
            }
            if cell.end > end {
                self.0.insert(
                    end,
                    Cell {
                        end: cell.end,
                        kinds: cell.kinds,
                        val: AbsVal::opaque(cell.val.taint),
                    },
                );
            }
        }
        self.0.insert(addr, Cell { end, kinds, val });
    }

    fn covering(&self, pos: i64) -> Option<i64> {
        self.0
            .range(..=pos)
            .next_back()
            .filter(|(_, cell)| cell.end > pos)
            .map(|(&start, _)| start)
    }

    fn load(&self, addr: i64, width: i64) -> (u8, Option<AbsVal>) {
        let end = addr + width;
        let mut kinds = 0u8;
        let mut cursor = addr;
        let mut exact = None;
        let lower = self.covering(addr).unwrap_or(addr);
        for (&start, cell) in self.0.range(lower..end) {
            if cell.end <= addr {
                continue;
            }
            if start > cursor {
                kinds |= implicit_kinds(cursor, start);
            }
            kinds |= cell.kinds;
            if start == addr && cell.end == end {
                exact = Some(cell.val);
            }
            cursor = cursor.max(cell.end);
        }
        if cursor < end {
            kinds |= implicit_kinds(cursor, end);
        }
        (kinds, exact)
    }

    fn mark_written(&mut self, lo: i64, hi: i64, kinds: u8) {
        if lo >= hi {
            return;
        }
        let touched: Vec<(i64, Cell)> = self
            .0
            .range(..hi)
            .rev()
            .take_while(|(_, cell)| cell.end > lo)
            .map(|(&start, cell)| (start, cell.clone()))
            .collect();
        for (start, cell) in touched {
            self.0.remove(&start);
            if start < lo {
                self.0.insert(
                    start,
                    Cell {
                        end: lo,
                        kinds: cell.kinds,
                        val: AbsVal::opaque(cell.val.taint),
                    },
                );
            }
            let mid_lo = start.max(lo);
            let mid_hi = cell.end.min(hi);
            self.0.insert(
                mid_lo,
                Cell {
                    end: mid_hi,
                    kinds: cell.kinds | kinds,
                    val: AbsVal::opaque(cell.val.taint),
                },
            );
            if cell.end > hi {
                self.0.insert(
                    hi,
                    Cell {
                        end: cell.end,
                        kinds: cell.kinds,
                        val: AbsVal::opaque(cell.val.taint),
                    },
                );
            }
        }
    }

    fn as_cells(&self) -> Cells {
        self.0
            .iter()
            .map(|(start, cell)| (*start, cell.clone()))
            .collect()
    }
}

#[test]
fn vector_cells_equal_the_ordered_map_on_random_frames() {
    let mut rng = Rng(0x517c_c1b7_2722_0a95);
    let mut loads = 0usize;
    for _frame in 0..4_000 {
        let mut state = State::entry();
        let mut map = MapCells::default();
        for _op in 0..40 {
            // Addresses straddle the CFA; widths are the scalar and pair sizes.
            let addr = rng.below(96) as i64 - 72;
            let width = [1, 2, 4, 8, 8, 16, 16, 32][rng.below(8) as usize];
            match rng.below(4) {
                0 | 1 => {
                    let kinds = 1 + rng.below(15) as u8;
                    let val = random_val(&mut rng);
                    state.store(addr, width, kinds, val);
                    map.store(addr, width, kinds, val);
                }
                2 => {
                    let kinds = 1 << rng.below(4);
                    // An empty range (hi <= lo) is a no-op on both sides.
                    let hi = addr + width - rng.below(3) as i64 * width;
                    state.mark_written(addr, hi, kinds);
                    map.mark_written(addr, hi, kinds);
                }
                _ => {
                    loads += 1;
                    assert_eq!(state.load(addr, width), map.load(addr, width));
                }
            }
            assert_eq!(state.cells, map.as_cells());
            for pos in -80..32 {
                assert_eq!(
                    cell_covering(&state.cells, pos).map(|(start, _)| start),
                    map.covering(pos)
                );
            }
        }
    }
    assert!(loads > 30_000, "{loads}");
}

#[test]
fn in_place_join_equals_the_merge_and_reports_exactly_a_change() {
    let mut rng = Rng(0x2b99_2ddf_a232_49d6);
    let mut changed_joins = 0usize;
    let mut unchanged_joins = 0usize;
    for round in 0..20_000 {
        let mut a = State::entry();
        a.cells = random_cells(&mut rng);
        let mut b = if round % 4 == 0 {
            State::entry()
        } else {
            a.clone()
        };
        b.cells = if round % 3 == 0 {
            random_cells(&mut rng)
        } else {
            perturb(&mut rng, &a.cells)
        };
        for state in [&mut a, &mut b] {
            for _ in 0..rng.below(4) {
                let loc = rng.below(LOCS as u64) as usize;
                state.regs[loc] = random_val(&mut rng);
            }
            if rng.below(3) == 0 {
                state.sp = [None, Some(0), Some(-16), Some(-32)][rng.below(4) as usize];
            }
            state.torn_down = rng.below(2) == 0;
            state.upper_clobbered = rng.below(256) as u8;
        }
        for (x, y) in [(&a, &b), (&b, &a), (&a, &a)] {
            let merged = x.merge(y);
            let mut joined = x.clone();
            let changed = joined.join_from(y);
            assert_eq!(joined, merged);
            assert_eq!(changed, merged != *x);
            if changed {
                changed_joins += 1;
            } else {
                unchanged_joins += 1;
            }
        }
    }
    assert!(changed_joins > 10_000 && unchanged_joins > 10_000);
}
