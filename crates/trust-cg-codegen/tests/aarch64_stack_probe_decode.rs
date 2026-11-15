// Copyright 2026 Andrew Yates | Apache-2.0
//! AArch64 stack-probe decode checks.
//!
//! Frame lowering allocates static local areas in `STACK_PROBE_INTERVAL`
//! steps, each followed by `str xzr, [sp]`, and walks runtime-sized
//! allocations down one interval at a time. These tests encode real frames,
//! decode the bytes with the independent `trust-cg-lift` decoder and execute
//! them in a stack-touch emulator. For every exercised size they require:
//!
//! * no SP decrement moves more than one interval below the lowest address
//!   the frame (or, at worst, its caller) has touched;
//! * the exact probe addresses, the final SP and the returned allocation;
//! * X29 holds the FP-based CFA rule whenever SP moves after the frame
//!   record is saved, so the unwind description stays valid in probe loops.
//!
//! A mutation control removes one probe and requires the check to fail. This
//! is executable evidence for the listed inputs on this decoder and emulator,
//! not a proof over all sizes; host-native guard-page execution is in
//! `e2e_aarch64_stack_probe_native.rs`.

#[path = "common/stack_probe_emulator.rs"]
mod emulator;

use emulator::{ENTRY_SP, INTERVAL, MAX_UNPROBED};
use trust_cg_codegen::frame::{
    self, FrameLayout, STACK_PROBE_INTERVAL, STACK_PROBE_MAX_UNPROBED, STACK_PROBE_MAX_UNROLL,
    StaticStackProbePlan,
};
use trust_cg_codegen::pipeline::{self, OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::function::{
    EhCallSiteEntry, MachFunction, Signature, StackSlot, StackSlotSizeSource, Type,
};
use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::{X0, X1, X19};
use trust_cg_lower::function::{
    BasicBlock, Function as LirFunction, Signature as LirSignature, StackSlotInfo,
};
use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
use trust_cg_lower::types::Type as LirType;

const MIB: u32 = 1 << 20;
/// `str xzr, [sp]`, written from the Arm ARM independently of the encoder.
const PROBE_WORD: u32 = 0xf900_03ff;
const NOP_WORD: u32 = 0xd503_201f;

fn ret(returns: bool) -> MachInst {
    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    if returns {
        ret.with_implicit_uses(&[X0])
    } else {
        ret
    }
}

fn static_frame(local: u32) -> (MachFunction, FrameLayout) {
    let mut func = MachFunction::new(format!("static_{local}"), Signature::new(vec![], vec![]));
    func.alloc_stack_slot(StackSlot::new(local, 16));
    let id = func.push_inst(ret(false));
    func.append_inst(func.entry, id);
    let layout = frame::compute_frame_layout(&func, 0, false);
    assert_eq!(layout.sp_adjustment(), local);
    assert_eq!(layout.callee_saved_area_size, 16);
    (func, layout)
}

/// `x0 = alloca(x1 bytes, align)` after a `local`-byte fixed area.
fn dynamic_frame(local: u32, align: i64) -> (MachFunction, FrameLayout) {
    let mut func = MachFunction::new(
        format!("dynamic_{local}_{align}"),
        Signature::new(vec![Type::I64, Type::I64], vec![Type::I64]),
    );
    if local > 0 {
        func.alloc_stack_slot(StackSlot::new(local, 16));
    }
    for inst in [
        MachInst::new(
            AArch64Opcode::StackAlloc,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(1),
                MachOperand::Imm(align),
            ],
        ),
        ret(true),
    ] {
        let id = func.push_inst(inst);
        func.append_inst(func.entry, id);
    }
    let layout = frame::compute_frame_layout(&func, 0, false);
    assert!(layout.has_dynamic_alloc);
    assert_eq!(layout.sp_adjustment(), local);
    (func, layout)
}

fn lower(mut func: MachFunction, layout: &FrameLayout) -> (MachFunction, Vec<u8>) {
    frame::insert_prologue_epilogue(&mut func, layout).expect("frame insertion");
    pipeline::resolve_branches(&mut func).expect("branch resolution");
    let code = pipeline::encode_function(&func).expect("encoding with decode-check");
    (func, code)
}

fn self_loops(func: &MachFunction) -> usize {
    func.block_order
        .iter()
        .filter(|id| func.blocks[id.0 as usize].succs.contains(id))
        .count()
}

fn assert_clean(run: &emulator::Run, context: &str) {
    assert!(run.violations.is_empty(), "{context}: {:?}", run.violations);
    assert!(
        run.cfa_violations.is_empty(),
        "{context}: {:?}",
        run.cfa_violations
    );
    assert!(run.max_untouched_decrement <= INTERVAL, "{context}");
}

#[test]
fn probe_constants_match_the_llvm_aarch64_inline_scheme() {
    assert_eq!(u64::from(STACK_PROBE_INTERVAL), INTERVAL);
    assert_eq!(u64::from(STACK_PROBE_MAX_UNPROBED), MAX_UNPROBED);
    assert_eq!(STACK_PROBE_MAX_UNROLL, 4);
    let plan = |bytes, followup| StaticStackProbePlan::for_adjustment(bytes, followup);
    for bytes in [0, 16, 1008, 1024] {
        assert_eq!(plan(bytes, false).probe_count(), 0, "{bytes}");
    }
    assert!(plan(1040, false).residual_probe);
    assert_eq!(
        plan(16, true).probe_count(),
        1,
        "a runtime allocation follows"
    );
    assert_eq!(
        plan(0, true).probe_count(),
        0,
        "the callee-saved store touched SP"
    );
    let exact = plan(4096, false);
    assert_eq!(
        (exact.steps, exact.residual, exact.residual_probe),
        (1, 0, false)
    );
    let over = plan(4112, false);
    assert_eq!(
        (over.steps, over.residual, over.residual_probe),
        (1, 16, false)
    );
    assert!(!plan(4 * 4096 + 4080, false).looped);
    assert!(plan(5 * 4096, false).looped);
    let mib = plan(MIB, false);
    assert_eq!((mib.steps, mib.looped, mib.residual), (256, true, 0));
}

#[test]
fn static_frames_probe_every_interval_and_reach_the_exact_sp() {
    for local in [
        16,
        1024,
        1040,
        4080,
        4096,
        4112,
        8192,
        16384,
        16400,
        20480,
        20480 + 2048,
        MIB,
        MIB + 1040,
        3 * MIB + 48,
    ] {
        let (func, layout) = static_frame(local);
        let plan = StaticStackProbePlan::for_layout(&layout);
        let (lowered, code) = lower(func, &layout);
        assert_eq!(self_loops(&lowered), usize::from(plan.looped), "{local}");
        let run = emulator::run(&code, &[]).unwrap_or_else(|e| panic!("{local}: {e}"));
        assert_clean(&run, &format!("static {local}"));

        // Probes: one per interval below the saved frame record, then the
        // residual's when it exceeds the unprobed allowance.
        let top = ENTRY_SP - 16;
        let bottom = top - u64::from(local);
        let mut expected: Vec<u64> = (1..=u64::from(plan.steps))
            .map(|k| top - k * INTERVAL)
            .collect();
        if plan.residual_probe {
            expected.push(bottom);
        }
        assert_eq!(run.probes, expected, "{local}");
        assert_eq!(run.min_sp, bottom, "{local}: final SP");
        assert!(
            run.lowest_touch - run.min_sp <= MAX_UNPROBED,
            "{local}: {} bytes left unprobed above the final SP",
            run.lowest_touch - run.min_sp
        );
        if local <= STACK_PROBE_MAX_UNPROBED {
            assert!(run.probes.is_empty(), "{local}: no probe at or below 1 KiB");
        }
    }
}

#[test]
fn named_static_frames_have_the_llvm_shape() {
    let probes = |local| {
        let (func, layout) = static_frame(local);
        let (_, code) = lower(func, &layout);
        emulator::run(&code, &[]).unwrap().probes
    };
    let top = ENTRY_SP - 16;
    assert_eq!(probes(4096), vec![top - 4096]);
    assert_eq!(probes(4112), vec![top - 4096]);
    let mib = probes(MIB);
    assert_eq!(mib.len(), 256);
    assert_eq!(mib.last().copied(), Some(top - u64::from(MIB)));
}

#[test]
fn dynamic_allocations_probe_each_interval_and_the_final_sp() {
    // MIB + 32 composes a looped static probe with the runtime loop in one entry.
    for local in [0, 32, 2000, 4128, MIB + 32] {
        for align in [16, 64] {
            let (func, layout) = dynamic_frame(local, align);
            let static_plan = StaticStackProbePlan::for_layout(&layout);
            let (_, code) = lower(func, &layout);
            for n in [
                0u64,
                1,
                16,
                17,
                1024,
                4095,
                4096,
                4097,
                8192,
                12345,
                u64::from(MIB),
                u64::from(MIB) + 8,
            ] {
                let context = format!("local {local} align {align} n {n}");
                let run =
                    emulator::run(&code, &[0, n]).unwrap_or_else(|e| panic!("{context}: {e}"));
                assert_clean(&run, &context);
                let slack = if align > 16 { align as u64 - 1 } else { 0 };
                let bytes = ((n + slack + 15) & !15).max(16);
                let start = ENTRY_SP - 16 - u64::from(local);
                let target = start - bytes;
                assert_eq!(run.min_sp, target, "{context}: final SP");
                assert_eq!(run.lowest_touch, target, "{context}: final SP probed");
                let address = run.result;
                assert_eq!(address % align as u64, 0, "{context}");
                assert!(address >= target && address + n <= start, "{context}");
                let dynamic: Vec<u64> = run.probes[static_plan.probe_count() as usize..].to_vec();
                let mut expected = Vec::new();
                let mut cursor = start;
                while cursor - INTERVAL > target {
                    cursor -= INTERVAL;
                    expected.push(cursor);
                }
                expected.push(target);
                assert_eq!(dynamic, expected, "{context}");
            }
        }
    }
}

#[test]
fn decode_check_rejects_a_frame_with_a_missing_probe() {
    let mutate = |mut code: Vec<u8>, skip: usize| {
        let position = code
            .as_chunks::<4>()
            .0
            .iter()
            .enumerate()
            .filter(|(_, word)| {
                u32::from_le_bytes([word[0], word[1], word[2], word[3]]) == PROBE_WORD
            })
            .nth(skip)
            .map(|(index, _)| index * 4)
            .expect("probe word present");
        code[position..position + 4].copy_from_slice(&NOP_WORD.to_le_bytes());
        code
    };
    // Unrolled static steps, the static loop body and the dynamic loop body.
    for (local, skip) in [(8192, 0), (MIB, 0)] {
        let (func, layout) = static_frame(local);
        let (_, code) = lower(func, &layout);
        let run = emulator::run(&mutate(code, skip), &[]).unwrap();
        assert!(
            !run.violations.is_empty(),
            "static {local}: missing probe not caught"
        );
    }
    let (func, layout) = dynamic_frame(0, 16);
    let (_, code) = lower(func, &layout);
    // The first probe word is the loop step; the second, the final-SP probe.
    let stepless = emulator::run(&mutate(code.clone(), 0), &[0, u64::from(MIB)]).unwrap();
    assert!(
        !stepless.violations.is_empty(),
        "dynamic loop probe not required"
    );
    let finalless = emulator::run(&mutate(code, 1), &[0, 16]).unwrap();
    assert_ne!(
        finalless.lowest_touch, finalless.min_sp,
        "final probe not required"
    );
}

/// Distinct nonzero seeds for X0-X30 (X29/X30 are replaced by the emulator).
fn seeded_registers() -> [u64; 31] {
    std::array::from_fn(|r| 0x5eed_0000_0000_0000 | ((r as u64) << 32) | (r as u64 * 0x0101))
}

/// Registers in `preserved` whose value at RET differs from `seed`.
fn clobbered(
    run: &emulator::Run,
    seed: &[u64; 31],
    preserved: impl IntoIterator<Item = usize>,
) -> Vec<usize> {
    preserved
        .into_iter()
        .filter(|&r| run.registers[r] != seed[r])
        .collect()
}

/// Rewrite the static probe loop's counter (`movz x16, #steps` and
/// `subs x16, x16, #1`) to `to`, keeping the loop otherwise intact.
fn move_probe_counter(mut code: Vec<u8>, to: u32) -> Vec<u8> {
    use trust_cg_lift::disasm::aarch64::{Instruction as Decoded, decode};
    let mut rewritten = 0;
    for word in code.as_chunks_mut::<4>().0 {
        let raw = u32::from_le_bytes([word[0], word[1], word[2], word[3]]);
        let patched = match decode(raw) {
            Ok(Decoded::MoveWide(m)) if m.rd == 16 => (raw & !0x1f) | to,
            Ok(Decoded::AddSubImm(a)) if a.set_flags && a.rd == 16 && a.rn == 16 => {
                (raw & !0x3ff) | (to << 5) | to
            }
            _ => continue,
        };
        word.copy_from_slice(&patched.to_le_bytes());
        rewritten += 1;
    }
    assert_eq!(
        rewritten, 2,
        "one counter materialization and one decrement"
    );
    code
}

#[test]
fn probe_sequences_preserve_argument_platform_and_callee_saved_registers() {
    // Frame lowering may clobber only the IP0/IP1 scratch pair (and the
    // caller-saved temporaries X9-X15). Arguments X0-X7, the indirect-result
    // register X8, the platform register X18 and callee-saved X19-X28 must
    // reach the body unchanged, and the callee-saved ones the caller too. The
    // functions below return immediately, so their RET observes exactly what
    // the prologue, probes, runtime walk and epilogue left behind.
    let seed = seeded_registers();
    for local in [4112, 4 * 4096, 5 * 4096, MIB + 1040] {
        for extra_pair in [false, true] {
            let (mut func, mut layout) = static_frame(local);
            if extra_pair {
                let keep = func.push_inst(MachInst::new(
                    AArch64Opcode::MovR,
                    vec![MachOperand::PReg(X19), MachOperand::PReg(X19)],
                ));
                func.blocks[func.entry.0 as usize].insts.insert(0, keep);
                layout = frame::compute_frame_layout(&func, 0, false);
                assert_eq!(layout.callee_saved_area_size, 32);
            }
            let context = format!("static {local} extra pair {extra_pair}");
            let (_, code) = lower(func, &layout);
            let run = emulator::run_with_registers(&code, seed)
                .unwrap_or_else(|e| panic!("{context}: {e}"));
            assert_clean(&run, &context);
            let lost = clobbered(&run, &seed, (0..=8).chain(18..=28));
            assert!(lost.is_empty(), "{context}: clobbered x{lost:?}");
        }
    }
    for local in [0, 4128, MIB + 32] {
        for align in [16, 64] {
            let (func, layout) = dynamic_frame(local, align);
            let (_, code) = lower(func, &layout);
            for n in [16u64, 5000, u64::from(MIB) + 8] {
                let context = format!("dynamic local {local} align {align} n {n}");
                let mut registers = seed;
                registers[1] = n;
                let run = emulator::run_with_registers(&code, registers)
                    .unwrap_or_else(|e| panic!("{context}: {e}"));
                assert_clean(&run, &context);
                let lost = clobbered(&run, &registers, (1..=8).chain(18..=28));
                assert!(lost.is_empty(), "{context}: clobbered x{lost:?}");
            }
        }
    }

    // Control: the same looped frame with its counter moved to X8 still
    // probes correctly, and only the register check notices.
    let (func, layout) = static_frame(MIB);
    let (_, code) = lower(func, &layout);
    let run = emulator::run_with_registers(&move_probe_counter(code, 8), seed).unwrap();
    assert_clean(&run, "counter in x8");
    assert_eq!(run.probes.len(), 256, "the mutated loop still probes");
    assert_eq!(clobbered(&run, &seed, (0..=8).chain(18..=28)), vec![8]);
}

#[test]
fn direct_lower_relaxation_path_emits_the_same_probed_frames() {
    // `lower::lower_function` computes its own red-zone-enabled layout and
    // resolves branches through branch relaxation instead of the pipeline.
    for local in [4112, MIB] {
        // A callee-saved register keeps the red-zone layout from dropping
        // the frame; X19/X20 sit below the frame record.
        let (mut func, _) = static_frame(local);
        let keep = func.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![MachOperand::PReg(X19), MachOperand::PReg(X19)],
        ));
        func.blocks[func.entry.0 as usize].insts.insert(0, keep);
        let result = trust_cg_codegen::lower::lower_function(&mut func).expect("direct lowering");
        assert_eq!(result.frame_layout.sp_adjustment(), local);
        assert_eq!(result.frame_layout.callee_saved_area_size, 32);
        let run = emulator::run(&result.code, &[]).unwrap();
        assert_clean(&run, &format!("direct static {local}"));
        assert_eq!(run.min_sp, ENTRY_SP - 32 - u64::from(local));
        assert_eq!(run.probes.len() as u32, local / STACK_PROBE_INTERVAL);
    }
    let (mut func, _) = dynamic_frame(0, 16);
    let result = trust_cg_codegen::lower::lower_function(&mut func).expect("direct lowering");
    for n in [16u64, 4097, u64::from(MIB)] {
        let run = emulator::run(&result.code, &[0, n]).unwrap();
        assert_clean(&run, &format!("direct dynamic {n}"));
        assert_eq!(run.lowest_touch, run.min_sp, "direct dynamic {n}");
    }
}

#[test]
fn probe_splits_move_an_eh_call_site_with_its_call() {
    // An invoke block split by the entry's static probe loop and by a runtime
    // allocation ahead of the call: the call site follows the call.
    for (local, runtime) in [(MIB, false), (32, true), (MIB, true)] {
        let mut func = MachFunction::new("eh_move".into(), Signature::new(vec![], vec![]));
        func.eh_metadata.personality = Some("__gxx_personality_v0".into());
        func.alloc_stack_slot(StackSlot::new(local, 16));
        let pad = func.create_block();
        if runtime {
            let alloc = func.push_inst(MachInst::new(
                AArch64Opcode::StackAlloc,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                    MachOperand::Imm(1),
                    MachOperand::Imm(16),
                ],
            ));
            func.append_inst(func.entry, alloc);
        }
        let call = func.push_inst(MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("may_throw".into())],
        ));
        let done = func.push_inst(ret(false));
        func.append_inst(func.entry, call);
        func.append_inst(func.entry, done);
        let pad_ret = func.push_inst(ret(false));
        func.append_inst(pad, pad_ret);
        func.add_edge(func.entry, pad);
        func.eh_metadata.call_sites.push(EhCallSiteEntry {
            call_block: func.entry,
            start_offset: 0,
            length: 0,
            landing_pad_block: Some(pad),
        });
        let layout = frame::compute_frame_layout(&func, 0, false);
        frame::insert_prologue_epilogue(&mut func, &layout).unwrap();
        pipeline::resolve_branches(&mut func).expect("CFG metadata stays consistent");
        let site = func.eh_metadata.call_sites[0].call_block;
        assert_ne!(site, func.entry, "{local} {runtime}");
        assert!(
            func.blocks[site.0 as usize].insts.contains(&call),
            "{local} {runtime}"
        );
        assert!(func.blocks[site.0 as usize].succs.contains(&pad));
        assert_eq!(func.blocks[pad.0 as usize].preds, vec![site]);
    }
}

#[test]
fn looped_static_probe_requires_a_frame_pointer() {
    let (mut func, mut layout) = static_frame(MIB);
    layout.callee_saved_pairs.clear();
    layout.callee_saved_area_size = 0;
    layout.total_frame_size = MIB;
    layout.uses_frame_pointer = false;
    let before = format!("{func:?}");
    let error = frame::insert_prologue_epilogue(&mut func, &layout).unwrap_err();
    assert!(
        error.to_string().contains("requires a frame pointer"),
        "{error}"
    );
    assert_eq!(
        format!("{func:?}"),
        before,
        "refusal must leave the function unchanged"
    );
    // The straight-line form of the same layout stays fully probed.
    let prologue = frame::emit_prologue(&layout);
    assert_eq!(
        prologue
            .iter()
            .filter(|inst| frame::is_stack_probe(inst))
            .count(),
        256
    );
}

#[test]
fn probe_split_refuses_to_separate_an_eh_call_from_its_landing_pad() {
    let mut func = MachFunction::new("eh_split".into(), Signature::new(vec![], vec![]));
    let pad = func.create_block();
    let call = func.push_inst(MachInst::new(
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol("may_throw".into())],
    ));
    let alloc = func.push_inst(MachInst::new(
        AArch64Opcode::StackAlloc,
        vec![
            MachOperand::PReg(X0),
            MachOperand::PReg(X1),
            MachOperand::Imm(1),
            MachOperand::Imm(16),
        ],
    ));
    let done = func.push_inst(ret(false));
    for id in [call, alloc, done] {
        func.append_inst(func.entry, id);
    }
    let pad_ret = func.push_inst(ret(false));
    func.append_inst(pad, pad_ret);
    func.add_edge(func.entry, pad);
    func.eh_metadata.call_sites.push(EhCallSiteEntry {
        call_block: func.entry,
        start_offset: 0,
        length: 0,
        landing_pad_block: Some(pad),
    });
    let layout = frame::compute_frame_layout(&func, 0, false);
    let before = format!("{func:?}");
    let error = frame::insert_prologue_epilogue(&mut func, &layout).unwrap_err();
    assert!(error.to_string().contains("EH-protected"), "{error}");
    assert_eq!(format!("{func:?}"), before);
}

#[test]
fn probe_split_refuses_eh_blocks_whose_call_cannot_follow_the_site() {
    // The split guard has two independent clauses, each pinned here. A block
    // with a protected call on each side of the allocation is refused unsplit
    // by LSDA resolution (exactly one call per protected block); moving the
    // site to the continuation with the second call would silently leave the
    // first call without its landing pad. A protected block whose call does
    // not move (here: no call at all) must not have its site moved either.
    let call =
        |symbol: &str| MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Symbol(symbol.into())]);
    let alloc = || {
        MachInst::new(
            AArch64Opcode::StackAlloc,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(1),
                MachOperand::Imm(16),
            ],
        )
    };
    let shapes: [(&str, Vec<MachInst>); 2] = [
        (
            "calls on both sides",
            vec![
                call("may_throw"),
                alloc(),
                call("may_throw_too"),
                ret(false),
            ],
        ),
        ("no protected call", vec![alloc(), ret(false)]),
    ];
    for (shape, body) in shapes {
        let mut func = MachFunction::new("eh_split_guard".into(), Signature::new(vec![], vec![]));
        func.eh_metadata.personality = Some("__gxx_personality_v0".into());
        let pad = func.create_block();
        for inst in body {
            let id = func.push_inst(inst);
            func.append_inst(func.entry, id);
        }
        let pad_ret = func.push_inst(ret(false));
        func.append_inst(pad, pad_ret);
        func.add_edge(func.entry, pad);
        func.eh_metadata.call_sites.push(EhCallSiteEntry {
            call_block: func.entry,
            start_offset: 0,
            length: 0,
            landing_pad_block: Some(pad),
        });
        let layout = frame::compute_frame_layout(&func, 0, false);
        assert!(layout.has_dynamic_alloc, "{shape}");
        let before = format!("{func:?}");
        let error = frame::insert_prologue_epilogue(&mut func, &layout)
            .expect_err(&format!("{shape}: the split must be refused"));
        assert!(
            error.to_string().contains("EH-protected"),
            "{shape}: {error}"
        );
        assert_eq!(format!("{func:?}"), before, "{shape}");
    }
}

// ---------------------------------------------------------------------------
// Production pipeline (LIR through register allocation, frame lowering,
// layout and branch resolution) at every optimization level.
// ---------------------------------------------------------------------------

fn inst(opcode: Opcode, args: Vec<u32>, results: Vec<u32>) -> Instruction {
    Instruction {
        opcode,
        args: args.into_iter().map(Value).collect(),
        results: results.into_iter().map(Value).collect(),
    }
}

/// `f(x) = x + x` through volatile stores at both ends of a `bytes` slot, or
/// of an `x`-byte runtime slot when `bytes` is `None`.
fn lir_far_end(name: &str, bytes: Option<u32>) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        LirSignature {
            params: vec![LirType::I64],
            returns: vec![LirType::I64],
        },
    );
    func.stack_slots.push(match bytes {
        Some(bytes) => StackSlotInfo::new(bytes, 16),
        None => StackSlotInfo::new_dynamic_with_unit(StackSlotSizeSource::Value(0), 1, 16),
    });
    let volatile_store = || Opcode::VolatileStore {
        ty: LirType::I64,
        align: None,
    };
    let volatile_load = || Opcode::VolatileLoad {
        ty: LirType::I64,
        align: None,
    };
    let constant = |imm, value| {
        inst(
            Opcode::Iconst {
                ty: LirType::I64,
                imm,
            },
            vec![],
            vec![value],
        )
    };
    let mut instructions = vec![inst(Opcode::StackAddr { slot: 0 }, vec![], vec![1])];
    match bytes {
        Some(bytes) => instructions.push(constant(i64::from(bytes) - 8, 3)),
        // Runtime sizes here are at least 8 bytes: the near end is x - 8.
        None => instructions.extend([constant(-8, 2), inst(Opcode::Iadd, vec![2, 0], vec![3])]),
    }
    instructions.extend([
        inst(Opcode::Iadd, vec![1, 3], vec![4]),
        inst(volatile_store(), vec![0, 1], vec![]),
        inst(volatile_store(), vec![0, 4], vec![]),
        inst(volatile_load(), vec![1], vec![5]),
        inst(volatile_load(), vec![4], vec![6]),
        inst(Opcode::Iadd, vec![5, 6], vec![7]),
        inst(Opcode::Return, vec![7], vec![]),
    ]);
    func.blocks.insert(
        Block(0),
        BasicBlock {
            params: vec![(Value(0), LirType::I64)],
            instructions,
            source_locs: vec![],
        },
    );
    func
}

fn pipeline(triple: &str, opt_level: OptLevel) -> Pipeline {
    Pipeline::new(PipelineConfig {
        opt_level,
        target_triple: triple.into(),
        emit_debug: false,
        verify_dispatch: trust_cg_codegen::pipeline::DispatchVerifyMode::Off,
        ..Default::default()
    })
}

const TRIPLES: [&str; 2] = ["aarch64-apple-darwin", "aarch64-unknown-linux-gnu"];
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

#[test]
fn production_static_frames_are_probed_at_every_level() {
    for triple in TRIPLES {
        for level in LEVELS {
            for bytes in [4096, 4112, MIB, 3 * MIB / 2] {
                let context = format!("{triple} {level:?} {bytes}");
                let prepared = pipeline(triple, level)
                    .prepare_function(&lir_far_end("far_end", Some(bytes)))
                    .unwrap_or_else(|e| panic!("{context}: {e:?}"));
                let code = pipeline::encode_function(&prepared).unwrap();
                let run =
                    emulator::run(&code, &[0x5a]).unwrap_or_else(|e| panic!("{context}: {e}"));
                assert_clean(&run, &context);
                assert_eq!(run.result, 0xb4, "{context}");
                assert!(ENTRY_SP - run.min_sp >= u64::from(bytes) + 16, "{context}");
                assert!(
                    run.probes.len() as u64 >= u64::from(bytes) / INTERVAL,
                    "{context}: {} probes",
                    run.probes.len()
                );
            }
        }
    }
}

#[test]
fn production_runtime_allocations_are_probed_at_every_level() {
    for triple in TRIPLES {
        for level in LEVELS {
            let context = format!("{triple} {level:?}");
            let prepared = pipeline(triple, level)
                .prepare_function(&lir_far_end("far_end_dynamic", None))
                .unwrap_or_else(|e| panic!("{context}: {e:?}"));
            let code = pipeline::encode_function(&prepared).unwrap();
            for n in [8u64, 16, 4096, 4104, 65536, u64::from(MIB) + 8] {
                let run =
                    emulator::run(&code, &[n]).unwrap_or_else(|e| panic!("{context} n {n}: {e}"));
                assert_clean(&run, &format!("{context} n {n}"));
                assert_eq!(run.result, 2 * n, "{context} n {n}");
                assert_eq!(
                    run.lowest_touch, run.min_sp,
                    "{context} n {n}: final SP probed"
                );
                assert!(ENTRY_SP - run.min_sp >= n + 16, "{context} n {n}");
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Object level: the emitted ELF text is the decoded function, and its FDE
// describes the probed frame with the FP-based CFA alone.
// ---------------------------------------------------------------------------

fn u16_at(bytes: &[u8], at: usize) -> u16 {
    u16::from_le_bytes(bytes[at..at + 2].try_into().unwrap())
}
fn u32_at(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
}
fn u64_at(bytes: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap())
}

/// Section bytes by name from an ELF64 little-endian relocatable object.
fn elf_section<'a>(object: &'a [u8], wanted: &str) -> Option<&'a [u8]> {
    assert_eq!(&object[..4], b"\x7fELF");
    let shoff = u64_at(object, 0x28) as usize;
    let shentsize = usize::from(u16_at(object, 0x3a));
    let shnum = usize::from(u16_at(object, 0x3c));
    let shstrndx = usize::from(u16_at(object, 0x3e));
    let header = |index: usize| shoff + index * shentsize;
    let names = u64_at(object, header(shstrndx) + 0x18) as usize;
    (0..shnum).find_map(|index| {
        let at = header(index);
        let name_at = names + u32_at(object, at) as usize;
        let end = object[name_at..].iter().position(|&b| b == 0)?;
        (std::str::from_utf8(&object[name_at..name_at + end]).ok()? == wanted).then(|| {
            let offset = u64_at(object, at + 0x18) as usize;
            let size = u64_at(object, at + 0x20) as usize;
            &object[offset..offset + size]
        })
    })
}

fn uleb(bytes: &[u8], at: &mut usize) -> u64 {
    let (mut value, mut shift) = (0u64, 0);
    loop {
        let byte = bytes[*at];
        *at += 1;
        value |= u64::from(byte & 0x7f) << shift;
        shift += 7;
        if byte & 0x80 == 0 {
            return value;
        }
    }
}

/// `(pc_range, instructions)` of every FDE, parsed from the DWARF `.eh_frame`
/// layout. Only the augmentations the backend emits are accepted.
fn eh_frame_fdes(section: &[u8]) -> Vec<(u64, Vec<u8>)> {
    let pointer_size = |encoding: u8| match encoding & 0x0f {
        0x00 | 0x04 | 0x0c => 8,
        0x02 | 0x0a => 2,
        0x03 | 0x0b => 4,
        other => panic!("pointer encoding {other:#x}"),
    };
    let mut fde_encoding = 0u8;
    let mut fdes = Vec::new();
    let mut at = 0;
    while at + 4 <= section.len() {
        let length = u32_at(section, at) as usize;
        if length == 0 {
            break;
        }
        let body = at + 4;
        let end = body + length;
        let id = u32_at(section, body);
        if id == 0 {
            let mut cursor = body + 5;
            let augmentation_end = cursor + section[cursor..].iter().position(|&b| b == 0).unwrap();
            let augmentation = std::str::from_utf8(&section[cursor..augmentation_end]).unwrap();
            cursor = augmentation_end + 1;
            uleb(section, &mut cursor); // code alignment
            uleb(section, &mut cursor); // data alignment (SLEB; skipped)
            uleb(section, &mut cursor); // return register
            if augmentation.starts_with('z') {
                uleb(section, &mut cursor);
                for letter in augmentation.chars().skip(1) {
                    match letter {
                        'R' => {
                            fde_encoding = section[cursor];
                            cursor += 1;
                        }
                        'L' => cursor += 1,
                        'P' => {
                            let encoding = section[cursor];
                            cursor += 1 + pointer_size(encoding);
                        }
                        other => panic!("augmentation {other}"),
                    }
                }
            }
        } else {
            let size = pointer_size(fde_encoding);
            let mut cursor = body + 4 + size;
            let range = match size {
                4 => u64::from(u32_at(section, cursor)),
                8 => u64_at(section, cursor),
                _ => unreachable!(),
            };
            cursor += size;
            let augmentation_length = uleb(section, &mut cursor) as usize;
            cursor += augmentation_length;
            let mut program = section[cursor..end].to_vec();
            while program.last() == Some(&0) {
                program.pop();
            }
            fdes.push((range, program));
        }
        at = end;
    }
    fdes
}

#[test]
fn elf_object_text_is_the_decoded_frame_and_its_fde_needs_no_probe_rows() {
    let triple = "aarch64-unknown-linux-gnu";
    for (name, bytes) in [("elf_static", Some(MIB)), ("elf_dynamic", None)] {
        let lir = lir_far_end(name, bytes);
        let object = pipeline(triple, OptLevel::O0)
            .compile_function(&lir)
            .expect("ELF object (the in-crate reparse gate runs during emission)");
        let text = elf_section(&object, ".text").expect(".text");
        let prepared = pipeline(triple, OptLevel::O0)
            .prepare_function(&lir)
            .unwrap();
        assert_eq!(
            text,
            pipeline::encode_function(&prepared).unwrap(),
            "{name}"
        );
        let run = emulator::run(text, &[4096]).unwrap();
        assert_clean(&run, name);

        let fdes = eh_frame_fdes(elf_section(&object, ".eh_frame").expect(".eh_frame"));
        assert_eq!(fdes.len(), 1, "{name}");
        let (range, program) = &fdes[0];
        assert_eq!(*range, text.len() as u64, "{name}");
        // DW_CFA_def_cfa x29, 16 is the final row: every probe, probe loop
        // and runtime allocation executes after it and needs no CFA change.
        assert!(program.ends_with(&[0x0c, 29, 16]), "{name}: {program:02x?}");
    }
}

#[test]
fn linux_native_probe_objects_build_and_probe_at_every_level() {
    // `e2e_aarch64_stack_probe_native` links these ELF objects only on a
    // Linux host. Build them here with its exact pipeline configuration and
    // arguments so its Linux arm cannot first fail on object generation, and
    // execute each emitted `.text` under the stack-touch emulator.
    for level in LEVELS {
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level: level,
            target_triple: "aarch64-unknown-linux-gnu".into(),
            emit_debug: false,
            ..Default::default()
        });
        for (name, bytes, argument) in [
            ("cg_probe_static", Some(3 * MIB / 2), 21u64),
            ("cg_probe_dynamic", None, 3 << 20),
        ] {
            let context = format!("{level:?} {name}");
            let object = pipeline
                .compile_function(&lir_far_end(name, bytes))
                .unwrap_or_else(|e| panic!("{context}: {e:?}"));
            let text = elf_section(&object, ".text").expect(".text");
            let run = emulator::run(text, &[argument]).unwrap_or_else(|e| panic!("{context}: {e}"));
            assert_clean(&run, &context);
            assert_eq!(run.result, 2 * argument, "{context}");
            let fdes = eh_frame_fdes(elf_section(&object, ".eh_frame").expect(".eh_frame"));
            assert_eq!(fdes.len(), 1, "{context}");
            assert!(fdes[0].1.ends_with(&[0x0c, 29, 16]), "{context}");
        }
    }
}
