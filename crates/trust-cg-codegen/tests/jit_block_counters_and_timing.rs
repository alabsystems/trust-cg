// trust-cg-codegen/tests/jit_block_counters_and_timing.rs
// Per-basic-block JIT counters + cycle timing (AArch64, issue #364 Phase 3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Covers the public API landed for issue #364, Phase 3
// `BlockCountsAndTiming`:
// - `ProfileHookMode::BlockCountsAndTiming` enables one
//   `{count, total_cycles}` cell per basic block plus a single buffer-wide
//   `TimingState`.
// - `ExecutableBuffer::block_timing(name, BlockId)` returns the
//   `(count, total_cycles)` tuple for a specific block.
// - `ExecutableBuffer::block_timings(name)` enumerates every
//   `(block_id, count, total_cycles)` tuple for a function.
// - `ExecutableBuffer::block_count(name, BlockId)` / `block_counts(name)`
//   keep working in parallel with the timing-aware storage — the
//   read-side API does not care which mode compiled the function.
// - `ExecutableBuffer::get_profile(name)` / `entry_count(name)` continue to
//   return the entry block's counter (so the stable #478 API is
//   preserved even under timing mode).
//
// Fixture (same diamond as `jit_block_counters.rs`): if/else on X0 == 0,
// layout order [entry, else, then, join]. Calling with alternating
// arguments (non-zero / zero) produces these per-block counts for N=100
// iterations: entry=100, else=50, then=50, join=100.
//
// For cycle timing, the attribution model (see `TimingState` docs) is
// "first block entered under buffer contributes 0 cycles; each subsequent
// block attributes the delta from its entry back to the previous block's
// total_cycles". On a diamond run N times, the timing surface as a whole
// must accumulate nonzero cycles. Individual short blocks may still land
// on the same virtual-counter tick and report 0 on a fast core, so the
// stable invariant is aggregate timing, not per-cell `> 0`.
//
// Part of #364

#[cfg(target_arch = "aarch64")]
use std::collections::HashMap;
#[cfg(target_arch = "aarch64")]
use trust_cg_codegen::jit::{JitCompiler, JitConfig, ProfileHookMode};
#[cfg(target_arch = "aarch64")]
use trust_cg_codegen::pipeline::resolve_branches;
#[cfg(target_arch = "aarch64")]
use trust_cg_ir::function::{JumpTableData, MachFunction, Signature, Type};
#[cfg(target_arch = "aarch64")]
use trust_cg_ir::inst::{AArch64Opcode, MachInst};
#[cfg(target_arch = "aarch64")]
use trust_cg_ir::operand::MachOperand;
#[cfg(target_arch = "aarch64")]
use trust_cg_ir::regs::{X0, X1, X2, X3};
#[cfg(target_arch = "aarch64")]
use trust_cg_ir::types::BlockId;

/// Build the canonical if/else diamond — same fixture shape as
/// `jit_block_counters.rs` but lifted here so the two suites can evolve
/// independently.
#[cfg(target_arch = "aarch64")]
fn build_diamond() -> MachFunction {
    let sig = Signature::new(vec![Type::I64], vec![Type::I64]);
    let mut func = MachFunction::new("diamond_t".to_string(), sig);

    let entry = func.entry;
    let else_b = func.create_block();
    let then_b = func.create_block();
    let join_b = func.create_block();

    // entry: CMP X0, #0 ; B.EQ then
    let cmp = MachInst::new(
        AArch64Opcode::CmpRI,
        vec![MachOperand::PReg(X0), MachOperand::Imm(0)],
    );
    let cmp_id = func.push_inst(cmp);
    func.append_inst(entry, cmp_id);

    let beq = MachInst::new(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(0x0), // EQ
            MachOperand::Block(then_b),
        ],
    );
    let beq_id = func.push_inst(beq);
    func.append_inst(entry, beq_id);

    // else: MOVZ X0, #77 ; B join
    let mov_77 = MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(X0), MachOperand::Imm(77)],
    );
    let mov_77_id = func.push_inst(mov_77);
    func.append_inst(else_b, mov_77_id);

    let b_join = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(join_b)]);
    let b_join_id = func.push_inst(b_join);
    func.append_inst(else_b, b_join_id);

    // then: MOVZ X0, #11 (falls through to join)
    let mov_11 = MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(X0), MachOperand::Imm(11)],
    );
    let mov_11_id = func.push_inst(mov_11);
    func.append_inst(then_b, mov_11_id);

    // join: RET
    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret);
    func.append_inst(join_b, ret_id);

    // Exact semantic CFG, including layout fallthroughs. Keep predecessor
    // metadata in lock-step via the canonical edge helper.
    func.add_edge(entry, else_b);
    func.add_edge(entry, then_b);
    func.add_edge(else_b, join_b);
    func.add_edge(then_b, join_b);

    resolve_branches(&mut func).expect("valid counter fixture must resolve branches");
    func
}

#[cfg(target_arch = "aarch64")]
fn build_switch3() -> MachFunction {
    let sig = Signature::new(vec![Type::I64], vec![Type::I64]);
    let mut func = MachFunction::new("switch3_t".to_string(), sig);

    let entry = func.entry;
    let case_0 = func.create_block();
    let case_1 = func.create_block();
    let case_2 = func.create_block();
    let default_b = func.create_block();
    let end_b = func.create_block();

    let jt_idx = func.jump_tables.len() as u32;
    func.jump_tables.push(JumpTableData {
        min_val: 0,
        targets: vec![case_0, case_1, case_2],
    });

    let cmp = MachInst::new(
        AArch64Opcode::CmpRI,
        vec![MachOperand::PReg(X0), MachOperand::Imm(2)],
    );
    let cmp_id = func.push_inst(cmp);
    func.append_inst(entry, cmp_id);

    let bhi = MachInst::new(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(0x8), // HI
            MachOperand::Block(default_b),
        ],
    );
    let bhi_id = func.push_inst(bhi);
    func.append_inst(entry, bhi_id);

    let adr = MachInst::new(
        AArch64Opcode::Adr,
        vec![MachOperand::PReg(X1), MachOperand::JumpTableIndex(jt_idx)],
    );
    let adr_id = func.push_inst(adr);
    func.append_inst(entry, adr_id);

    let ldrsw = MachInst::new(
        AArch64Opcode::LdrswRO,
        vec![
            MachOperand::PReg(X2),
            MachOperand::PReg(X1),
            MachOperand::PReg(X0),
        ],
    );
    let ldrsw_id = func.push_inst(ldrsw);
    func.append_inst(entry, ldrsw_id);

    let add = MachInst::new(
        AArch64Opcode::AddRR,
        vec![
            MachOperand::PReg(X3),
            MachOperand::PReg(X1),
            MachOperand::PReg(X2),
        ],
    );
    let add_id = func.push_inst(add);
    func.append_inst(entry, add_id);

    let br = MachInst::new(AArch64Opcode::Br, vec![MachOperand::PReg(X3)]);
    let br_id = func.push_inst(br);
    func.append_inst(entry, br_id);

    let m10 = MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(X0), MachOperand::Imm(10)],
    );
    let m10_id = func.push_inst(m10);
    func.append_inst(case_0, m10_id);
    let b0 = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(end_b)]);
    let b0_id = func.push_inst(b0);
    func.append_inst(case_0, b0_id);

    let m20 = MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(X0), MachOperand::Imm(20)],
    );
    let m20_id = func.push_inst(m20);
    func.append_inst(case_1, m20_id);
    let b1 = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(end_b)]);
    let b1_id = func.push_inst(b1);
    func.append_inst(case_1, b1_id);

    let m30 = MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(X0), MachOperand::Imm(30)],
    );
    let m30_id = func.push_inst(m30);
    func.append_inst(case_2, m30_id);
    let b2 = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(end_b)]);
    let b2_id = func.push_inst(b2);
    func.append_inst(case_2, b2_id);

    let m99 = MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(X0), MachOperand::Imm(99)],
    );
    let m99_id = func.push_inst(m99);
    func.append_inst(default_b, m99_id);
    let bd = MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(end_b)]);
    let bd_id = func.push_inst(bd);
    func.append_inst(default_b, bd_id);

    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret);
    func.append_inst(end_b, ret_id);

    // The indirect jump reaches every jump-table case; the bounds branch
    // reaches the default. Every arm then branches to the shared return.
    for target in [case_0, case_1, case_2, default_b] {
        func.add_edge(entry, target);
        func.add_edge(target, end_b);
    }

    resolve_branches(&mut func).expect("valid timing fixture must resolve branches");
    func
}

#[cfg(target_arch = "aarch64")]
#[test]
fn block_timing_diamond_alternating_inputs() {
    let jit = JitCompiler::new(JitConfig {
        profile_hooks: ProfileHookMode::BlockCountsAndTiming,
        ..JitConfig::default()
    });
    let ext: HashMap<String, *const u8> = HashMap::new();
    let buf = jit
        .compile_raw(&[build_diamond()], &ext)
        .expect("compile_raw must succeed with BlockCountsAndTiming on AArch64");

    let diamond: extern "C" fn(u64) -> u64 = unsafe {
        buf.get_fn_bound("diamond_t")
            .expect("typed function pointer must exist")
            .into_inner()
    };

    // Alternate inputs so both arms of the diamond fire.
    const N: u64 = 100;
    let mut even_calls = 0u64;
    let mut odd_calls = 0u64;
    for i in 0..N {
        if i % 2 == 0 {
            even_calls += 1;
            assert_eq!(diamond(0), 11, "even call {} (arg=0) must hit `then`", i);
        } else {
            odd_calls += 1;
            assert_eq!(diamond(i), 77, "odd call {} (arg={}) must hit `else`", i, i);
        }
    }
    assert_eq!(even_calls + odd_calls, N);
    assert_eq!(even_calls, 50);
    assert_eq!(odd_calls, 50);

    // --- Count assertions: identical to the BlockCounts suite.
    //   block 0 (entry) = N
    //   block 1 (else)  = odd_calls
    //   block 2 (then)  = even_calls
    //   block 3 (join)  = N
    assert_eq!(
        buf.block_count("diamond_t", BlockId(0)),
        Some(N),
        "entry block must be entered once per call"
    );
    assert_eq!(
        buf.block_count("diamond_t", BlockId(1)),
        Some(odd_calls),
        "else block must be entered only on non-zero-argument calls"
    );
    assert_eq!(
        buf.block_count("diamond_t", BlockId(2)),
        Some(even_calls),
        "then block must be entered only on zero-argument calls"
    );
    assert_eq!(
        buf.block_count("diamond_t", BlockId(3)),
        Some(N),
        "join block must be entered once per call (every path reaches it)"
    );

    // `block_counts` walks the timing-cells map in Phase 3.
    let mut all_counts: Vec<(u32, u64)> = buf.block_counts("diamond_t");
    all_counts.sort_by_key(|&(bid, _)| bid);
    assert_eq!(
        all_counts,
        vec![(0, N), (1, odd_calls), (2, even_calls), (3, N)]
    );

    // Stable #478 alias surface must still report the entry count.
    assert_eq!(buf.entry_count("diamond_t"), Some(N));
    assert_eq!(
        buf.get_profile("diamond_t")
            .expect("entry profile")
            .call_count,
        N
    );

    // --- Timing assertions.
    //
    // The attribution chain for the diamond (alternating calls):
    //   entry -> {then,else} -> join -> entry -> ... -> entry -> {then,else} -> join
    // First block entered under the buffer contributes 0 cycles (CBZ
    // skips attribution when prev_ts=0). Every subsequent block entry
    // attributes `now - prev_ts` back to the PREVIOUSLY-ENTERED cell.
    //
    // Aggregate timing across the diamond must be nonzero after N=100
    // alternating calls. We deliberately do not require every individual
    // cell to be nonzero: `CNTVCT_EL0` frequency differs across cores and
    // very short blocks can legitimately collapse to a zero delta.
    let entry_tim = buf
        .block_timing("diamond_t", BlockId(0))
        .expect("entry block timing must be present in Phase 3");
    assert_eq!(entry_tim.0, N, "timing cell count must match block_count");

    let else_tim = buf
        .block_timing("diamond_t", BlockId(1))
        .expect("else block timing must be present");
    assert_eq!(else_tim.0, odd_calls);

    let then_tim = buf
        .block_timing("diamond_t", BlockId(2))
        .expect("then block timing must be present");
    assert_eq!(then_tim.0, even_calls);

    let join_tim = buf
        .block_timing("diamond_t", BlockId(3))
        .expect("join block timing must be present");
    assert_eq!(join_tim.0, N);
    let total_cycles = entry_tim.1 + else_tim.1 + then_tim.1 + join_tim.1;
    assert!(
        total_cycles > 0,
        "timing surface must accumulate cycles across N={} alternating calls (entry={}, else={}, then={}, join={})",
        N,
        entry_tim.1,
        else_tim.1,
        then_tim.1,
        join_tim.1
    );

    // block_timings iterator yields all four cells.
    let mut all_tim: Vec<(u32, u64, u64)> = buf.block_timings("diamond_t");
    all_tim.sort_by_key(|&(bid, _, _)| bid);
    assert_eq!(all_tim.len(), 4);
    assert_eq!(all_tim[0].0, 0);
    assert_eq!(all_tim[0].1, N);
    assert_eq!(all_tim[1].0, 1);
    assert_eq!(all_tim[1].1, odd_calls);
    assert_eq!(all_tim[2].0, 2);
    assert_eq!(all_tim[2].1, even_calls);
    assert_eq!(all_tim[3].0, 3);
    assert_eq!(all_tim[3].1, N);
    assert_eq!(
        all_tim.iter().map(|(_, _, cyc)| *cyc).sum::<u64>(),
        total_cycles,
        "iterator surface must match direct block_timing queries"
    );
}

#[cfg(target_arch = "aarch64")]
#[test]
fn block_timing_jump_table_switch_three_cases_and_default() {
    let jit = JitCompiler::new(JitConfig {
        profile_hooks: ProfileHookMode::BlockCountsAndTiming,
        ..JitConfig::default()
    });
    let ext: HashMap<String, *const u8> = HashMap::new();
    let buf = jit
        .compile_raw(&[build_switch3()], &ext)
        .expect("compile_raw must succeed for switch3_t with BlockCountsAndTiming");

    let switch3: extern "C" fn(u64) -> u64 = unsafe {
        buf.get_fn_bound("switch3_t")
            .expect("typed function pointer must exist")
            .into_inner()
    };

    assert_eq!(switch3(0), 10, "case_0 must return 10");
    assert_eq!(switch3(1), 20, "case_1 must return 20");
    assert_eq!(switch3(2), 30, "case_2 must return 30");
    assert_eq!(switch3(3), 99, "selector=3 must fall to default");
    assert_eq!(switch3(100), 99, "far-out selector must fall to default");

    for _ in 0..7 {
        assert_eq!(switch3(1), 20);
    }
    for _ in 0..3 {
        assert_eq!(switch3(0), 10);
    }
    for _ in 0..2 {
        assert_eq!(switch3(4), 99);
    }

    assert_eq!(buf.block_count("switch3_t", BlockId(0)), Some(17), "entry");
    assert_eq!(buf.block_count("switch3_t", BlockId(1)), Some(4), "case_0");
    assert_eq!(buf.block_count("switch3_t", BlockId(2)), Some(8), "case_1");
    assert_eq!(buf.block_count("switch3_t", BlockId(3)), Some(1), "case_2");
    assert_eq!(buf.block_count("switch3_t", BlockId(4)), Some(4), "default");
    assert_eq!(buf.block_count("switch3_t", BlockId(5)), Some(17), "end");
    assert_eq!(buf.entry_count("switch3_t"), Some(17));

    let mut timings = buf.block_timings("switch3_t");
    timings.sort_by_key(|&(bid, _, _)| bid);
    assert_eq!(
        timings
            .iter()
            .map(|&(bid, count, _)| (bid, count))
            .collect::<Vec<_>>(),
        vec![(0, 17), (1, 4), (2, 8), (3, 1), (4, 4), (5, 17)]
    );
    assert!(
        timings.iter().map(|(_, _, cycles)| *cycles).sum::<u64>() > 0,
        "timing-mode switch should accumulate cycles"
    );
}

#[cfg(target_arch = "aarch64")]
#[test]
fn block_timing_unknown_block_returns_none() {
    let jit = JitCompiler::new(JitConfig {
        profile_hooks: ProfileHookMode::BlockCountsAndTiming,
        ..JitConfig::default()
    });
    let ext: HashMap<String, *const u8> = HashMap::new();
    let buf = jit
        .compile_raw(&[build_diamond()], &ext)
        .expect("compile_raw must succeed");

    // Unknown block id within a known function must return None.
    assert_eq!(buf.block_timing("diamond_t", BlockId(99)), None);
    // Unknown function name must likewise return None.
    assert_eq!(buf.block_timing("not_a_function", BlockId(0)), None);
    assert!(buf.block_timings("not_a_function").is_empty());
}

#[cfg(target_arch = "aarch64")]
#[test]
fn block_timing_disabled_mode_yields_no_timing_cells() {
    // With a non-timing profile mode, `block_timing` must return `None`
    // for every block.
    let jit = JitCompiler::new(JitConfig {
        profile_hooks: ProfileHookMode::BlockCounts,
        ..JitConfig::default()
    });
    let ext: HashMap<String, *const u8> = HashMap::new();
    let buf = jit
        .compile_raw(&[build_diamond()], &ext)
        .expect("compile_raw must succeed with BlockCounts");

    for bid in [BlockId(0), BlockId(1), BlockId(2), BlockId(3)] {
        assert_eq!(
            buf.block_timing("diamond_t", bid),
            None,
            "BlockCounts mode must NOT allocate timing cells"
        );
    }
    assert!(buf.block_timings("diamond_t").is_empty());
}

#[cfg(not(target_arch = "aarch64"))]
#[test]
fn block_timing_aarch64_only_placeholder() {
    // Intentionally empty: the timing splice path is AArch64-only in
    // the Phase 3 landing (issue #364). A follow-up will cover x86-64
    // via RDTSC. Keeping this file compiling on non-aarch64 targets
    // makes the `tests/` directory cross-architecture clean.
}
