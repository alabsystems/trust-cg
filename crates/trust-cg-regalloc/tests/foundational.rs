// trust-cg-regalloc/tests/foundational.rs - Foundational regression tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Foundational coverage for the three regalloc subsystems whose
//! correctness underpins JIT'd solver kernels: liveness, linear scan,
//! and copy coalescing, plus phi elimination and trivial-program edge
//! cases. Each test constructs a hand-checkable input and asserts a
//! property that can be verified by inspection of the program.

use std::collections::BTreeMap;

use trust_cg_regalloc::coalesce::{apply_coalescing, coalesce_copies};
use trust_cg_regalloc::linear_scan::LinearScan;
use trust_cg_regalloc::liveness::compute_live_intervals;
use trust_cg_regalloc::machine_types::{
    BlockId, InstFlags, InstId, MachBlock, MachFunction, MachInst, MachOperand, PReg, RegClass,
    VReg,
};
use trust_cg_regalloc::phi_elim::{PSEUDO_COPY, eliminate_phis};
use trust_cg_regalloc::{AllocConfig, AllocStrategy, allocate};

fn vreg(id: u32) -> VReg {
    VReg {
        id,
        class: RegClass::Gpr64,
    }
}

fn def_imm(id: u32, imm: i64) -> MachInst {
    MachInst {
        opcode: 1,
        defs: vec![MachOperand::VReg(vreg(id))],
        uses: vec![MachOperand::Imm(imm)],
        implicit_defs: Vec::new(),
        implicit_uses: Vec::new(),
        flags: InstFlags::default(),
        tied_operands: vec![],
    }
}

fn use_vreg(id: u32) -> MachInst {
    MachInst {
        opcode: 2,
        defs: vec![],
        uses: vec![MachOperand::VReg(vreg(id))],
        implicit_defs: Vec::new(),
        implicit_uses: Vec::new(),
        flags: InstFlags::default(),
        tied_operands: vec![],
    }
}

fn single_block_func(name: &str, insts: Vec<MachInst>, next_vreg: u32) -> MachFunction {
    let inst_ids: Vec<InstId> = (0..insts.len() as u32).map(InstId).collect();
    MachFunction {
        name: name.into(),
        insts,
        blocks: vec![MachBlock {
            insts: inst_ids,
            preds: Vec::new(),
            succs: Vec::new(),
            loop_depth: 0,
        }],
        block_order: vec![BlockId(0)],
        entry_block: BlockId(0),
        next_vreg,
        next_stack_slot: 0,
        stack_slots: BTreeMap::new(),
    }
}

// ---------------------------------------------------------------------------
// Liveness
// ---------------------------------------------------------------------------

#[test]
fn liveness_straightline_3instr_2vreg() {
    // i0: def v0 = 0
    // i1: def v1 = 1
    // i2: use v0, use v1
    let insts = vec![
        def_imm(0, 0),
        def_imm(1, 1),
        MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(vreg(0)), MachOperand::VReg(vreg(1))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        },
    ];
    let func = single_block_func("liveness_straightline", insts, 2);
    let result = compute_live_intervals(&func);

    let iv0 = result.intervals.get(&0).expect("v0 must have an interval");
    let iv1 = result.intervals.get(&1).expect("v1 must have an interval");

    assert!(iv0.is_live_at(0));
    assert!(iv0.is_live_at(1));
    assert!(iv0.is_live_at(2));
    assert!(iv1.is_live_at(1));
    assert!(iv1.is_live_at(2));
    assert!(!iv1.is_live_at(0));

    assert!(iv0.overlaps(iv1));
}

#[test]
fn liveness_dead_after_use_does_not_extend() {
    // i0: def v0 = 0
    // i1: use v0
    // i2: def v1 = 1
    // i3: use v1
    let insts = vec![def_imm(0, 0), use_vreg(0), def_imm(1, 1), use_vreg(1)];
    let func = single_block_func("liveness_dead_after_use", insts, 2);
    let result = compute_live_intervals(&func);

    let iv0 = result.intervals.get(&0).expect("v0 must have an interval");
    let iv1 = result.intervals.get(&1).expect("v1 must have an interval");

    assert!(iv0.is_live_at(0));
    assert!(iv0.is_live_at(1));
    assert!(!iv0.is_live_at(2));
    assert!(!iv0.is_live_at(3));

    assert!(!iv1.is_live_at(0));
    assert!(!iv1.is_live_at(1));
    assert!(iv1.is_live_at(2));
    assert!(iv1.is_live_at(3));

    assert!(!iv0.overlaps(iv1));
}

// ---------------------------------------------------------------------------
// Linear scan / spill correctness
// ---------------------------------------------------------------------------

fn defs_then_uses_func(n: u32) -> MachFunction {
    let mut insts: Vec<MachInst> = (0..n).map(|i| def_imm(i, i as i64)).collect();
    for i in 0..n {
        insts.push(use_vreg(i));
    }
    single_block_func("defs_then_uses", insts, n)
}

#[test]
fn linear_scan_spills_when_pressure_exceeds_pregs() {
    let mut func = defs_then_uses_func(5);
    let mut allocatable = BTreeMap::new();
    allocatable.insert(
        RegClass::Gpr64,
        vec![PReg::new(0), PReg::new(1), PReg::new(2)],
    );

    let config = AllocConfig {
        allocatable_regs: allocatable,
        strategy: AllocStrategy::LinearScan,
        enable_coalescing: false,
        enable_remat: false,
        enable_critical_edge_splitting: false,
        enable_splitting: false,
        enable_spill_code: true,
        enable_spill_slot_reuse: false,
        hints: BTreeMap::new(),
        coalesce_tuning: Default::default(),
    };

    let result = allocate(&mut func, &config).expect("allocation should succeed");

    assert!(
        !result.spills.is_empty(),
        "expected at least one spill with 5 simultaneously-live vregs and 3 pregs"
    );
    assert!(
        result.allocation.len() <= 3,
        "no more allocated vregs than physical registers; got {}",
        result.allocation.len()
    );
}

#[test]
fn linear_scan_no_overlap_in_physical_assignments() {
    let n = 4u32;
    let mut func = defs_then_uses_func(n);
    let mut allocatable = BTreeMap::new();
    allocatable.insert(
        RegClass::Gpr64,
        vec![PReg::new(0), PReg::new(1), PReg::new(2), PReg::new(3)],
    );

    let config = AllocConfig {
        allocatable_regs: allocatable,
        strategy: AllocStrategy::LinearScan,
        enable_coalescing: false,
        enable_remat: false,
        enable_critical_edge_splitting: false,
        enable_splitting: false,
        enable_spill_code: true,
        enable_spill_slot_reuse: false,
        hints: BTreeMap::new(),
        coalesce_tuning: Default::default(),
    };

    let result = allocate(&mut func, &config).expect("allocation should succeed");

    let liveness = compute_live_intervals(&func);
    let mut by_preg: BTreeMap<PReg, Vec<VReg>> = BTreeMap::new();
    for (&v, &p) in &result.allocation {
        by_preg.entry(p).or_default().push(v);
    }

    for (preg, vregs) in &by_preg {
        for i in 0..vregs.len() {
            for j in (i + 1)..vregs.len() {
                let a = vregs[i];
                let b = vregs[j];
                let Some(ia) = liveness.intervals.get(&a.id) else {
                    continue;
                };
                let Some(ib) = liveness.intervals.get(&b.id) else {
                    continue;
                };
                assert!(
                    !ia.overlaps(ib),
                    "vregs {a:?} and {b:?} both assigned {preg:?} but their live intervals overlap"
                );
            }
        }
    }
}

#[test]
fn linear_scan_low_level_api_handles_zero_intervals() {
    let allocatable = BTreeMap::new();
    let mut scanner = LinearScan::new(Vec::new(), &allocatable);
    let result = scanner
        .allocate()
        .expect("zero-interval allocation must succeed");
    assert!(result.allocation.is_empty());
    assert!(result.spills.is_empty());
}

// ---------------------------------------------------------------------------
// Coalescing
// ---------------------------------------------------------------------------

fn copy_inst(dst: u32, src: u32) -> MachInst {
    MachInst {
        opcode: PSEUDO_COPY,
        defs: vec![MachOperand::VReg(vreg(dst))],
        uses: vec![MachOperand::VReg(vreg(src))],
        implicit_defs: Vec::new(),
        implicit_uses: Vec::new(),
        flags: InstFlags::default(),
        tied_operands: vec![],
    }
}

#[test]
fn coalesce_removes_copy_between_non_overlapping_vregs() {
    // i0: def v0 = 0
    // i1: use v0           (v0 dies here)
    // i2: v1 = copy v0     (non-overlapping with the later def)
    // i3: use v1
    let insts = vec![def_imm(0, 0), use_vreg(0), copy_inst(1, 0), use_vreg(1)];
    let mut func = single_block_func("coalesce_non_overlap", insts, 2);

    let liveness = compute_live_intervals(&func);
    let mut intervals = liveness.intervals;

    let original_copy_count = func
        .insts
        .iter()
        .filter(|inst| inst.opcode == PSEUDO_COPY)
        .count();
    assert_eq!(original_copy_count, 1);

    let coalesce_result = coalesce_copies(&func, &mut intervals);
    assert!(
        coalesce_result.copies_removed >= 1,
        "at least one non-overlapping copy must be removable, got {}",
        coalesce_result.copies_removed
    );

    apply_coalescing(
        &mut func,
        &coalesce_result.removals,
        &coalesce_result.rewrites,
    );

    let remaining_copies: usize = func
        .blocks
        .iter()
        .flat_map(|b| b.insts.iter())
        .filter(|id| func.insts[id.0 as usize].opcode == PSEUDO_COPY)
        .count();
    assert_eq!(
        remaining_copies, 0,
        "coalescing must eliminate the non-overlapping copy"
    );
}

#[test]
fn coalesce_keeps_copy_between_overlapping_vregs() {
    // i0: def v0 = 0
    // i1: v1 = copy v0
    // i2: use v0, use v1  -- both still live, must not coalesce
    let insts = vec![
        def_imm(0, 0),
        copy_inst(1, 0),
        MachInst {
            opcode: 2,
            defs: vec![],
            uses: vec![MachOperand::VReg(vreg(0)), MachOperand::VReg(vreg(1))],
            implicit_defs: Vec::new(),
            implicit_uses: Vec::new(),
            flags: InstFlags::default(),
            tied_operands: vec![],
        },
    ];
    let func = single_block_func("coalesce_overlap_blocks", insts, 2);

    let liveness = compute_live_intervals(&func);
    let mut intervals = liveness.intervals;
    let result = coalesce_copies(&func, &mut intervals);

    assert_eq!(
        result.copies_removed, 0,
        "overlapping copy source/dest must not be coalesced"
    );
    assert!(result.removals.is_empty());
    assert!(result.rewrites.is_empty());
}

// ---------------------------------------------------------------------------
// Phi elimination
// ---------------------------------------------------------------------------

#[test]
fn phi_elim_two_block_single_phi_lowers_to_copy_in_predecessor() {
    // Block 0 (entry):
    //   i0: def v0 = 0
    //   i1: jump block 1   (terminator)
    // Block 1 (merge with phi):
    //   i2: phi v2 = [v0 from block 0]  -- single-pred phi.
    //   i3: use v2
    let phi_inst = MachInst {
        opcode: 0,
        defs: vec![MachOperand::VReg(vreg(2))],
        uses: vec![MachOperand::VReg(vreg(0))],
        implicit_defs: Vec::new(),
        implicit_uses: Vec::new(),
        flags: InstFlags::IS_PHI,
        tied_operands: vec![],
    };
    let jump = MachInst {
        opcode: 0xBA,
        defs: vec![],
        uses: vec![MachOperand::Block(BlockId(1))],
        implicit_defs: Vec::new(),
        implicit_uses: Vec::new(),
        flags: InstFlags::IS_BRANCH.union(InstFlags::IS_TERMINATOR),
        tied_operands: vec![],
    };

    let insts = vec![def_imm(0, 0), jump, phi_inst, use_vreg(2)];
    let mut func = MachFunction {
        name: "phi_elim_two_block".into(),
        insts,
        blocks: vec![
            MachBlock {
                insts: vec![InstId(0), InstId(1)],
                preds: Vec::new(),
                succs: vec![BlockId(1)],
                loop_depth: 0,
            },
            MachBlock {
                insts: vec![InstId(2), InstId(3)],
                preds: vec![BlockId(0)],
                succs: Vec::new(),
                loop_depth: 0,
            },
        ],
        block_order: vec![BlockId(0), BlockId(1)],
        entry_block: BlockId(0),
        next_vreg: 3,
        next_stack_slot: 0,
        stack_slots: BTreeMap::new(),
    };

    eliminate_phis(&mut func);

    let block0_has_copy_v2_from_v0 = func.blocks[0].insts.iter().any(|id| {
        let inst = &func.insts[id.0 as usize];
        inst.opcode == PSEUDO_COPY
            && inst.defs.first().and_then(MachOperand::as_vreg) == Some(vreg(2))
            && inst.uses.first().and_then(MachOperand::as_vreg) == Some(vreg(0))
    });
    assert!(
        block0_has_copy_v2_from_v0,
        "phi must lower to a PSEUDO_COPY (v2 <- v0) in the predecessor block"
    );

    let block1_has_phi = func.blocks[1].insts.iter().any(|id| {
        let inst = &func.insts[id.0 as usize];
        inst.flags.is_phi()
    });
    assert!(
        !block1_has_phi,
        "phi instruction must be removed from its block after elimination"
    );

    let last_inst_of_block0 = func.blocks[0]
        .insts
        .last()
        .expect("block 0 must have a terminator");
    let last_inst = &func.insts[last_inst_of_block0.0 as usize];
    assert!(
        last_inst.flags.is_terminator() || last_inst.flags.is_branch(),
        "predecessor terminator must remain last; got opcode {:#x}",
        last_inst.opcode
    );
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn allocate_empty_function_returns_trivial_result() {
    let mut func = MachFunction {
        name: "empty".into(),
        insts: Vec::new(),
        blocks: vec![MachBlock {
            insts: Vec::new(),
            preds: Vec::new(),
            succs: Vec::new(),
            loop_depth: 0,
        }],
        block_order: vec![BlockId(0)],
        entry_block: BlockId(0),
        next_vreg: 0,
        next_stack_slot: 0,
        stack_slots: BTreeMap::new(),
    };

    let config = AllocConfig::default_aarch64();
    let result = allocate(&mut func, &config).expect("allocating empty function must succeed");

    assert!(result.allocation.is_empty());
    assert!(result.spills.is_empty());
}

#[test]
fn liveness_empty_function_returns_no_intervals() {
    let func = MachFunction {
        name: "empty_liveness".into(),
        insts: Vec::new(),
        blocks: vec![MachBlock {
            insts: Vec::new(),
            preds: Vec::new(),
            succs: Vec::new(),
            loop_depth: 0,
        }],
        block_order: vec![BlockId(0)],
        entry_block: BlockId(0),
        next_vreg: 0,
        next_stack_slot: 0,
        stack_slots: BTreeMap::new(),
    };

    let result = compute_live_intervals(&func);
    assert!(result.intervals.is_empty());
    assert!(result.inst_numbering.is_empty());
}

#[test]
fn allocate_function_with_only_immediates_has_no_allocations() {
    // No virtual registers at all -- only an immediate-using terminator.
    let insts = vec![MachInst {
        opcode: 0xBA,
        defs: vec![],
        uses: vec![MachOperand::Imm(0)],
        implicit_defs: Vec::new(),
        implicit_uses: Vec::new(),
        flags: InstFlags::IS_TERMINATOR,
        tied_operands: vec![],
    }];
    let mut func = single_block_func("no_vregs", insts, 0);

    let config = AllocConfig::default_aarch64();
    let result = allocate(&mut func, &config).expect("allocating zero-vreg function must succeed");

    assert!(result.allocation.is_empty());
    assert!(result.spills.is_empty());
}
