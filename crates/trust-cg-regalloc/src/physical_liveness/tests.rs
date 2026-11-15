// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{BlockId, InstFlags, RegAllocBlock, RegAllocInst, RegAllocOperand};

fn instruction(
    defs: &[u16],
    uses: &[u16],
    implicit_defs: &[u16],
    implicit_uses: &[u16],
) -> RegAllocInst {
    RegAllocInst {
        opcode: 123,
        defs: defs
            .iter()
            .map(|&r| RegAllocOperand::PReg(PReg::new(r)))
            .collect(),
        uses: uses
            .iter()
            .map(|&r| RegAllocOperand::PReg(PReg::new(r)))
            .collect(),
        implicit_defs: implicit_defs.iter().map(|&r| PReg::new(r)).collect(),
        implicit_uses: implicit_uses.iter().map(|&r| PReg::new(r)).collect(),
        flags: InstFlags::default(),
        tied_operands: Vec::new(),
    }
}

fn function(instructions: Vec<Vec<RegAllocInst>>, edges: &[&[u32]]) -> RegAllocFunction {
    let mut insts = Vec::new();
    let blocks: Vec<_> = instructions
        .into_iter()
        .enumerate()
        .map(|(b, body)| {
            let first = insts.len();
            insts.extend(body);
            RegAllocBlock {
                insts: (first..insts.len()).map(|i| InstId(i as u32)).collect(),
                // Deliberately absent: the analysis must derive edges from succs.
                preds: Vec::new(),
                succs: edges
                    .get(b)
                    .into_iter()
                    .flat_map(|v| v.iter())
                    .copied()
                    .map(BlockId)
                    .collect(),
                loop_depth: 0,
            }
        })
        .collect();
    RegAllocFunction {
        name: "physical_liveness_worklist".into(),
        insts,
        block_order: (0..blocks.len()).map(|b| BlockId(b as u32)).collect(),
        blocks,
        entry_block: BlockId(0),
        next_vreg: 0,
        next_stack_slot: 0,
        stack_slots: BTreeMap::new(),
    }
}

fn numbering(func: &RegAllocFunction) -> BTreeMap<InstId, u32> {
    (0..func.insts.len())
        .map(|i| (InstId(i as u32), (i as u32) * 3 + 7))
        .collect()
}

fn compare(func: &RegAllocFunction, numbering: &BTreeMap<InstId, u32>) -> (WorkStats, WorkStats) {
    let prefix = BTreeMap::from([(PReg::new(1), vec![91, 17]), (PReg::new(65000), vec![14])]);
    let mut actual = prefix.clone();
    let mut worklist = prefix.clone();
    let mut expected = prefix;
    let fast = reserve(func, numbering, &mut actual);
    reserve_worklist(func, numbering, &mut worklist);
    let scalar = crate::reserve_physical_use_spans_scalar(func, numbering, &mut expected);
    // Compare raw lists, not just sorted sets: preserve existing prefixes,
    // repeated block occurrences, holes, and exact representative map keys.
    assert_eq!(actual, expected, "{}: {func:?}", func.name);
    assert_eq!(
        worklist, expected,
        "general worklist {}: {func:?}",
        func.name
    );
    (fast, scalar)
}

#[test]
fn physical_liveness_single_block_topology_preserves_ignored_edges_and_duplicate_order() {
    let mut func = function(
        vec![
            vec![instruction(&[], &[512], &[], &[])],
            vec![
                instruction(&[1], &[], &[], &[]),
                instruction(&[], &[], &[], &[33]),
            ],
            vec![instruction(&[], &[1000], &[], &[])],
        ],
        &[&[], &[0, 2, u32::MAX], &[]],
    );
    func.block_order = vec![BlockId(u32::MAX), BlockId(1), BlockId(1)];
    func.blocks[1].insts.insert(1, InstId(u32::MAX));
    let mut nums = numbering(&func);
    nums.remove(&InstId(1));
    assert_eq!(single_block_without_backedge(&func), Some(1));
    let (fast, _) = compare(&func, &nums);
    assert_eq!(
        fast.instruction_scans, 6,
        "one discovery and two output walks"
    );
    func.blocks[1].succs.push(BlockId(1));
    assert_eq!(single_block_without_backedge(&func), None);
    compare(&func, &nums);
    func.blocks[1].succs.pop();
    func.block_order.push(BlockId(0));
    assert_eq!(single_block_without_backedge(&func), None);
    compare(&func, &nums);
    func.block_order = vec![BlockId(u32::MAX)];
    assert_eq!(single_block_without_backedge(&func), None);
    compare(&func, &nums);
}

#[test]
fn physical_liveness_singleton_read_before_def_holes_and_repeated_points() {
    for (rep, alias) in [(33, 1), (528, 512), (65535, 65535)] {
        let mut func = function(
            vec![vec![
                instruction(&[], &[], &[], &[]),
                instruction(&[alias], &[], &[], &[]),
                instruction(&[], &[], &[], &[]),
                instruction(&[], &[], &[alias], &[rep]),
                instruction(&[], &[rep], &[], &[]),
                instruction(&[], &[], &[alias], &[]),
                instruction(&[], &[], &[], &[]),
                instruction(&[], &[], &[], &[rep]),
                instruction(&[], &[], &[], &[]),
            ]],
            &[],
        );
        func.insts[5].flags = InstFlags::IS_CALL;
        func.blocks[0].insts.insert(3, InstId(u32::MAX));
        func.block_order = vec![BlockId(0), BlockId(u32::MAX), BlockId(0)];
        let mut nums = numbering(&func);
        nums.remove(&InstId(3)); // An unnumbered RMW must still transfer liveness.
        let (fast, scalar) = compare(&func, &nums);
        assert_eq!(fast.instruction_scans, 27);
        assert!(fast.scratch_payload_bytes < scalar.scratch_payload_bytes);
        let mut output = BTreeMap::new();
        reserve(&func, &nums, &mut output);
        let once = [28, 25, 22, 19, 13, 10];
        assert_eq!(output, BTreeMap::from([(PReg::new(rep), once.repeat(2))]));
    }
}

#[test]
fn physical_liveness_local_mask_cache_bounds_linear_lookup_and_preserves_alias_masks() {
    let reps = [PReg::new(1), PReg::new(65), PReg::new(512), PReg::new(1000)];
    let operands = [1, 33, 65, 97, 129, 166, 198, 512, 528, 1000, 65535, 17];
    let mut masks = LocalMasks::default();
    let mut stats = WorkStats::default();
    for _ in 0..3 {
        for operand in operands {
            let preg = PReg::new(operand);
            let mut actual = Vec::new();
            masks
                .get_or_insert(preg, &reps, &mut stats)
                .for_each(|id| actual.push(id));
            let expected: Vec<_> = reps
                .iter()
                .enumerate()
                .filter_map(|(id, &rep)| allocator_pregs_overlap(preg, rep).then_some(id))
                .collect();
            assert_eq!(actual, expected);
        }
    }
    assert!(masks.index.is_some());
    assert_eq!(masks.values.len(), operands.len());
    assert_eq!(stats.alias_queries, operands.len() * reps.len());
}

#[test]
fn physical_liveness_first_seen_alias_keys_and_arbitrary_encodings() {
    for (first, alias) in [
        (33, 1),
        (1, 33),
        (97, 65),
        (166, 198),
        (528, 512),
        (559, 559),
        (640, 640),
        (u16::MAX, u16::MAX),
    ] {
        let func = function(
            vec![vec![
                instruction(&[], &[first], &[], &[]),
                instruction(&[], &[], &[], &[alias]),
                instruction(&[alias], &[], &[], &[]),
                instruction(&[], &[first], &[], &[]),
            ]],
            &[],
        );
        compare(&func, &numbering(&func));
        let mut output = BTreeMap::new();
        reserve(&func, &numbering(&func), &mut output);
        assert_eq!(
            output.keys().copied().collect::<Vec<_>>(),
            vec![PReg::new(first)]
        );
    }
    // More than two bitset words and values beyond the coalescer's 640 bits.
    let regs: Vec<_> = (1000..1130).collect();
    let func = function(vec![vec![instruction(&[], &regs, &[], &[])]], &[]);
    compare(&func, &numbering(&func));
    let mut output = BTreeMap::new();
    reserve(&func, &numbering(&func), &mut output);
    assert_eq!(output.len(), regs.len());
}

#[test]
fn physical_liveness_read_before_def_and_out_change_without_in_change() {
    for implicit in [false, true] {
        let rmw = if implicit {
            instruction(&[], &[], &[33], &[1])
        } else {
            instruction(&[33], &[1], &[], &[])
        };
        let mut call = instruction(&[], &[], &[0, 1, 33, 97], &[1, 65]);
        call.flags = InstFlags::IS_CALL;
        let func = function(
            vec![
                vec![
                    instruction(&[1], &[], &[], &[]),
                    instruction(&[], &[], &[], &[]),
                ],
                vec![rmw, call],
                vec![instruction(&[], &[1, 97], &[], &[])],
            ],
            &[&[1], &[2], &[]],
        );
        let nums = numbering(&func);
        compare(&func, &nums);
        let mut output = BTreeMap::new();
        reserve(&func, &nums, &mut output);
        assert!(output[&PReg::new(1)].contains(&nums[&InstId(1)]));
    }
    // Force the defining block to run before its successor. Its IN stays
    // empty, but its OUT must acquire the successor's read and reserve the def.
    let mut func = function(
        vec![
            vec![instruction(&[1], &[], &[], &[])],
            vec![instruction(&[], &[1], &[], &[])],
        ],
        &[&[1], &[]],
    );
    func.block_order.reverse();
    compare(&func, &numbering(&func));
    let mut output = BTreeMap::new();
    reserve(&func, &numbering(&func), &mut output);
    assert!(output[&PReg::new(1)].contains(&7));
}

#[test]
fn physical_liveness_diamond_irreducible_disconnected_and_stale_preds() {
    let nop = || instruction(&[], &[], &[], &[]);
    let mut func = function(
        vec![
            vec![nop()],
            vec![nop(), instruction(&[33], &[], &[], &[])],
            vec![nop()],
            vec![instruction(&[], &[1], &[], &[])],
            vec![nop(), instruction(&[], &[], &[], &[512])],
        ],
        &[&[1, 2], &[3], &[3], &[1, 2], &[4]],
    );
    func.block_order = [3, 0, 4, 2, 1].into_iter().map(BlockId).collect();
    for block in &mut func.blocks {
        block.preds = vec![BlockId(u32::MAX)];
    }
    compare(&func, &numbering(&func));
}

#[test]
fn physical_liveness_missing_unlisted_duplicate_and_numbering_holes() {
    let mut func = function(
        vec![
            vec![
                instruction(&[], &[], &[], &[]),
                instruction(&[33], &[], &[], &[]),
            ],
            vec![instruction(&[], &[1], &[], &[])],
            vec![instruction(&[], &[512], &[], &[])],
        ],
        &[&[1, 2, 99], &[0], &[]],
    );
    func.blocks[0].insts.insert(1, InstId(u32::MAX));
    func.block_order = vec![BlockId(99), BlockId(1), BlockId(0), BlockId(1)];
    let mut nums = numbering(&func);
    nums.remove(&InstId(2));
    compare(&func, &nums);
    let mut output = BTreeMap::new();
    reserve(&func, &nums, &mut output);
    assert!(
        !output.contains_key(&PReg::new(512)),
        "unlisted block stays absent"
    );
    assert!(
        output.contains_key(&PReg::new(1)),
        "unnumbered read still discovers key"
    );
    func.block_order.clear();
    compare(&func, &nums);
    output.clear();
    reserve(&func, &nums, &mut output);
    assert!(output.is_empty(), "empty order does not mean all blocks");
}

struct Random(u32);
impl Random {
    fn next(&mut self) -> u32 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 17;
        self.0 ^= self.0 << 5;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        self.next() as usize % n
    }
}

#[test]
fn physical_liveness_random_cfgs_match_independent_scalar() {
    let mut random = Random(0x2026_090d);
    for case in 0..192 {
        let (func, nums) = random_cfg_case(&mut random, case);
        compare(&func, &nums);
    }
}

/// One randomized CFG case: random physical defs/uses/implicit operands over
/// every register band (including SP/ZR, x86 and unassigned encodings), random
/// calls, random and invalid successors and instruction ids, shuffled,
/// truncated, duplicated or invalid `block_order`, and missing numbering.
fn random_cfg_case(random: &mut Random, case: usize) -> (RegAllocFunction, BTreeMap<InstId, u32>) {
    let pool = [
        0, 1, 2, 32, 33, 34, 64, 65, 96, 97, 128, 129, 165, 166, 197, 198, 160, 161, 512, 513, 528,
        529, 544, 559, 639, 640, 1000, 65535,
    ];
    let count = 1 + random.below(15);
    let bodies: Vec<_> = (0..count)
        .map(|_| {
            (0..random.below(9))
                .map(|_| {
                    let mut lanes: [Vec<u16>; 4] = std::array::from_fn(|_| Vec::new());
                    for lane in &mut lanes {
                        for _ in 0..random.below(4) {
                            lane.push(pool[random.below(pool.len())]);
                        }
                    }
                    let mut inst = instruction(&lanes[0], &lanes[1], &lanes[2], &lanes[3]);
                    if random.below(3) == 0 {
                        inst.flags = InstFlags::IS_CALL;
                    }
                    inst.uses.push(RegAllocOperand::Imm(123));
                    inst
                })
                .collect()
        })
        .collect();
    let mut func = function(bodies, &[]);
    func.name = format!("seed_2026090d_case_{case}");
    for block in &mut func.blocks[..count] {
        for _ in 0..random.below(5) {
            block.succs.push(BlockId(random.below(count + 2) as u32));
        }
        if random.below(5) == 0 {
            block.insts.push(InstId(u32::MAX));
        }
    }
    for i in (1..count).rev() {
        func.block_order.swap(i, random.below(i + 1));
    }
    if case.is_multiple_of(3) {
        func.block_order.pop();
    }
    if case.is_multiple_of(5) && !func.block_order.is_empty() {
        func.block_order.push(func.block_order[0]);
    }
    if case.is_multiple_of(7) {
        func.block_order.push(BlockId(u32::MAX));
    }
    let mut nums = numbering(&func);
    for i in 0..func.insts.len() {
        if random.below(5) == 0 {
            nums.remove(&InstId(i as u32));
        }
    }
    (func, nums)
}

/// The validator's independent physical-liveness recomputation
/// (`crate::independent_physical_liveness`) never reports a live point the
/// production reservation map covers, on the same randomized CFG corpus; and
/// each injected `reserve` corruption is detected on part of that corpus.
#[test]
fn independent_liveness_is_covered_by_reserve_and_detects_injected_faults() {
    use super::fault::{ReserveFault, inject};
    let mut random = Random(0x2026_0918);
    let mut detected = [0usize; 2];
    for case in 0..192 {
        let (func, nums) = random_cfg_case(&mut random, case);
        let reserved = crate::implicit_def_reservations(&func, &nums);
        let misses =
            crate::independent_physical_liveness::unreserved_live_points(&func, &nums, &reserved);
        assert!(misses.is_empty(), "case {case}: {misses:?}");
        for (slot, fault) in [
            ReserveFault::DropSuccessorLiveIn,
            ReserveFault::IgnoreImplicitUses,
        ]
        .into_iter()
        .enumerate()
        {
            let corrupted = {
                let _fault = inject(fault);
                crate::implicit_def_reservations(&func, &nums)
            };
            if !crate::independent_physical_liveness::unreserved_live_points(
                &func, &nums, &corrupted,
            )
            .is_empty()
            {
                detected[slot] += 1;
            }
        }
    }
    assert!(
        detected.iter().all(|&count| count > 0),
        "each injected reserve() fault must be detected on the corpus: {detected:?}"
    );
}

#[test]
fn physical_liveness_scan_work_and_scratch_observation() {
    // Fixed source inventory per function; reversed order exercises a slow
    // scalar propagation schedule. Counts are algorithmic work, not timings.
    for registers in [1, 8, 32, 96] {
        let count = 32;
        let mut func = function(
            (0..count)
                .map(|_| (0..8).map(|_| instruction(&[], &[], &[], &[])).collect())
                .collect(),
            &[],
        );
        for (b, block) in func.blocks[..count - 1].iter_mut().enumerate() {
            block.succs.push(BlockId((b + 1) as u32));
        }
        let regs: Vec<_> = (1000..1000 + registers as u16).collect();
        func.insts.last_mut().unwrap().implicit_uses =
            regs.iter().copied().map(PReg::new).collect();
        func.block_order.reverse();
        let (fast, scalar) = compare(&func, &numbering(&func));
        assert_eq!(fast.instruction_scans, func.insts.len() * 3);
        assert!(scalar.instruction_scans > fast.instruction_scans);
        assert!(fast.alias_queries <= registers * registers * 2);
        assert!(
            scalar.alias_queries > 0,
            "scalar comparisons are observed too"
        );
        eprintln!(
            "physical_liveness blocks={count} instructions={} representatives={registers} fast={fast:?} scalar={scalar:?}; scratch is retained payload capacity, excludes output/tree overhead, not RSS",
            func.insts.len()
        );
    }
}

/// Bounded diagnostic micro-measurement, not a performance regression gate.
/// Timing includes both algorithms' observation counters, output allocation,
/// and dropping previous outputs. Input construction and equality assertions
/// are outside the timed regions. It is not whole-pipeline or RSS evidence.
#[test]
#[ignore = "optimized-build timing observation; run --release --ignored --nocapture"]
fn physical_liveness_timing_observation() {
    use std::hint::black_box;
    use std::time::{Duration, Instant};

    if cfg!(debug_assertions) {
        panic!("run this observation with --release");
    }
    const WARMUP_BATCHES: usize = 4;
    const SAMPLES: usize = 9;
    type Analysis =
        fn(&RegAllocFunction, &BTreeMap<InstId, u32>, &mut BTreeMap<PReg, Vec<u32>>) -> WorkStats;

    fn batch(
        analyze: Analysis,
        func: &RegAllocFunction,
        nums: &BTreeMap<InstId, u32>,
        repeats: usize,
    ) -> (Duration, BTreeMap<PReg, Vec<u32>>) {
        assert!(repeats > 0);
        let mut last = BTreeMap::new();
        let start = Instant::now();
        for _ in 0..repeats {
            let mut output = BTreeMap::new();
            let stats = black_box(analyze)(black_box(func), black_box(nums), &mut output);
            black_box(stats);
            black_box(&output);
            last = output;
        }
        (start.elapsed(), last)
    }

    let mut cases = vec![("empty".to_owned(), function(Vec::new(), &[]), 10_000)];
    for representatives in [1, 8, 32] {
        // Real allocator classes: 16 AArch64 GPRs then 16 FPRs. Their 32/64-bit
        // aliases are definitions below, not extra representatives.
        let regs: Vec<_> = (0..16).chain(64..80).take(representatives).collect();
        let aliases: Vec<_> = regs.iter().map(|r| r + 32).collect();
        let mut call = instruction(&[], &[], &aliases, &[]);
        call.flags = InstFlags::IS_CALL;
        let tiny = function(
            vec![vec![
                call.clone(),
                instruction(&[], &[], &[], &[]),
                instruction(&[], &regs, &[], &[]),
            ]],
            &[],
        );
        cases.push((format!("tiny_r{representatives}"), tiny, 512));

        let mut straight = function(
            vec![(0..128).map(|_| instruction(&[], &[], &[], &[])).collect()],
            &[],
        );
        straight.insts[0] = call.clone();
        *straight.insts.last_mut().unwrap() = instruction(&[], &regs, &[], &[]);
        cases.push((format!("straight_r{representatives}"), straight, 64));

        let mut cyclic = function(
            (0..16)
                .map(|_| (0..8).map(|_| instruction(&[], &[], &[], &[])).collect())
                .collect(),
            &[],
        );
        for (b, block) in cyclic.blocks[..15].iter_mut().enumerate() {
            block.succs.push(BlockId((b + 1) as u32));
        }
        cyclic.blocks[0].succs.push(BlockId(2));
        cyclic.blocks[7].succs.extend([BlockId(1), BlockId(2)]);
        cyclic.blocks[14].succs.push(BlockId(4));
        cyclic.insts[0] = call;
        cyclic.insts[60] = instruction(&aliases[..representatives / 2], &[], &[], &[]);
        *cyclic.insts.last_mut().unwrap() = instruction(&[], &[], &[], &regs);
        // Fixed non-RPO order exposes the worklist's propagation independently
        // of the favorable straight-line sweep schedule.
        cyclic.block_order.reverse();
        cases.push((format!("cyclic_r{representatives}"), cyclic, 32));
    }

    eprintln!(
        "physical_liveness timing: optimized instrumented unit functions; warmup_batches={WARMUP_BATCHES} samples={SAMPLES}; six rotating/reversing algorithm orders (dispatch, general worklist, scalar); medians per invocation; includes output allocation/drop and observation counters; no whole-pipeline/RSS claim"
    );
    for (name, func, repeats) in cases {
        let nums = numbering(&func);
        let (fast_stats, scalar_stats) = compare(&func, &nums);
        let mut expected = BTreeMap::new();
        crate::reserve_physical_use_spans_scalar(&func, &nums, &mut expected);
        let mut worklist_output = BTreeMap::new();
        let worklist_stats = reserve_worklist(&func, &nums, &mut worklist_output);
        assert_eq!(worklist_output, expected);
        let algorithms: [Analysis; 3] = [
            reserve,
            reserve_worklist,
            crate::reserve_physical_use_spans_scalar,
        ];
        let mut samples: [Vec<Duration>; 3] = std::array::from_fn(|_| Vec::with_capacity(SAMPLES));
        let orders = [
            [0, 1, 2],
            [2, 1, 0],
            [1, 2, 0],
            [0, 2, 1],
            [2, 0, 1],
            [1, 0, 2],
        ];
        for sample in 0..WARMUP_BATCHES + SAMPLES {
            let order = orders[sample % orders.len()];
            for algorithm in order {
                let (elapsed, output) = batch(algorithms[algorithm], &func, &nums, repeats);
                assert_eq!(
                    output, expected,
                    "{name}, sample={sample}, algorithm={algorithm}"
                );
                if sample >= WARMUP_BATCHES {
                    samples[algorithm].push(elapsed);
                }
            }
        }
        for sample in &mut samples {
            sample.sort_unstable();
        }
        let fast_ns = samples[0][SAMPLES / 2].as_nanos() / repeats as u128;
        let worklist_ns = samples[1][SAMPLES / 2].as_nanos() / repeats as u128;
        let scalar_ns = samples[2][SAMPLES / 2].as_nanos() / repeats as u128;
        eprintln!(
            "physical_liveness timing case={name} blocks={} instructions={} repeats={repeats} median_fast_ns={fast_ns} median_worklist_ns={worklist_ns} median_scalar_ns={scalar_ns} fast={fast_stats:?} worklist={worklist_stats:?} scalar={scalar_stats:?}; retained scratch payload excludes output/tree overhead and is not peak memory",
            func.blocks.len(),
            func.insts.len()
        );
    }
}
