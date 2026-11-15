// trust-cg-verify/cegis_pass_walk_tests.rs - indexed vs direct CEGIS walk facts
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The CEGIS search asks its matchers two structural questions per
//! instruction: how many times the arena reads a vreg, and which constant the
//! block prefix materializes into it. [`DirectWalkFacts`] answers them by
//! scanning, which made the walk quadratic; [`IndexedWalkFacts`] keeps them
//! current. These tests run whole Layer A/B/C searches under both and require
//! the same candidates, verdict order, completion, cache entry, statistics
//! and final function, over randomized functions (including malformed
//! schedules) and a corpus of hand-built and real selected functions.

use super::*;
use trust_cg_ir::function::Signature;

// ---------------------------------------------------------------------------
// Running a search under each kind of facts
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
enum VerdictMode {
    /// A verdict per candidate occurrence, mostly `Equivalent` or
    /// `NotEquivalent`, with rare incomplete outcomes that end the search.
    Mixed(u64),
    AllEquivalent,
    AllNotEquivalent,
}

fn splitmix64(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    x = (x ^ (x >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    x ^ (x >> 31)
}

fn equivalent(proof_hash: u64) -> CegisResult {
    CegisResult::Equivalent {
        proof_hash,
        iterations: 1,
    }
}

fn not_equivalent() -> CegisResult {
    CegisResult::NotEquivalent {
        counterexample: crate::cegis::ConcreteInput::new(),
        found_by_concrete: false,
    }
}

fn verdicts(mode: VerdictMode) -> Box<dyn FnMut(RewriteLayer, InstId) -> CegisResult + Send> {
    let mut occurrences: HashMap<(u8, u32), u64> = HashMap::new();
    Box::new(move |layer, inst_id| match mode {
        VerdictMode::AllEquivalent => equivalent(0x486),
        VerdictMode::AllNotEquivalent => not_equivalent(),
        VerdictMode::Mixed(seed) => {
            let key = (layer as u8, inst_id.0);
            let occurrence = occurrences.entry(key).or_insert(0);
            *occurrence += 1;
            let h = splitmix64(
                seed ^ (u64::from(key.0) << 56) ^ (u64::from(key.1) << 16) ^ *occurrence,
            );
            match h % 100 {
                0..=54 => equivalent(h),
                55..=95 => not_equivalent(),
                96 => CegisResult::Timeout,
                97 => CegisResult::MaxIterationsReached { counterexamples: 0 },
                _ => CegisResult::Error("scripted".to_string()),
            }
        }
    })
}

fn walk_modes(seed: u64) -> Vec<(CegisSuperoptTestHooks, VerdictMode)> {
    vec![
        (Default::default(), VerdictMode::Mixed(seed)),
        (Default::default(), VerdictMode::Mixed(splitmix64(seed))),
        (Default::default(), VerdictMode::AllEquivalent),
        (Default::default(), VerdictMode::AllNotEquivalent),
        (
            CegisSuperoptTestHooks {
                force_layer_a_equal_cost: true,
                ..Default::default()
            },
            VerdictMode::AllEquivalent,
        ),
        (
            CegisSuperoptTestHooks {
                force_layer_b_equal_cost: true,
                ..Default::default()
            },
            VerdictMode::Mixed(seed ^ 0xB),
        ),
        (
            CegisSuperoptTestHooks {
                force_deadline_after_verifications: Some(2),
                ..Default::default()
            },
            VerdictMode::AllEquivalent,
        ),
    ]
}

/// Everything a search produces that must not depend on how facts are kept.
#[derive(Debug, PartialEq)]
struct WalkOutcome {
    events: Vec<String>,
    committed: bool,
    entry: CegisCacheEntry,
    completion: CegisSearchCompletion,
    used_failed_proof_seed: bool,
    stats: String,
    function: String,
}

fn run_walk(
    func: &MachFunction,
    hooks: &CegisSuperoptTestHooks,
    mode: VerdictMode,
    facts: &mut impl WalkFacts,
) -> (WalkOutcome, MachFunction) {
    // The wall-clock budget never elapses here; the deadline hook stands in.
    let config = CegisSuperoptConfig {
        budget_sec: 3_600,
        per_query_ms: 1_000,
        target_triple: "aarch64-apple-darwin".to_string(),
        cpu: "apple-m1".to_string(),
        features: Vec::new(),
        opt_level: 2,
        search_schedule: CegisSearchScheduleIdentity::serial(),
        cache: None,
        trace: None,
    };
    let mut pass = CegisSuperoptPass::new(config).with_test_hooks(hooks.clone());
    pass.test_walk_script = Some(WalkScript {
        verdict: verdicts(mode),
        events: Vec::new(),
    });
    let mut search = func.clone();
    let (committed, entry, completion, used_failed_proof_seed) =
        pass.search_layers(&mut search, facts, None);
    let mut stats = pass.stats().clone();
    stats.solver_ms = 0;
    let outcome = WalkOutcome {
        events: pass.test_walk_script.take().expect("script").events,
        committed,
        entry,
        completion,
        used_failed_proof_seed,
        stats: format!("{stats:?}"),
        function: format!("{search:?}"),
    };
    (outcome, search)
}

fn schedules_repeat_an_id(func: &MachFunction) -> bool {
    func.block_order.iter().any(|&block| {
        let mut seen = HashSet::new();
        func.block(block).insts.iter().any(|id| !seen.insert(*id))
    })
}

fn nonzero_uses(facts: &IndexedWalkFacts) -> Vec<(u32, u64)> {
    let mut uses: Vec<_> = facts
        .uses
        .iter()
        .filter(|(_, count)| **count > 0)
        .map(|(id, count)| (*id, *count))
        .collect();
    uses.sort_unstable();
    uses
}

#[derive(Debug, Default)]
struct Tally {
    functions: usize,
    searches: usize,
    candidates: usize,
    verdicts: usize,
    rewrites: usize,
}

/// Run every mode under both kinds of facts and require identical outcomes.
fn assert_walks_agree(label: &str, func: &MachFunction, seed: u64, tally: &mut Tally) {
    tally.functions += 1;
    let repeats = schedules_repeat_an_id(func);
    for (hooks, mode) in walk_modes(seed) {
        let mut indexed = IndexedWalkFacts::for_search(func);
        let (fast, fast_func) = run_walk(func, &hooks, mode, &mut indexed);
        let (reference, _) = run_walk(func, &hooks, mode, &mut DirectWalkFacts);
        let context = format!("{label} hooks={hooks:?} mode={mode:?}");

        if let Some(index) = fast
            .events
            .iter()
            .zip(&reference.events)
            .position(|(a, b)| a != b)
        {
            panic!(
                "{context}: event {index} differs\n  indexed: {}\n  direct:  {}",
                fast.events[index], reference.events[index]
            );
        }
        assert_eq!(
            fast.events.len(),
            reference.events.len(),
            "{context}: event count"
        );
        assert_eq!(fast.completion, reference.completion, "{context}");
        assert_eq!(fast.committed, reference.committed, "{context}");
        assert_eq!(fast.entry, reference.entry, "{context}");
        assert_eq!(
            fast.used_failed_proof_seed, reference.used_failed_proof_seed,
            "{context}"
        );
        assert_eq!(fast.stats, reference.stats, "{context}");
        assert!(
            fast.function == reference.function,
            "{context}: final functions differ"
        );

        // The indexed use counts must still describe the searched function.
        assert_eq!(
            nonzero_uses(&indexed),
            nonzero_uses(&IndexedWalkFacts::for_search(&fast_func)),
            "{context}: use index drifted from the function"
        );
        if !repeats {
            assert_eq!(
                indexed.direct_fallbacks, 0,
                "{context}: a well-formed schedule must never need a direct scan"
            );
        }

        tally.searches += 1;
        tally.candidates += fast
            .events
            .iter()
            .filter(|event| event.starts_with("candidate"))
            .count();
        tally.verdicts += fast
            .events
            .iter()
            .filter(|event| event.starts_with("verdict"))
            .count();
        tally.rewrites += fast.entry.proven_rewrites.len();
    }
}

// ---------------------------------------------------------------------------
// Randomized functions
// ---------------------------------------------------------------------------

struct TestRng(u64);

impl TestRng {
    fn next(&mut self) -> u64 {
        self.0 = splitmix64(self.0);
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }

    fn pick<T: Copy>(&mut self, items: &[T]) -> T {
        items[self.below(items.len() as u64) as usize]
    }
}

/// Vreg source for one random function: a small shared pool (so reads
/// collide) plus fresh ids for motifs that want a single reader.
struct Regs {
    pool: u32,
    next_fresh: u32,
    classes: HashMap<u32, RegClass>,
}

impl Regs {
    fn class_of(&mut self, rng: &mut TestRng, id: u32) -> RegClass {
        *self.classes.entry(id).or_insert_with(|| {
            rng.pick(&[
                RegClass::Gpr32,
                RegClass::Gpr32,
                RegClass::Gpr32,
                RegClass::Gpr64,
                RegClass::Gpr64,
                RegClass::Fpr64,
            ])
        })
    }

    /// A pool vreg; occasionally the same id under another class.
    fn any(&mut self, rng: &mut TestRng) -> MachOperand {
        let id = rng.below(u64::from(self.pool)) as u32;
        let class = if rng.chance(4) {
            rng.pick(&[RegClass::Gpr32, RegClass::Gpr64])
        } else {
            self.class_of(rng, id)
        };
        MachOperand::VReg(VReg::new(id, class))
    }

    fn fresh(&mut self, class: RegClass) -> VReg {
        let id = self.next_fresh;
        self.next_fresh += 1;
        self.classes.insert(id, class);
        VReg::new(id, class)
    }

    /// A vreg of `class`: fresh, or a pool id that already has that class.
    fn of_class(&mut self, rng: &mut TestRng, class: RegClass) -> VReg {
        if rng.chance(50) {
            let id = rng.below(u64::from(self.pool)) as u32;
            if self.class_of(rng, id) == class {
                return VReg::new(id, class);
            }
        }
        self.fresh(class)
    }
}

fn imm(value: i64) -> MachOperand {
    MachOperand::Imm(value)
}

fn inst(opcode: AArch64Opcode, operands: Vec<MachOperand>) -> MachInst {
    MachInst::new(opcode, operands)
}

fn random_move_wide(rng: &mut TestRng, regs: &mut Regs) -> MachInst {
    let opcode = rng.pick(&[
        AArch64Opcode::Movz,
        AArch64Opcode::Movn,
        AArch64Opcode::Movk,
    ]);
    let dst = regs.any(rng);
    let value = rng.pick(&[0, 1, 5, 0xFF, 0x5555, 0x0F0F, 0xFFFF, 0x1_0000, -1]);
    let mut operands = vec![dst, imm(value)];
    if opcode == AArch64Opcode::Movk || rng.chance(40) {
        operands.push(imm(rng.pick(&[0, 16, 32, 48, 8, 64])));
    }
    inst(opcode, operands)
}

fn random_single(rng: &mut TestRng, regs: &mut Regs) -> MachInst {
    match rng.below(12) {
        0..=2 => random_move_wide(rng, regs),
        3 => inst(
            AArch64Opcode::AddRR,
            vec![regs.any(rng), regs.any(rng), regs.any(rng)],
        ),
        4 | 5 => {
            let mut operands = vec![regs.any(rng), regs.any(rng)];
            if rng.chance(90) {
                operands.push(regs.any(rng));
            }
            inst(AArch64Opcode::AndRR, operands)
        }
        6 => inst(
            AArch64Opcode::MulRR,
            vec![regs.any(rng), regs.any(rng), regs.any(rng)],
        ),
        // Operand 0 of a compare or store is a read, not a definition.
        7 => inst(AArch64Opcode::CmpRR, vec![regs.any(rng), regs.any(rng)]),
        8 => inst(
            AArch64Opcode::StrRI,
            vec![regs.any(rng), regs.any(rng), imm(8)],
        ),
        // A paired load defines operand 1 as well as operand 0.
        9 if rng.chance(50) => inst(
            AArch64Opcode::LdpRI,
            vec![regs.any(rng), regs.any(rng), regs.any(rng), imm(16)],
        ),
        9 => inst(AArch64Opcode::MovR, vec![regs.any(rng), regs.any(rng)]),
        10 => inst(
            rng.pick(&[AArch64Opcode::AddRI, AArch64Opcode::AndRI]),
            vec![regs.any(rng), regs.any(rng), imm(0xFF)],
        ),
        _ => inst(AArch64Opcode::Ret, vec![]),
    }
}

/// `Movz`/`Movn`/`Movk*` materializing a mask into `mask`, then `AndRR`.
fn mask_motif(rng: &mut TestRng, regs: &mut Regs, out: &mut Vec<MachInst>) {
    let class = rng.pick(&[RegClass::Gpr32, RegClass::Gpr64]);
    let mask = if rng.chance(85) {
        regs.fresh(class)
    } else {
        regs.of_class(rng, class)
    };
    let chunk = rng.pick(&[
        0x5555, 0x3333, 0x0F0F, 0x00FF, 0xFFFF, 0x1234, 0x0001, 0x0005,
    ]);
    let first = if rng.chance(80) {
        AArch64Opcode::Movz
    } else {
        AArch64Opcode::Movn
    };
    let mut head = vec![MachOperand::VReg(mask), imm(chunk)];
    if rng.chance(20) {
        head.push(imm(0));
    }
    out.push(inst(first, head));
    let halves = if class == RegClass::Gpr64 { 3 } else { 1 };
    for step in 1..=halves {
        if rng.chance(70) {
            let other = if rng.chance(80) {
                chunk
            } else {
                rng.pick(&[0x5555, 0x00FF, 0x1234])
            };
            out.push(inst(
                AArch64Opcode::Movk,
                vec![MachOperand::VReg(mask), imm(other), imm(16 * step)],
            ));
        }
    }
    if rng.chance(20) {
        out.push(random_single(rng, regs));
    }
    if rng.chance(30) {
        out.push(rewrite_operand_zero(rng, regs, mask));
    }
    let dst = regs.of_class(rng, class);
    let src = regs.of_class(rng, class);
    out.push(inst(
        AArch64Opcode::AndRR,
        vec![
            MachOperand::VReg(dst),
            MachOperand::VReg(src),
            MachOperand::VReg(mask),
        ],
    ));
    if rng.chance(10) {
        // A second reader keeps the mask materialized.
        let dst = regs.fresh(class);
        out.push(inst(
            AArch64Opcode::AndRR,
            vec![
                MachOperand::VReg(dst),
                MachOperand::VReg(src),
                MachOperand::VReg(mask),
            ],
        ));
    }
}

/// An instruction naming `mask` (or its id under another class) between a
/// materializer and its reader: a definition at any position moves the scan,
/// a read (the compare's and the store's operand 0) adds a reader.
fn rewrite_operand_zero(rng: &mut TestRng, regs: &mut Regs, mask: VReg) -> MachInst {
    let target = if rng.chance(20) {
        let other = if mask.class == RegClass::Gpr32 {
            RegClass::Gpr64
        } else {
            RegClass::Gpr32
        };
        MachOperand::VReg(VReg::new(mask.id, other))
    } else {
        MachOperand::VReg(mask)
    };
    match rng.below(9) {
        0 => inst(
            AArch64Opcode::AddRR,
            vec![target, regs.any(rng), regs.any(rng)],
        ),
        1 => inst(AArch64Opcode::CmpRR, vec![target, regs.any(rng)]),
        2 => inst(AArch64Opcode::StrRI, vec![target, regs.any(rng), imm(8)]),
        3 => inst(AArch64Opcode::MovR, vec![target, regs.any(rng)]),
        4 => inst(AArch64Opcode::Movz, vec![target, imm(0x00FF)]),
        5 => inst(AArch64Opcode::Movn, vec![target, imm(0xFFFF)]),
        6 => inst(
            AArch64Opcode::Movk,
            vec![target, imm(rng.pick(&[0x5555, 0x00FF])), imm(16)],
        ),
        // A paired load writing `mask` at operand 1.
        8 => inst(
            AArch64Opcode::LdpRI,
            vec![regs.any(rng), target, regs.any(rng), imm(16)],
        ),
        // A Movk the scan refuses; read with shift 0 it would rebuild a
        // logical immediate.
        _ => {
            let mut operands = vec![target, imm(rng.pick(&[0x5555, 0x00FF, 0x0F0F]))];
            if rng.chance(75) {
                operands.push(imm(rng.pick(&[8, 64, -16])));
            }
            inst(AArch64Opcode::Movk, operands)
        }
    }
}

/// `Movz k` feeding `AddRR`, and `Movz #0` feeding `MulRR` (possibly also an
/// `AddRR`, so a Layer A rewrite leaves the Movz with one reader).
fn constant_motif(rng: &mut TestRng, regs: &mut Regs, out: &mut Vec<MachInst>) {
    let class = rng.pick(&[RegClass::Gpr32, RegClass::Gpr64]);
    let constant = regs.fresh(class);
    let zero = rng.chance(50);
    let mut movz = vec![
        MachOperand::VReg(constant),
        imm(if zero {
            0
        } else {
            rng.pick(&[1, 7, 0xFFF, 0xFFFF])
        }),
    ];
    if rng.chance(20) {
        movz.push(imm(rng.pick(&[0, 16])));
    }
    out.push(inst(AArch64Opcode::Movz, movz));
    let src = regs.of_class(rng, class);
    if zero {
        let dst = regs.fresh(class);
        out.push(inst(
            AArch64Opcode::MulRR,
            vec![
                MachOperand::VReg(dst),
                MachOperand::VReg(src),
                MachOperand::VReg(constant),
            ],
        ));
    }
    if !zero || rng.chance(60) {
        let dst = regs.fresh(class);
        out.push(inst(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::VReg(dst),
                MachOperand::VReg(src),
                MachOperand::VReg(constant),
            ],
        ));
    }
}

fn random_walk_function(seed: u64) -> MachFunction {
    let mut rng = TestRng(seed);
    let mut func = MachFunction::new(format!("walk_facts_{seed}"), Signature::new(vec![], vec![]));
    let mut blocks = vec![func.entry];
    for _ in 0..rng.below(3) {
        blocks.push(func.create_block());
    }
    let pool = 3 + rng.below(10) as u32;
    let mut regs = Regs {
        pool,
        next_fresh: pool,
        classes: HashMap::new(),
    };

    for &block in &blocks {
        for _ in 0..rng.below(24) {
            let mut insts = Vec::new();
            match rng.below(10) {
                0..=3 => mask_motif(&mut rng, &mut regs, &mut insts),
                4 | 5 => constant_motif(&mut rng, &mut regs, &mut insts),
                _ => insts.push(random_single(&mut rng, &mut regs)),
            }
            for inst in insts {
                let id = func.push_inst(inst);
                func.append_inst(block, id);
            }
        }
    }

    // Arena entries no block schedules still count as reads.
    if rng.chance(15) {
        for _ in 0..=rng.below(3) {
            let orphan = random_single(&mut rng, &mut regs);
            func.push_inst(orphan);
        }
    }
    // Malformed layouts: an id scheduled twice in a block or in two blocks,
    // and a block laid out twice.
    if rng.chance(15) {
        let block = rng.pick(&blocks);
        let len = func.block(block).insts.len();
        if len > 0 {
            let id = func.block(block).insts[rng.below(len as u64) as usize];
            let at = rng.below(len as u64 + 1) as usize;
            func.block_mut(block).insts.insert(at, id);
        }
    }
    if rng.chance(10) && blocks.len() > 1 {
        let from = rng.pick(&blocks);
        let to = rng.pick(&blocks);
        if let Some(&id) = func.block(from).insts.first() {
            func.append_inst(to, id);
        }
    }
    if rng.chance(10) {
        let block = rng.pick(&blocks);
        func.block_order.push(block);
    }
    func
}

#[test]
fn indexed_walk_facts_match_direct_scans_on_random_functions() {
    let mut tally = Tally::default();
    for seed in 0..1_500u64 {
        let func = random_walk_function(seed);
        assert_walks_agree(&format!("random seed {seed}"), &func, seed, &mut tally);
    }
    // Guard the generator: the comparison is only as strong as the matches,
    // verdicts and rewrites it actually exercises.
    assert!(tally.candidates > 20_000, "{tally:?}");
    assert!(tally.verdicts > 10_000, "{tally:?}");
    assert!(tally.rewrites > 5_000, "{tally:?}");
}

/// No current layer changes a body it has already passed in a way the scan
/// sees, so the searches above never reach the stale fallback. Drive the
/// walk protocol directly: a schedule that repeats a `Movz`, rewritten into a
/// `Movk` at its second occurrence, must answer as the direct scan does.
#[test]
fn indexed_walk_facts_fall_back_when_a_passed_body_changes() {
    let mut func = MachFunction::new("stale".to_string(), Signature::new(vec![], vec![]));
    let block = func.entry;
    let mask = VReg::new(0, RegClass::Gpr32);
    let movz = func.push_inst(inst(
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(mask), imm(0x00FF)],
    ));
    let movk = func.push_inst(inst(
        AArch64Opcode::Movk,
        vec![MachOperand::VReg(mask), imm(0x0F0F), imm(16)],
    ));
    let and = func.push_inst(inst(
        AArch64Opcode::AndRR,
        vec![
            MachOperand::VReg(VReg::new(1, RegClass::Gpr32)),
            MachOperand::VReg(VReg::new(2, RegClass::Gpr32)),
            MachOperand::VReg(mask),
        ],
    ));
    for id in [movz, movk, movz, and] {
        func.append_inst(block, id);
    }

    let mut facts = IndexedWalkFacts::for_search(&func);
    facts.enter_block(block, &func.block(block).insts);
    facts.passed(movz, func.inst(movz));
    facts.passed(movk, func.inst(movk));
    let rewritten = inst(
        AArch64Opcode::Movk,
        vec![MachOperand::VReg(mask), imm(0x00FF), imm(16)],
    );
    let source = std::mem::replace(func.inst_mut(movz), rewritten);
    facts.replaced(movz, &source, func.inst(movz));
    assert!(facts.stale, "a passed body changed under the scan");
    facts.passed(movz, func.inst(movz));

    let direct = DirectWalkFacts.materialized_wide_const_before(&func, block, and, mask, 32);
    assert_eq!(direct, None, "the scan now meets a Movk before any Movz");
    assert_eq!(
        facts.materialized_wide_const_before(&func, block, and, mask, 32),
        direct
    );
    assert_eq!(facts.direct_fallbacks, 1);
}

// ---------------------------------------------------------------------------
// Corpus: hand-built payload shapes
// ---------------------------------------------------------------------------

struct Builder {
    func: MachFunction,
}

impl Builder {
    fn new(name: &str) -> Self {
        Self {
            func: MachFunction::new(name.to_string(), Signature::new(vec![], vec![])),
        }
    }

    fn vreg(&mut self, class: RegClass) -> VReg {
        VReg::new(self.func.alloc_vreg(), class)
    }

    fn push(&mut self, opcode: AArch64Opcode, operands: Vec<MachOperand>) {
        let entry = self.func.entry;
        let id = self.func.push_inst(MachInst::new(opcode, operands));
        self.func.append_inst(entry, id);
    }

    /// Materialize `value` into a fresh vreg the way ISel does: `Movz` of
    /// the low half-word and a `Movk` for each non-zero higher one.
    fn materialize(&mut self, class: RegClass, value: u64) -> VReg {
        let width = if class == RegClass::Gpr64 { 64 } else { 32 };
        let v = self.vreg(class);
        self.push(
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(v), imm((value & 0xFFFF) as i64)],
        );
        for shift in (16..width).step_by(16) {
            let chunk = (value >> shift) & 0xFFFF;
            if chunk != 0 {
                self.push(
                    AArch64Opcode::Movk,
                    vec![MachOperand::VReg(v), imm(chunk as i64), imm(shift as i64)],
                );
            }
        }
        v
    }

    fn rr(&mut self, opcode: AArch64Opcode, class: RegClass, a: VReg, b: VReg) -> VReg {
        let d = self.vreg(class);
        self.push(
            opcode,
            vec![
                MachOperand::VReg(d),
                MachOperand::VReg(a),
                MachOperand::VReg(b),
            ],
        );
        d
    }

    fn ri(&mut self, opcode: AArch64Opcode, class: RegClass, a: VReg, value: i64) -> VReg {
        let d = self.vreg(class);
        self.push(
            opcode,
            vec![MachOperand::VReg(d), MachOperand::VReg(a), imm(value)],
        );
        d
    }
}

/// The `revertBits.c` O2 shape (#844/#854): each swap stage materializes its
/// masks before `AndRR`.
fn revert_bits(width: u32) -> MachFunction {
    let class = if width == 64 {
        RegClass::Gpr64
    } else {
        RegClass::Gpr32
    };
    let mut b = Builder::new(&format!("revert_bits_{width}"));
    let mut x = b.vreg(class);
    let masks: &[(u64, i64)] = if width == 64 {
        &[
            (0x5555_5555_5555_5555, 1),
            (0x3333_3333_3333_3333, 2),
            (0x0F0F_0F0F_0F0F_0F0F, 4),
            (0x00FF_00FF_00FF_00FF, 8),
            (0x0000_FFFF_0000_FFFF, 16),
            (0x0000_0000_FFFF_FFFF, 32),
        ]
    } else {
        &[
            (0x5555_5555, 1),
            (0x3333_3333, 2),
            (0x0F0F_0F0F, 4),
            (0x00FF_00FF, 8),
            (0x0000_FFFF, 16),
        ]
    };
    for &(mask, shift) in masks {
        let hi = b.ri(AArch64Opcode::LsrRI, class, x, shift);
        let m1 = b.materialize(class, mask);
        let hi = b.rr(AArch64Opcode::AndRR, class, hi, m1);
        let m2 = b.materialize(class, mask);
        let lo = b.rr(AArch64Opcode::AndRR, class, x, m2);
        let lo = b.ri(AArch64Opcode::LslRI, class, lo, shift);
        x = b.rr(AArch64Opcode::OrrRR, class, hi, lo);
    }
    b.push(AArch64Opcode::Ret, vec![]);
    b.func
}

/// Layer A and B payloads, a zero shared by a `MulRR` and an `AddRR` (the
/// Layer A rewrite leaves the `AddRR` a Layer B candidate), and a mask read
/// twice.
fn mixed_payloads() -> MachFunction {
    let mut b = Builder::new("mixed_payloads");
    let x = b.vreg(RegClass::Gpr32);
    let y = b.vreg(RegClass::Gpr64);
    let zero = b.materialize(RegClass::Gpr32, 0);
    let product = b.rr(AArch64Opcode::MulRR, RegClass::Gpr32, x, zero);
    let _ = b.rr(AArch64Opcode::AddRR, RegClass::Gpr32, product, zero);
    let seven = b.materialize(RegClass::Gpr64, 7);
    let sum = b.rr(AArch64Opcode::AddRR, RegClass::Gpr64, y, seven);
    let shared = b.materialize(RegClass::Gpr64, 0x00FF_00FF_00FF_00FF);
    let _ = b.rr(AArch64Opcode::AndRR, RegClass::Gpr64, sum, shared);
    let _ = b.rr(AArch64Opcode::AndRR, RegClass::Gpr64, y, shared);
    let odd = b.materialize(RegClass::Gpr32, 0x1234_5678);
    let _ = b.rr(AArch64Opcode::AndRR, RegClass::Gpr32, x, odd);
    b.push(AArch64Opcode::Ret, vec![]);
    b.func
}

/// The quadratic-walk reproducer: `AddRR mask=src,src; AndRR dst=src,mask`.
fn add_and_pairs(pairs: usize) -> MachFunction {
    let mut b = Builder::new(&format!("add_and_pairs_{pairs}"));
    let src = b.vreg(RegClass::Gpr32);
    for _ in 0..pairs {
        let mask = b.rr(AArch64Opcode::AddRR, RegClass::Gpr32, src, src);
        let _ = b.rr(AArch64Opcode::AndRR, RegClass::Gpr32, src, mask);
    }
    b.func
}

#[test]
fn indexed_walk_facts_match_direct_scans_on_payload_shapes() {
    let mut tally = Tally::default();
    let shapes = [
        revert_bits(32),
        revert_bits(64),
        mixed_payloads(),
        add_and_pairs(300),
    ];
    for (i, func) in shapes.iter().enumerate() {
        assert_walks_agree(&func.name, func, i as u64, &mut tally);
    }
    assert!(tally.rewrites > 50, "{tally:?}");
}

// ---------------------------------------------------------------------------
// Corpus: real selected functions
// ---------------------------------------------------------------------------

/// Instruction selection as the AArch64 pipeline runs it (`Pipeline::run_isel`
/// without proof metadata or target-feature admissions).
fn select(lir: &trust_cg_lower::Function) -> Option<MachFunction> {
    use trust_cg_lower::abi::AArch64AbiVariant;
    use trust_cg_lower::isel::InstructionSelector;

    lir.validate_eh_structure().ok()?;
    let mut isel = InstructionSelector::new(lir.name.clone(), lir.signature.clone());
    isel.set_abi_variant(AArch64AbiVariant::Darwin);
    isel.set_stack_slots(lir.stack_slots.clone());
    isel.seed_value_types(&lir.value_types);
    isel.seed_libm_pure_callees(&lir.libm_pure_callees);
    isel.seed_sret_param(lir.abi_sret_param).ok()?;
    isel.seed_sret_arg_callees(&lir.sret_arg_callees);
    isel.seed_sret_arg_indirect_callees(&lir.sret_arg_indirect_callees);
    isel.seed_iconst_origins(
        lir.blocks
            .values()
            .map(|block| block.instructions.as_slice()),
    );
    isel.seed_function_value_use_counts(lir);
    isel.lower_formal_arguments(&lir.signature, lir.entry_block)
        .ok()?;
    for block_ref in lir.layout_order() {
        let block = &lir.blocks[&block_ref];
        if block_ref != lir.entry_block && !block.params.is_empty() {
            isel.define_block_params(&block.params);
        }
        let origins = lir
            .trust_ir_origins
            .get(&block_ref)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        isel.select_block_with_provenance(
            block_ref,
            &block.instructions,
            &block.source_locs,
            origins,
        )
        .ok()?;
    }
    Some(isel.finalize_with_eh_info(&lir.eh_info).ok()?.to_ir_func())
}

/// Trust IR modules checked in beside the codegen tests: Rust MIR fixtures
/// and Clean kernel components.
const TRUST_IR_CORPUS: &[&str] = &[
    "tests/fixtures/mir_edge_bounds.tir",
    "tests/fixtures/mir_fold_binop.tir",
    "tests/fixtures/mir_value_matches.tir",
    "tests/native_arith.trust.tir",
    "tests/clean_quot_names.tir",
    "tests/clean_ri_names.tir",
];

#[test]
fn indexed_walk_facts_match_direct_scans_on_selected_trust_ir_corpus() {
    let codegen = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../trust-cg-codegen");
    let mut tally = Tally::default();
    let mut unselected = 0usize;
    let mut instructions = 0usize;
    for relative in TRUST_IR_CORPUS {
        let path = codegen.join(relative);
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
        let module = trust_ir::parser::parse_module(&text)
            .unwrap_or_else(|error| panic!("parse {}: {error:?}", path.display()));
        let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::AArch64,
            trust_cg_lower::TlsDialect::default(),
            &permit_unlicensed(),
        )
        .unwrap_or_else(|error| panic!("translate {}: {error:?}", path.display()));
        for (lir, _) in &lowered {
            let Some(selected) = select(lir) else {
                unselected += 1;
                continue;
            };
            let mut optimized = selected.clone();
            trust_cg_opt::OptimizationPipeline::new(trust_cg_opt::OptLevel::O2).run(&mut optimized);
            for (stage, func) in [("isel", &selected), ("o2", &optimized)] {
                instructions += func.insts.len();
                let seed = splitmix64(tally.functions as u64);
                assert_walks_agree(
                    &format!("{relative}::{} ({stage})", func.name),
                    func,
                    seed,
                    &mut tally,
                );
            }
        }
    }
    eprintln!("walk-facts corpus: {tally:?} unselected={unselected} instructions={instructions}");
    assert!(tally.functions > 100, "{tally:?} unselected={unselected}");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its lowerings state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
