// trust-cg-codegen/tests/mach_id_admission_property.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! L10-P5: identity freshness over the optimizer, on generated functions.
//!
//! A deterministic generator builds trust-ir loops (loads, arithmetic chains,
//! diamonds, stores, accumulators) that the real adapter and instruction
//! selector lower. For each function and each of O1, O2 and O3 the test runs
//! the optimizer's own pass ladder under the real pass manager with a boundary
//! observer and checks, at every admitted boundary:
//!
//! * the identity admission accepts the function;
//! * the register counter and every arena (instructions, blocks, stack slots,
//!   jump tables) only grow, so no ID is ever handed out twice;
//! * every register that appears for the first time lies in the range the
//!   register counter advanced over during that pass (`[counter before,
//!   counter after)`), so no new register aliased one that was live before
//!   the pass. The oracle cannot tell an allocated register from one a pass
//!   numbered by hand and then covered by raising the counter itself; the
//!   stale-counter controls below are what catch that pattern.
//!
//! The whole pipeline then prepares the same function at that level without an
//! identity refusal. The same observed ladders run over every function the
//! pipeline selects from a slice of the committed compile corpus (this
//! repository's TrustIR fixtures and seven rustc-bridge programs); a refusal at
//! the instruction-selection exit counts as a violation, and only selection's
//! own unsupported-input errors skip a function. A selected function with a
//! stale counter or a dangling sidecar key is refused by name at the
//! optimization entry, and on the corpus every O2 ladder pass that allocates
//! is refused at that allocation when the pass before it left the register
//! counter a near miss below the highest live register. Testing evidence over
//! these corpora, not a proof about every pass.
#![cfg(target_arch = "aarch64")]

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, PipelineError};
use trust_cg_ir::{InstId, LoweringProvenance, MachFunction, MachIdDomain, MachOperand};
use trust_cg_opt::{
    MachinePass, OptLevel as OptOptLevel, OptimizationPipeline, PassBoundary, PassManager,
};
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const TRIPLE: &str = "aarch64-apple-darwin";
const SEEDS: u64 = 48;

/// Deterministic xorshift64*; the generator needs no external crate.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1)
    }

    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }
}

/// `fn kernel(a: *mut T, n: i64, k: i64) -> i64`: one or two counted loops
/// over `a[0..n]` or `a[0..C]` (`T` is `i64` or `i32`) whose body is a random
/// arithmetic chain over the loaded element, `k`, a loop-invariant product,
/// the index and constants, optionally a diamond merging two arms and a store
/// back, accumulated into the return value.
fn generate(seed: u64) -> trust_ir::Module {
    let mut rng = Rng::new(seed);
    let mut mb = ModuleBuilder::new(format!("mach_id_property_{seed}"));
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("kernel", ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, Ty::I64);
    let k = fb.add_block_param(entry, Ty::I64);
    let loops = 1 + rng.below(2);
    let (elem, shift) = if rng.chance(50) {
        (Ty::I64, 3)
    } else {
        (Ty::I32, 2)
    };
    let exit = fb.create_block();
    let result = fb.add_block_param(exit, Ty::I64);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I64, 0);
    let mut carried = zero;
    let mut current = entry;
    for _ in 0..loops {
        let head = fb.create_block();
        let i = fb.add_block_param(head, Ty::I64);
        let acc = fb.add_block_param(head, Ty::I64);
        let body = fb.create_block();
        let after = fb.create_block();
        let after_acc = fb.add_block_param(after, Ty::I64);

        fb.switch_to_block(current);
        let start = fb.iconst(Ty::I64, 0);
        fb.br(head, vec![start, carried]);

        fb.switch_to_block(head);
        let bound = if rng.chance(50) {
            n
        } else {
            fb.iconst(Ty::I64, [8, 16, 64, 100][rng.below(4) as usize])
        };
        let more = fb.icmp(ICmpOp::Slt, Ty::I64, i, bound);
        fb.condbr(more, body, vec![], after, vec![acc]);

        fb.switch_to_block(body);
        let scale = fb.iconst(Ty::I64, shift);
        let offset = fb.binop(BinOp::Shl, Ty::I64, i, scale);
        let slot = fb.gep(Ty::I8, a, vec![offset]);
        let element = fb.load(elem.clone(), slot);
        let factor = fb.iconst(Ty::I64, 3 + rng.below(13) as i128);
        let invariant = fb.binop(BinOp::Mul, Ty::I64, k, factor);
        if elem == Ty::I32 && rng.chance(60) {
            // A vectorizable map: `a[i] = a[i] op c` in the element type.
            let c = fb.iconst(Ty::I32, 1 + rng.below(30) as i128);
            let op = [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Xor][rng.below(4) as usize];
            let mapped = fb.binop(op, Ty::I32, element, c);
            fb.store(Ty::I32, slot, mapped);
        }
        let loaded = if elem == Ty::I32 {
            fb.sext(Ty::I32, Ty::I64, element)
        } else {
            element
        };
        let mut value = loaded;
        for _ in 0..1 + rng.below(6) {
            let rhs = match rng.below(5) {
                0 => k,
                1 => i,
                2 => loaded,
                3 => invariant,
                _ => fb.iconst(Ty::I64, 1 + rng.below(40) as i128),
            };
            let op = match rng.below(9) {
                0 => BinOp::Add,
                1 => BinOp::Sub,
                2 => BinOp::Mul,
                3 => BinOp::And,
                4 => BinOp::Or,
                5 => BinOp::Xor,
                6 => {
                    let amount = fb.iconst(Ty::I64, 1 + rng.below(7) as i128);
                    value = fb.binop(BinOp::Shl, Ty::I64, value, amount);
                    continue;
                }
                7 => {
                    let amount = fb.iconst(Ty::I64, 1 + rng.below(7) as i128);
                    value = fb.binop(BinOp::LShr, Ty::I64, value, amount);
                    continue;
                }
                _ => BinOp::Add,
            };
            value = fb.binop(op, Ty::I64, value, rhs);
        }
        let merged = if rng.chance(50) {
            let then_block = fb.create_block();
            let else_block = fb.create_block();
            let join = fb.create_block();
            let joined = fb.add_block_param(join, Ty::I64);
            let test = fb.icmp(ICmpOp::Ult, Ty::I64, value, k);
            fb.condbr(test, then_block, vec![], else_block, vec![]);
            fb.switch_to_block(then_block);
            let c = fb.iconst(Ty::I64, 1 + rng.below(9) as i128);
            let t = fb.binop(BinOp::Add, Ty::I64, value, c);
            fb.br(join, vec![t]);
            fb.switch_to_block(else_block);
            let d = fb.iconst(Ty::I64, 2 + rng.below(9) as i128);
            let e = fb.binop(BinOp::Mul, Ty::I64, value, d);
            fb.br(join, vec![e]);
            fb.switch_to_block(join);
            joined
        } else {
            value
        };
        if elem == Ty::I64 && rng.chance(50) {
            fb.store(Ty::I64, slot, merged);
        }
        let next_acc = fb.binop(BinOp::Add, Ty::I64, acc, merged);
        let one = fb.iconst(Ty::I64, 1);
        let next_i = fb.binop(BinOp::Add, Ty::I64, i, one);
        fb.br(head, vec![next_i, next_acc]);

        carried = after_acc;
        current = after;
    }
    fb.switch_to_block(current);
    fb.br(exit, vec![carried]);
    fb.switch_to_block(exit);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn pipeline(opt_level: OptLevel) -> Pipeline {
    Pipeline::new(PipelineConfig {
        opt_level,
        target_triple: TRIPLE.into(),
        disabled_passes_override: Some(String::new()),
        ..PipelineConfig::default()
    })
}

/// The optimizer's input for `module`'s one function, as the pipeline builds it.
fn selected(module: &trust_ir::Module) -> MachFunction {
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect("adapter");
    assert_eq!(lowered.len(), 1);
    pipeline(OptLevel::O2)
        .select_ir_function(&lowered[0].0)
        .expect("instruction selection")
}

/// What a boundary snapshot records.
struct Snapshot {
    counters: [usize; 5],
    vregs: BTreeSet<u32>,
}

impl Snapshot {
    fn of(func: &MachFunction) -> Self {
        Self {
            counters: [
                func.next_vreg as usize,
                func.insts.len(),
                func.blocks.len(),
                func.stack_slots.len(),
                func.jump_tables.len(),
            ],
            vregs: func
                .insts
                .iter()
                .flat_map(|inst| inst.operands.iter().filter_map(MachOperand::as_vreg))
                .map(|reg| reg.id)
                .chain(func.noalias_params.iter().copied())
                .collect(),
        }
    }
}

#[derive(Default)]
struct Audit {
    previous: Option<Snapshot>,
    boundaries: usize,
    violations: Vec<String>,
    /// Passes that issued at least one ID, with how often.
    allocating: BTreeMap<String, usize>,
}

impl Audit {
    fn observe(&mut self, func: &MachFunction, boundary: PassBoundary<'_>) {
        self.boundaries += 1;
        let label = format!("{boundary:?}");
        if let Err(error) = func.admit_id_counters() {
            self.violations
                .push(format!("{label}: admitted boundary refuses: {error}"));
        }
        let now = Snapshot::of(func);
        if let Some(before) = &self.previous {
            const NAMES: [&str; 5] = ["vreg", "instruction", "block", "stack-slot", "jump-table"];
            for ((name, b), a) in NAMES.iter().zip(before.counters).zip(now.counters) {
                if a < b {
                    self.violations
                        .push(format!("{label}: the {name} counter fell from {b} to {a}"));
                }
            }
            let (low, high) = (before.counters[0] as u32, now.counters[0] as u32);
            for &reg in now.vregs.difference(&before.vregs) {
                if !(low..high).contains(&reg) {
                    self.violations.push(format!(
                        "{label}: v{reg} appeared without being issued (counter {low}..{high})"
                    ));
                }
            }
            if now.counters != before.counters
                && let PassBoundary::AfterPass { pass, .. } = boundary
            {
                *self.allocating.entry(pass.to_string()).or_default() += 1;
            }
        }
        self.previous = Some(now);
    }
}

fn optimizer_level(level: OptLevel) -> OptOptLevel {
    match level {
        OptLevel::O0 => OptOptLevel::O0,
        OptLevel::O1 => OptOptLevel::O1,
        OptLevel::O2 => OptOptLevel::O2,
        OptLevel::O3 => OptOptLevel::O3,
    }
}

/// What observing the optimizer's ladders found over a set of functions.
#[derive(Default)]
struct Observed {
    functions: usize,
    boundaries: usize,
    allocating: BTreeMap<String, usize>,
    violations: Vec<String>,
}

impl Observed {
    /// Run `input` through the O1, O2 and O3 ladders under an auditing
    /// observer, then through the whole pipeline at each level.
    fn run(&mut self, label: &str, input: &MachFunction) {
        self.functions += 1;
        for level in [OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let audit = Rc::new(RefCell::new(Audit::default()));
            let observer = Rc::clone(&audit);
            let mut manager = OptimizationPipeline::new(optimizer_level(level))
                .with_target_is_darwin(true)
                .with_disabled_passes(String::new())
                .build_pass_manager()
                .with_boundary_observer(Box::new(move |func, boundary| {
                    observer.borrow_mut().observe(func, boundary)
                }));
            let mut func = input.clone();
            let stats = if level == OptLevel::O3 {
                manager.run_to_fixpoint(&mut func, 4)
            } else {
                manager.run_once_with_stats(&mut func)
            };
            if let Err(refusal) = stats.id_admission {
                self.violations
                    .push(format!("{label} {level:?}: refused: {refusal}"));
            }
            let audit = audit.borrow();
            self.boundaries += audit.boundaries;
            for (pass, count) in &audit.allocating {
                *self.allocating.entry(pass.clone()).or_default() += count;
            }
            self.violations.extend(
                audit
                    .violations
                    .iter()
                    .map(|v| format!("{label} {level:?} {v}")),
            );

            let mut whole = input.clone();
            if let Err(PipelineError::MachIdAdmission(refusal)) =
                pipeline(level).prepare_ir_function(&mut whole)
            {
                self.violations.push(format!(
                    "{label} {level:?}: the pipeline refused: {refusal}"
                ));
            }
        }
    }
}

#[test]
fn optimizer_boundaries_issue_only_fresh_identities_on_generated_functions() {
    let mut observed = Observed::default();
    for seed in 0..SEEDS {
        let module = generate(seed);
        let input = selected(&module);
        observed.run(&format!("seed {seed}"), &input);
        // Generated functions compile: whole-pipeline refusals of any kind
        // would hide the property.
        for level in [OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            pipeline(level)
                .prepare_ir_function(&mut input.clone())
                .unwrap_or_else(|error| panic!("seed {seed} {level:?}: {error}"));
        }
    }
    assert!(observed.violations.is_empty(), "{:#?}", observed.violations);
    assert!(
        observed.boundaries > 5_000,
        "only {} boundaries observed",
        observed.boundaries
    );
    // The property must have watched allocation, not only no-op passes.
    for pass in ["mul-shift-reduce", "loop-latch-layout"] {
        assert!(
            observed.allocating.contains_key(pass),
            "`{pass}` issued no ID: {:?}",
            observed.allocating
        );
    }
    eprintln!(
        "[mach-id-property] generated: functions={} boundaries={} allocating={:?}",
        observed.functions, observed.boundaries, observed.allocating
    );
}

/// The committed compile-corpus modules (this repository's TrustIR fixtures
/// and a slice of the rustc-bridge programs): every function the pipeline
/// selects runs the same observed ladders.
/// The corpus slice: this repository's TrustIR fixtures and seven
/// rustc-bridge programs, in a stable order.
fn corpus_files() -> Vec<std::path::PathBuf> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/compile-corpus/modules");
    let mut files = Vec::new();
    for dir in [
        "fixtures",
        "bridge/beat-llvm--p1_xorshift",
        "bridge/beat-llvm--p2_collatz",
        "bridge/beat-llvm--p3_gcd",
        "bridge/beat-llvm--p5_struct_acc",
        "bridge/shape-coverage--s11_slice_sum_u64",
        "bridge/shape-coverage--s31_vec_sort_dedup",
        "bridge/shape-coverage--s63_state_machine",
    ] {
        let mut entries: Vec<_> = std::fs::read_dir(root.join(dir))
            .unwrap_or_else(|error| panic!("{dir}: {error}"))
            .filter_map(|entry| entry.ok().map(|entry| entry.path()))
            .filter(|path| path.extension().is_some_and(|ext| ext == "trust_irbin"))
            .collect();
        entries.sort();
        files.extend(entries);
    }
    files
}

/// Every distinct function the pipeline selects from the corpus slice, with
/// its label. A refusal at the instruction-selection exit is a violation;
/// selection's own errors (inputs it does not support) are counted as skips.
struct CorpusFunctions {
    functions: Vec<(String, MachFunction)>,
    skipped: usize,
    violations: Vec<String>,
}

fn corpus_functions() -> CorpusFunctions {
    let mut corpus = CorpusFunctions {
        functions: Vec::new(),
        skipped: 0,
        violations: Vec::new(),
    };
    let mut seen = BTreeSet::new();
    for file in &corpus_files() {
        let bytes = std::fs::read(file).expect("read module");
        let module = trust_cg_codegen::pipeline::load_module_from_bytes(&bytes).expect("decode");
        let Ok(lowered) = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::default(),
            trust_cg_lower::TlsDialect::default(),
            &permit_unlicensed(),
        ) else {
            corpus.skipped += 1;
            continue;
        };
        for (function, _) in &lowered {
            // Shared runtime functions recur in every codegen unit.
            if !seen.insert(function.name.clone()) {
                continue;
            }
            let label = format!("{}::{}", file.display(), function.name);
            match pipeline(OptLevel::O2).select_ir_function(function) {
                Ok(input) => corpus.functions.push((label, input)),
                Err(PipelineError::MachIdAdmission(refusal)) => corpus
                    .violations
                    .push(format!("{label}: selection exit refused: {refusal}")),
                Err(_) => corpus.skipped += 1,
            }
        }
    }
    corpus
}

#[test]
fn optimizer_boundaries_issue_only_fresh_identities_on_corpus_modules() {
    let corpus = corpus_functions();
    let mut observed = Observed {
        violations: corpus.violations,
        ..Observed::default()
    };
    for (label, input) in &corpus.functions {
        observed.run(label, input);
    }
    assert!(observed.violations.is_empty(), "{:#?}", observed.violations);
    assert!(
        observed.functions >= 100,
        "only {} corpus functions observed",
        observed.functions
    );
    assert!(
        observed.allocating.len() >= 5,
        "too few allocating passes observed: {:?}",
        observed.allocating
    );
    assert!(
        corpus.skipped <= observed.functions / 4,
        "{} corpus inputs skipped against {} observed",
        corpus.skipped,
        observed.functions
    );
    eprintln!(
        "[mach-id-property] corpus: functions={} skipped={} boundaries={} allocating={:?}",
        observed.functions, corpus.skipped, observed.boundaries, observed.allocating
    );
}

/// A test pass that sets the register counter without allocating: the stale
/// state a pass that wrote IDs by hand would leave behind.
struct StaleCounter(u32);

impl MachinePass for StaleCounter {
    fn name(&self) -> &str {
        "stale-counter"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        func.next_vreg = self.0;
        true
    }
}

/// The counter and arena extents: any growth means an ID was issued.
fn extents(func: &MachFunction) -> [usize; 4] {
    [
        func.next_vreg as usize,
        func.insts.len(),
        func.blocks.len(),
        func.stack_slots.len(),
    ]
}

fn o2_ladder() -> Vec<Box<dyn MachinePass>> {
    OptimizationPipeline::new(OptOptLevel::O2)
        .with_target_is_darwin(true)
        .with_disabled_passes(String::new())
        .build_pass_manager()
        .into_passes()
}

#[test]
fn every_allocating_pass_refuses_a_near_miss_stale_counter_on_corpus_functions() {
    // Walk each corpus function down the O2 ladder one pass at a time. Where
    // a pass allocates on the state it reaches, run a fresh instance of it
    // again after a pass that left the counter at the highest live register:
    // the next ID it would issue is live. The refusal must come at the pass's
    // first allocation, or, only when the pass then declined and issued
    // nothing, at the pass-manager exit.
    let corpus = corpus_functions();
    let mut violations = corpus.violations;
    let mut at_allocation: BTreeMap<String, usize> = BTreeMap::new();
    let mut declined: BTreeMap<String, usize> = BTreeMap::new();
    for (label, input) in &corpus.functions {
        let mut current = input.clone();
        for (probe, fresh) in o2_ladder().into_iter().zip(o2_ladder()) {
            let name = probe.name().to_string();
            let mut next = current.clone();
            let stats = PassManager::new()
                .with_pass(probe)
                .run_once_with_stats(&mut next);
            if stats.id_admission.is_err() {
                violations.push(format!("{label} `{name}`: clean run refused"));
                break;
            }
            let Some(highest) = current
                .insts
                .iter()
                .flat_map(|inst| inst.operands.iter().filter_map(MachOperand::as_vreg))
                .map(|reg| reg.id)
                .chain(current.noalias_params.iter().copied())
                .max()
            else {
                current = next;
                continue;
            };
            if extents(&next) != extents(&current) {
                let mut stale_input = current.clone();
                stale_input.next_vreg = highest;
                let mut func = current.clone();
                let stats = PassManager::new()
                    .with_pass(Box::new(StaleCounter(highest)))
                    .with_pass(fresh)
                    .run_once_with_stats(&mut func);
                match stats.id_admission {
                    Ok(()) => violations.push(format!(
                        "{label} `{name}`: ran on stale counter {highest} unrefused"
                    )),
                    Err(refusal) => {
                        let first = format!("the first allocation in pass `{name}` (iteration 1)");
                        let exit = format!("pass-manager exit (after pass `{name}`)");
                        if refusal.error.domain() != MachIdDomain::VReg {
                            violations.push(format!("{label} `{name}`: {refusal}"));
                        } else if refusal.boundary == first {
                            *at_allocation.entry(name.clone()).or_default() += 1;
                        } else if refusal.boundary == exit
                            && extents(&func) == extents(&stale_input)
                        {
                            *declined.entry(name.clone()).or_default() += 1;
                        } else {
                            violations.push(format!(
                                "{label} `{name}`: issued an ID without an admission: {refusal}"
                            ));
                        }
                    }
                }
            }
            current = next;
        }
    }
    assert!(violations.is_empty(), "{violations:#?}");
    // SROA numbers its shadows while analysing; it must be among the passes
    // refused at their allocation.
    for pass in ["sroa", "mul-shift-reduce", "loop-latch-layout"] {
        assert!(
            at_allocation.contains_key(pass),
            "`{pass}` was never refused at an allocation: {at_allocation:?}"
        );
    }
    eprintln!(
        "[mach-id-property] near-miss: at-allocation={at_allocation:?} declined={declined:?}"
    );
}

#[test]
fn a_stale_selected_function_is_refused_at_the_optimization_entry() {
    for seed in 0..8 {
        let input = selected(&generate(seed));
        for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let mut stale = input.clone();
            stale.next_vreg = 1;
            match pipeline(level).prepare_ir_function(&mut stale) {
                Err(PipelineError::MachIdAdmission(refusal)) => {
                    assert_eq!(refusal.boundary, "optimization entry");
                    assert_eq!(refusal.error.domain(), MachIdDomain::VReg);
                    assert_eq!(refusal.function, "kernel");
                    assert!(
                        refusal
                            .to_string()
                            .contains("[TCG-MIR-STALE-ID-COUNTER] vreg counter 1"),
                        "{refusal}"
                    );
                }
                other => panic!("seed {seed} {level:?}: expected a refusal, got {other:?}"),
            }

            let mut dangling = input.clone();
            let past = InstId(dangling.insts.len() as u32);
            dangling
                .lowering_provenance
                .insert(past, LoweringProvenance::UNATTRIBUTED);
            match pipeline(level).prepare_ir_function(&mut dangling) {
                Err(PipelineError::MachIdAdmission(refusal)) => {
                    assert_eq!(refusal.boundary, "optimization entry");
                    assert_eq!(refusal.error.domain(), MachIdDomain::Inst);
                }
                other => panic!("seed {seed} {level:?}: expected a refusal, got {other:?}"),
            }
        }
    }
}

#[test]
fn every_ladder_pass_refuses_a_stale_counter_on_selected_functions() {
    // Each pass of each ladder, alone, on real selection output: refused at
    // its entry, the function untouched.
    let input = selected(&generate(7));
    let mut stale = input.clone();
    stale.next_vreg = 1;
    let before = format!("{stale:?}");
    let mut checked = 0;
    for level in [OptOptLevel::O1, OptOptLevel::O2, OptOptLevel::O3] {
        for pass in OptimizationPipeline::new(level)
            .with_target_is_darwin(true)
            .with_disabled_passes(String::new())
            .build_pass_manager()
            .into_passes()
        {
            let name = pass.name().to_string();
            let mut manager = trust_cg_opt::PassManager::new().with_pass(pass);
            let mut func = stale.clone();
            let stats = manager.run_once_with_stats(&mut func);
            let refusal = stats.id_admission.expect_err(&name);
            assert_eq!(refusal.boundary, format!("entry of pass `{name}`"));
            assert_eq!(format!("{func:?}"), before, "{name}");
            checked += 1;
        }
    }
    assert!(checked > 100, "{checked}");
}

/// This file's fixtures and corpus modules are claim-less (`body_gate:
/// None`), which trust-cg REFUSES by default (roadmap WS7.5, decision gate
/// DG-73). Its translations state `Permit` explicitly, so no corpus module is
/// skipped because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
