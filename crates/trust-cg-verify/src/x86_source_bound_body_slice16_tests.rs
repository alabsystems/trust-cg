// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 16 of the x86-64 source-bound body theorem: a function past the
//! single-query bounds, cut at its entry, its loop headers and planned program
//! points (block starts and clean instruction boundaries inside blocks), its
//! theorem stated as one statement and replayed in PARTS, one per region
//! (`split.rs`). At every cut point every live value and private byte that is
//! not fixed for the run is a free input both sides share, and the theorem
//! states the cut-point relation on every edge into it.
//!
//! Fixtures are real: LIR from the trust-ir adapter, the machine stream from
//! the real x86-64 instruction selector (`super::select`). A small fixture is
//! stated in parts by a test policy that cuts it at chosen points
//! ([`cut_at`]); the production planner states only functions past the
//! single-query bounds in parts. Every test here runs without a solver (the
//! `x86_source_bound_body::tests::slice16::` library gate); the replay on AY
//! and Clean and the verifier credit are in `slice16_qualification`.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice9::{dag_holds_on_samples, dag_refuted_on_samples};
use super::slice22::fixture_owner;
use super::split::SplitPolicy;
use super::*;

/// A policy that cuts at exactly `points` (besides the entry and the loop
/// headers), with no region or part bound.
pub(crate) fn cut_at(points: Vec<(Block, usize)>) -> SplitPolicy {
    SplitPolicy {
        region_rows: usize::MAX,
        region_instructions: usize::MAX,
        region_blocks: usize::MAX,
        max_parts: usize::MAX,
        points: Some(points),
    }
}

/// The start of every block but the entry.
pub(crate) fn every_block(source: &Function) -> Vec<(Block, usize)> {
    let mut points: Vec<(Block, usize)> = source
        .blocks
        .keys()
        .filter(|block| **block != source.entry_block)
        .map(|block| (*block, 0))
        .collect();
    points.sort();
    points
}

/// Every block start but the entry's, and every instruction boundary inside a
/// block at which its machine rows split cleanly ([`split::clean_split_row`]).
pub(crate) fn every_point(source: &Function, machine: &X86ISelFunction) -> Vec<(Block, usize)> {
    let mut points = every_block(source);
    let Ok(correspondence) = block_correspondence(source, machine, &Default::default()) else {
        return points;
    };
    let mut blocks: Vec<&Block> = source.blocks.keys().collect();
    blocks.sort();
    for block in blocks {
        let body = &source.blocks[block];
        let lowered = correspondence.lowering[block];
        let rows = &machine.blocks[&lowered].insts;
        let stamps = split::stamped_rows(machine, lowered, *block);
        let last = body
            .instructions
            .len()
            .saturating_sub(1 + split::trailing_copies(body));
        let mut used = std::collections::BTreeSet::new();
        for k in 1..=last {
            if let Some(row) = split::clean_split_row(rows, &stamps, k)
                && used.insert(row)
            {
                points.push((*block, k));
            }
        }
    }
    points.sort();
    points.dedup();
    points
}

/// The owner of `source` and `machine`, stated in parts at `points`.
pub(crate) fn in_parts<'a>(
    source: &'a Function,
    machine: &'a X86ISelFunction,
    points: Vec<(Block, usize)>,
) -> Result<SourceBoundX86Body<'a>, X86BodyRefusal> {
    source_bound_x86_body_in_parts(source, machine, SYSV, &cut_at(points))
}

/// Whether some edge-word sample (slice 10's) or pooled two-word sample
/// (slice 11's) refutes `obligation`: inputs drawn from boundary words
/// (zero, one, the extremes and their neighbours), which keyed random
/// samples rarely hit.
fn pooled_refuted(obligation: &ProofObligation) -> bool {
    (0..super::slice10::EDGE_SAMPLES).any(|seed| !super::slice10::holds_at_edge(obligation, seed))
        || (0..super::slice11::POOL_SAMPLES)
            .any(|seed| !super::slice11::holds_at_pool(obligation, seed))
}

/// Every part of an owner holds on slice 9's keyed samples, and so does its
/// statement.
pub(crate) fn parts_hold(owner: &SourceBoundX86Body<'_>) -> Result<(), String> {
    for part in owner.parts() {
        if !dag_holds_on_samples(part) {
            return Err(format!("{} is refuted on samples", part.name));
        }
    }
    if !dag_holds_on_samples(owner.obligation()) {
        return Err("the statement is refuted on samples".into());
    }
    Ok(())
}

/// [`parts_hold`], and no part nor the statement is refuted by the edge or
/// pooled samples either: every sampler [`some_part_refuted`] uses, so a
/// refutation of a mis-model by any is one a correct lowering never gets.
/// (The edge and pooled samples are slow on the large shapes, which use
/// [`parts_hold`].)
pub(crate) fn parts_hold_on_every_sampler(owner: &SourceBoundX86Body<'_>) -> Result<(), String> {
    parts_hold(owner)?;
    for part in owner.parts() {
        if pooled_refuted(part) {
            return Err(format!("{} is refuted on pooled samples", part.name));
        }
    }
    if pooled_refuted(owner.obligation()) {
        return Err("the statement is refuted on pooled samples".into());
    }
    Ok(())
}

/// Some part of an owner, or its statement, is refuted on slice 9's keyed
/// samples, or on the edge or pooled samples.
pub(crate) fn some_part_refuted(owner: &SourceBoundX86Body<'_>) -> bool {
    owner.parts().iter().any(dag_refuted_on_samples)
        || dag_refuted_on_samples(owner.obligation())
        || owner.parts().iter().any(pooled_refuted)
        || pooled_refuted(owner.obligation())
}

/// Every fixture of slices 1 to 15 (slice 4's memory shapes and slice 5's
/// pairs included): label, LIR, the selector's stream.
pub(crate) fn earlier_fixtures() -> Vec<(String, Function, X86ISelFunction)> {
    let mut fixtures: Vec<(String, Function, X86ISelFunction)> = Vec::new();
    for shape in all_shapes() {
        let (source, machine) = pair(shape);
        fixtures.push((format!("{shape:?}"), source, machine));
    }
    for shape in super::memory::MEMORY_SHAPES {
        let (source, machine) = super::memory::memory_pair(shape);
        fixtures.push((format!("s4 {shape:?}"), source, machine));
    }
    for shape in super::slice5::SLICE_FIVE {
        let (source, machine) = super::slice5::slice5_pair(shape);
        fixtures.push((format!("s5 {shape:?}"), source, machine));
    }
    for shape in super::slice6::all_slice_six_shapes() {
        let (source, machine) = super::slice6::slice6_pair(shape);
        fixtures.push((format!("s6 {shape:?}"), source, machine));
    }
    for shape in super::slice7::all_slice_seven_shapes() {
        let (source, machine) = super::slice7::slice7_pair(shape);
        fixtures.push((format!("s7 {shape:?}"), source, machine));
    }
    for shape in super::slice8::all_slice_eight_shapes() {
        let (source, machine) = super::slice8::slice8_pair(shape);
        fixtures.push((format!("s8 {shape:?}"), source, machine));
    }
    for shape in super::slice9::SLICE_NINE {
        let (source, machine) = super::slice9::slice9_pair(shape);
        fixtures.push((format!("s9 {shape:?}"), source, machine));
    }
    for shape in super::slice10::all_slice_ten_shapes() {
        let (source, machine) = super::slice10::slice10_pair(shape);
        fixtures.push((format!("s10 {shape:?}"), source, machine));
    }
    for shape in super::slice11::all_slice_eleven_shapes() {
        let (source, machine) = super::slice11::slice11_pair(shape);
        fixtures.push((format!("s11 {shape:?}"), source, machine));
    }
    for shape in super::slice12::SLICE_TWELVE {
        let (source, machine) = super::slice12::slice12_pair(shape);
        fixtures.push((format!("s12 {shape:?}"), source, machine));
    }
    for shape in super::slice13::all_slice_thirteen_shapes() {
        let (source, machine) = super::slice13::slice13_pair(shape);
        fixtures.push((format!("s13 {shape:?}"), source, machine));
    }
    for shape in super::slice14::SLICE_FOURTEEN {
        let (source, machine) = super::slice14::slice14_pair(shape);
        fixtures.push((format!("s14 {shape:?}"), source, machine));
    }
    for shape in super::slice15::all_slice_fifteen_shapes() {
        let (source, machine) = super::slice15::slice15_pair(shape);
        fixtures.push((format!("s15 {shape:?}"), source, machine));
    }
    fixtures
}

/// Every wrong lowering of slices 6 to 15: label, LIR, the mutated stream.
pub(crate) fn earlier_refutations() -> Vec<(String, Function, X86ISelFunction)> {
    let mut cases: Vec<(String, Function, X86ISelFunction)> = Vec::new();
    let mut add = |prefix: &str, list: Vec<(&'static str, Function, X86ISelFunction)>| {
        for (label, source, machine) in list {
            cases.push((format!("{prefix} {label}"), source, machine));
        }
    };
    add("s6", super::slice6::slice_six_refutations());
    add("s7", super::slice7::slice_seven_refutations());
    add("s8", super::slice8::slice_eight_refutations());
    add("s9", super::slice9::slice_nine_refutations());
    add("s10", super::slice10::slice_ten_refutations());
    add("s11", super::slice11::slice_eleven_refutations());
    add("s12", super::slice12::slice_twelve_refutations());
    add("s13", super::slice13::slice_thirteen_refutations());
    add("s14", super::slice14::slice_fourteen_refutations());
    add("s15", super::slice15::slice_fifteen_refutations());
    cases
}

/// A refusal's text with its numbers removed (a histogram key).
fn reason_key(text: &str) -> String {
    let mut key = String::new();
    let mut skipping = false;
    for c in text.chars() {
        if c.is_ascii_digit() {
            if !skipping {
                key.push('#');
            }
            skipping = true;
        } else {
            skipping = false;
            key.push(c);
        }
    }
    key.chars().take(140).collect()
}

/// What stating a correct pair in parts at `points` gave: built (parts),
/// refused (reason), or a defect (a mismatch named, or a part refuted).
fn judge_correct(
    label: &str,
    source: &Function,
    machine: &X86ISelFunction,
    points: Vec<(Block, usize)>,
) -> Result<Result<usize, String>, String> {
    match in_parts(source, machine, points) {
        Ok(owner) => {
            owner
                .check_parts()
                .map_err(|why| format!("{label}: the inventory does not check: {why}"))?;
            parts_hold_on_every_sampler(&owner).map_err(|why| {
                format!(
                    "{label}: {why}\n{}{}",
                    describe_lir(source),
                    describe(machine)
                )
            })?;
            Ok(Ok(owner.parts().len()))
        }
        Err(X86BodyRefusal::Mismatch(mismatch)) => Err(format!(
            "{label}: a correct lowering stated in parts is named a mismatch: {mismatch}"
        )),
        Err(refusal) => Ok(Err(refusal.to_string())),
    }
}

/// Where a fixture is cut: the `(block, instruction index)` points chosen for
/// a source function and its machine stream.
type CutPoints = dyn Fn(&Function, &X86ISelFunction) -> Vec<(Block, usize)>;

/// Judge every correct earlier fixture cut at `points_of`'s points: the
/// counts built and refused, with each refusal reason's count, and the
/// defects.
fn judge_every_fixture(tag: &str, points_of: &CutPoints) -> (usize, usize, Vec<String>) {
    let mut built = 0;
    let mut refused = 0;
    let mut reasons: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    let mut defects = Vec::new();
    for (label, source, machine) in earlier_fixtures() {
        // Only pairs the single theorem binds: stating them in parts is the
        // question.
        if fixture_owner(&source, &machine).is_err() {
            continue;
        }
        match judge_correct(&label, &source, &machine, points_of(&source, &machine)) {
            Ok(Ok(_)) => built += 1,
            Ok(Err(reason)) => {
                refused += 1;
                *reasons.entry(reason_key(&reason)).or_default() += 1;
                eprintln!("{tag} refused {label}: {reason}");
            }
            Err(defect) => defects.push(defect),
        }
    }
    eprintln!("{tag} built={built} refused={refused}");
    for (reason, count) in &reasons {
        eprintln!("{tag} {count:4} {reason}");
    }
    (built, refused, defects)
}

/// Every correct fixture of slices 1 to 15, cut at every block start: the
/// owner states it in parts whose every part holds on the samples, or makes
/// no claim; never a named mismatch. (A cut may only refuse or refute more,
/// and on these O0 selector streams it does not refute.)
#[test]
fn every_earlier_fixture_cut_at_every_block_holds_part_by_part() {
    let (built, refused, defects) =
        judge_every_fixture("SLICE16_EVERY_BLOCK", &|source, _| every_block(source));
    assert!(defects.is_empty(), "{}", defects.join("\n\n"));
    assert!(built > 2 * refused, "most fixtures are stated in parts");
}

/// Every correct fixture, cut at every block start and every clean
/// instruction boundary inside a block: as above, through the pieces. On
/// the production verifier's stack: the edge and pooled samplers evaluate
/// each statement recursively (`SmtExpr::try_eval`), and a statement cut
/// everywhere, with OD-233's defined cut inputs, is deeper than a test
/// thread's default stack holds in a debug build.
#[test]
fn every_earlier_fixture_cut_at_every_clean_point_holds_part_by_part() {
    crate::resource_limits::run_on_proof_verifier_stack("slice16-every-point", || {
        let (built, refused, defects) = judge_every_fixture("SLICE16_EVERY_POINT", &every_point);
        assert!(defects.is_empty(), "{}", defects.join("\n\n"));
        assert!(built > refused, "most fixtures are stated in parts");
    });
}

/// What stating a wrong pair in parts at `points` gave: never every part
/// holding.
fn judge_wrong(
    label: &str,
    source: &Function,
    machine: &X86ISelFunction,
    points: Vec<(Block, usize)>,
) -> Result<&'static str, String> {
    match in_parts(source, machine, points) {
        Ok(owner) => {
            if some_part_refuted(&owner) {
                Ok("refuted")
            } else {
                Err(format!(
                    "{label}: a wrong lowering stated in parts holds part by part\n{}",
                    describe(machine)
                ))
            }
        }
        Err(X86BodyRefusal::Mismatch(_)) => Ok("mismatch"),
        Err(X86BodyRefusal::Unsupported(_)) => Ok("no claim"),
    }
}

/// Every wrong lowering of slices 6 to 15, cut at every block start and at
/// every clean point: never credited (a named mismatch, no claim, or some
/// part refuted on the samples).
#[test]
fn every_earlier_refutation_stated_in_parts_is_never_credited() {
    let mut counts: std::collections::BTreeMap<&'static str, usize> =
        std::collections::BTreeMap::new();
    let mut defects = Vec::new();
    for (label, source, machine) in earlier_refutations() {
        for points in [every_block(&source), every_point(&source, &machine)] {
            match judge_wrong(&label, &source, &machine, points) {
                Ok(outcome) => *counts.entry(outcome).or_default() += 1,
                Err(defect) => defects.push(defect),
            }
        }
    }
    eprintln!("SLICE16_REFUTATIONS {counts:?}");
    assert!(defects.is_empty(), "{}", defects.join("\n\n"));
    assert!(counts.get("refuted").copied().unwrap_or(0) > 0);
}

/// A function within the single-query bounds keeps its theorem: the owner
/// states no fixture in parts.
#[test]
fn a_function_within_the_bounds_is_never_stated_in_parts() {
    for (label, source, machine) in earlier_fixtures() {
        if let Ok(owner) = fixture_owner(&source, &machine) {
            assert!(!owner.is_stated_in_parts(), "{label}");
            assert!(owner.parts().is_empty(), "{label}");
            assert!(owner.check_parts().is_ok(), "{label}");
        }
    }
}

/// The part inventory is exactly the statement's split: removing a part, or
/// changing a region's claim count, fails the one inventory check.
#[test]
fn a_missing_or_regrouped_part_fails_the_inventory_check() {
    // The first pair stated in several parts: a loop cut at every block, or
    // a size shape by the production planner.
    let pairs: Vec<(Function, X86ISelFunction)> = std::iter::once(super::slice12::slice12_pair(
        super::slice12::LoopShape::SumBelow,
    ))
    .chain(SLICE_SIXTEEN.iter().map(|shape| slice16_pair(*shape)))
    .collect();
    let owner = pairs
        .iter()
        .find_map(|(source, machine)| {
            let owner = if split::fits_one_query(source, machine) {
                in_parts(source, machine, every_block(source))
            } else {
                fixture_owner(source, machine)
            }
            .ok()?;
            (owner.parts().len() >= 2).then_some(owner)
        })
        .expect("a pair stated in several parts");
    owner.check_parts().expect("the owner's inventory checks");
    let parts = owner.shared_parts();
    for k in 0..owner.parts().len() {
        let fewer = parts.without_part(k);
        assert!(
            fewer.check(owner.obligation()).is_err(),
            "the inventory without part {k} must not check"
        );
    }
    let mut regrouped = parts.region_claims().to_vec();
    if let Some(first) = regrouped.iter().position(|count| *count > 0)
        && let Some(next) = (first + 1..regrouped.len()).find(|r| regrouped[*r] > 0)
    {
        regrouped[first] += 1;
        regrouped[next] -= 1;
        assert!(
            check_x86_body_parts(owner.obligation(), &regrouped, owner.parts()).is_err(),
            "a regrouped inventory must not check"
        );
    }
}

/// Stating the same pair in parts twice gives the same statement and parts.
#[test]
fn theorems_in_parts_are_deterministic() {
    for shape in super::slice12::SLICE_TWELVE {
        let (source, machine) = super::slice12::slice12_pair(shape);
        let points = every_point(&source, &machine);
        let Ok(first) = in_parts(&source, &machine, points.clone()) else {
            continue;
        };
        for _ in 0..2 {
            let again = in_parts(&source, &machine, points.clone()).unwrap();
            assert_eq!(again.obligation(), first.obligation(), "{shape:?}");
            assert_eq!(again.parts(), first.parts(), "{shape:?}");
        }
    }
}

// ---------------------------------------------------------------------------
// Functions past the single-query bounds (the production planner)
// ---------------------------------------------------------------------------

/// Slice-16 fixture shapes: functions past the single-query bounds, which the
/// production planner states in parts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SizeShape {
    /// `fn(x: u64, p: *mut u64) -> u64`: one straight-line block of 90 steps
    /// `acc = (acc ^ (acc << 3)) + k_i; p[i] = acc`, then `acc`: cut inside
    /// the block (mid-block cuts at clean stamp boundaries).
    LongChain,
    /// `fn(x: u64, y: u64) -> u64`: 34 diamonds `if acc & m_i != 0 { acc +=
    /// y } else { acc ^= k_i }` in sequence: cut at block starts (joins).
    DiamondChain,
    /// `fn(n: u64, p: *mut u64) -> u64`: a loop whose body is 70 such steps:
    /// cut at its header and inside its body.
    BigLoop,
    /// `fn(p: *mut u64, i: u64) -> u64`: a local `[u64; 200]` zeroed element
    /// by element, then `a[3]` stored to `*p` and `i` returned: the zeroed
    /// bytes cross the cuts as closed constants.
    ZeroArray,
    /// `fn(x: u64) -> u64`: a local counter updated by 110 calls `c = g1(c) +
    /// x`, each result stored back to the local: call results and a slot's
    /// bytes cross the cuts.
    CallChain,
}

pub(crate) const SLICE_SIXTEEN: [SizeShape; 5] = [
    SizeShape::LongChain,
    SizeShape::DiamondChain,
    SizeShape::BigLoop,
    SizeShape::ZeroArray,
    SizeShape::CallChain,
];

impl SizeShape {
    fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s16_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }
}

type Builder<'a> = trust_ir_build::FunctionBuilder<'a>;
type V = trust_ir::value::ValueId;

/// One step `acc = (acc ^ (acc << 3)) + k; p[i] = acc` (the store when a
/// pointer is given).
fn step(f: &mut Builder<'_>, acc: V, k: u64, store: Option<(V, u64)>) -> V {
    let three = f.iconst(Ty::U64, 3);
    let shifted = f.binop(trust_ir::BinOp::Shl, Ty::U64, acc, three);
    let mixed = f.binop(trust_ir::BinOp::Xor, Ty::U64, acc, shifted);
    let constant = f.iconst(Ty::U64, k as i128);
    let next = f.add(Ty::U64, mixed, constant);
    if let Some((p, i)) = store {
        let at = f.gep_byte_offset(p, 8 * i);
        f.store(Ty::U64, at, next);
    }
    next
}

/// The LIR the trust-ir adapter produces for a slice-16 shape.
pub(crate) fn slice16_lir(shape: SizeShape) -> Function {
    use SizeShape::*;
    use trust_ir::ICmpOp;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice16");
    let g1 = {
        let ty = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        builder.declare_function("g1", ty)
    };
    let array = {
        let element = builder.add_type(Ty::U64);
        Ty::Array(element, 200)
    };
    let ptr = Ty::PtrMut(Box::new(Ty::U64));
    let (params, results): (Vec<Ty>, Vec<Ty>) = match shape {
        LongChain => (vec![Ty::U64, ptr.clone()], vec![Ty::U64]),
        DiamondChain => (vec![Ty::U64, Ty::U64], vec![Ty::U64]),
        BigLoop => (vec![Ty::U64, ptr.clone()], vec![Ty::U64]),
        ZeroArray => (vec![ptr.clone(), Ty::U64], vec![Ty::U64]),
        CallChain => (vec![Ty::U64], vec![Ty::U64]),
    };
    let signature = builder.add_func_type(params.clone(), results);
    let mut f = builder.function(shape.name(), signature);
    let entry = f.create_block();
    let args: Vec<V> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    match shape {
        LongChain => {
            let mut acc = args[0];
            for i in 0..90u64 {
                acc = step(&mut f, acc, 0x9e37 + 7 * i, Some((args[1], i)));
            }
            f.ret(vec![acc]);
        }
        DiamondChain => {
            let mut acc = args[0];
            for i in 0..34u64 {
                let (then, other, join) = (f.create_block(), f.create_block(), f.create_block());
                let joined = f.add_block_param(join, Ty::U64);
                let mask = f.iconst(Ty::U64, 1i128 << (i % 60));
                let bit = f.binop(trust_ir::BinOp::And, Ty::U64, acc, mask);
                let zero = f.iconst(Ty::U64, 0);
                let set = f.icmp(ICmpOp::Ne, Ty::U64, bit, zero);
                f.condbr(set, then, vec![], other, vec![]);
                f.switch_to_block(then);
                let sum = f.add(Ty::U64, acc, args[1]);
                f.br(join, vec![sum]);
                f.switch_to_block(other);
                let k = f.iconst(Ty::U64, (0x51 + 13 * i) as i128);
                let flipped = f.binop(trust_ir::BinOp::Xor, Ty::U64, acc, k);
                f.br(join, vec![flipped]);
                f.switch_to_block(join);
                acc = joined;
            }
            f.ret(vec![acc]);
        }
        BigLoop => {
            let (header, body, exit) = (f.create_block(), f.create_block(), f.create_block());
            let i = f.add_block_param(header, Ty::U64);
            let acc = f.add_block_param(header, Ty::U64);
            let zero = f.iconst(Ty::U64, 0);
            f.br(header, vec![zero, zero]);
            f.switch_to_block(header);
            let more = f.icmp(ICmpOp::Ult, Ty::U64, i, args[0]);
            f.condbr(more, body, vec![], exit, vec![]);
            f.switch_to_block(body);
            let mut next = acc;
            for k in 0..70u64 {
                next = step(&mut f, next, 0x2545 + 3 * k, Some((args[1], k)));
            }
            let one = f.iconst(Ty::U64, 1);
            let i1 = f.add(Ty::U64, i, one);
            f.br(header, vec![i1, next]);
            f.switch_to_block(exit);
            f.ret(vec![acc]);
        }
        ZeroArray => {
            let a = f.alloca(array.clone());
            let zero = f.iconst(Ty::U64, 0);
            for i in 0..200u64 {
                let at = f.gep_byte_offset(a, 8 * i);
                f.store(Ty::U64, at, zero);
            }
            let third = f.gep_byte_offset(a, 24);
            let value = f.load(Ty::U64, third);
            f.store(Ty::U64, args[0], value);
            f.ret(vec![args[1]]);
        }
        CallChain => {
            let c = f.alloca(Ty::U64);
            f.store(Ty::U64, c, args[0]);
            for _ in 0..110 {
                let now = f.load(Ty::U64, c);
                let called = f.call(g1, vec![now]);
                let next = f.add(Ty::U64, called, args[0]);
                f.store(Ty::U64, c, next);
            }
            let last = f.load(Ty::U64, c);
            f.ret(vec![last]);
        }
    }
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{shape:?}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == shape.name())
    .unwrap_or_else(|| panic!("{shape:?}: no translated function"))
}

pub(crate) fn slice16_pair(shape: SizeShape) -> (Function, X86ISelFunction) {
    let source = slice16_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

/// Every slice-16 shape is past the single-query bounds; the production owner
/// cuts it into several regions, each within the region bound, and states it
/// in parts (a region whose claims are identities once value-numbered is no
/// part), every part holding on the samples.
#[test]
fn the_production_planner_states_every_large_shape_in_parts() {
    for shape in SLICE_SIXTEEN {
        let (source, machine) = slice16_pair(shape);
        assert!(
            !split::fits_one_query(&source, &machine),
            "{shape:?}: past the single-query bounds"
        );
        let owner = fixture_owner(&source, &machine).unwrap_or_else(|refusal| {
            panic!(
                "{shape:?}: {refusal}\n{}{}",
                describe_lir(&source),
                describe(&machine)
            )
        });
        assert!(owner.is_stated_in_parts(), "{shape:?}");
        assert!(
            owner.shared_parts().region_claims().len() >= 2,
            "{shape:?}: several regions"
        );
        assert!(!owner.parts().is_empty(), "{shape:?}: some part");
        owner.check_parts().expect("the inventory checks");
        parts_hold(&owner).unwrap_or_else(|why| panic!("{shape:?}: {why}"));
        eprintln!(
            "SLICE16_PRODUCTION shape={shape:?} rows={} parts={} bound={}",
            machine
                .blocks
                .values()
                .map(|block| block.insts.len())
                .sum::<usize>(),
            owner.parts().len(),
            owner.bound_rows().len()
        );
    }
}

/// The bound rows of a function stated in parts are its value rows: every
/// row of the original stream that is not a transfer, a call or a `nop`, each
/// at its original walk ordinal.
#[test]
fn a_function_in_parts_binds_its_rows_at_their_original_ordinals() {
    for shape in SLICE_SIXTEEN {
        let (source, machine) = slice16_pair(shape);
        let owner = fixture_owner(&source, &machine).unwrap();
        let ordinals = rows(&machine);
        for row in owner.bound_rows() {
            let (_, block, index) = ordinals[*row];
            let opcode = machine.blocks[&block].insts[index].opcode;
            assert!(
                !matches!(
                    opcode,
                    X86Opcode::Jmp | X86Opcode::Ret | X86Opcode::Ud2 | X86Opcode::Call
                ),
                "{shape:?}: row {row} {opcode:?} is bound"
            );
        }
        assert!(
            owner.bound_rows().len() * 10 >= ordinals.len() * 8,
            "{shape:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// The cut-point rules: controls on small pairs cut at a chosen block
// ---------------------------------------------------------------------------

/// Small pairs for the cut-point rules, each cut at one chosen block start.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ControlShape {
    /// `fn(x, y: u64) -> u64 { let a = x + 0x55; let c = y ^ 0x33; [cut]
    /// a - c }`: two computed values cross the cut in registers.
    Handoff,
    /// `fn(x, y: u64) -> u64 { let mut t = [0u64; 2]; t[0] = x; [cut] t[0] +
    /// t[1] }`: a slot's written bytes cross the cut; `t[1]` is never
    /// written (the frame's initial bytes).
    SlotHandoff,
    /// `fn(x, y: u64) -> u64 { let k = 7; let p = if x != 0 { x + 1 } else {
    /// y }; [cut at the join] p + k }`: a constant and a join parameter cross
    /// the cut.
    ClosedJoin,
    /// `fn(x: u64) -> u32 { let a = x as u8; [cut] a as u32 }`: a narrow value
    /// crosses the cut.
    NarrowHandoff,
    /// `fn(x, y: u64) -> u64 { let c = x < y; let d = c as u64; [cut] d + 1 }`:
    /// a compare's `bool` (`setcc` of its flags) before the cut.
    CompareHandoff,
}

pub(crate) const CONTROLS: [ControlShape; 5] = [
    ControlShape::Handoff,
    ControlShape::SlotHandoff,
    ControlShape::ClosedJoin,
    ControlShape::NarrowHandoff,
    ControlShape::CompareHandoff,
];

impl ControlShape {
    fn name(self) -> String {
        format!("s16_control_{self:?}").to_lowercase()
    }
}

/// The LIR the trust-ir adapter produces for a control shape.
pub(crate) fn control_lir(shape: ControlShape) -> Function {
    use ControlShape::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice16_controls");
    let pair_u64 = {
        let element = builder.add_type(Ty::U64);
        Ty::Array(element, 2)
    };
    let (params, results): (Vec<Ty>, Vec<Ty>) = match shape {
        Handoff | SlotHandoff | ClosedJoin | CompareHandoff => {
            (vec![Ty::U64, Ty::U64], vec![Ty::U64])
        }
        NarrowHandoff => (vec![Ty::U64], vec![Ty::U32]),
    };
    let signature = builder.add_func_type(params.clone(), results);
    let mut f = builder.function(shape.name(), signature);
    let entry = f.create_block();
    let args: Vec<V> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    match shape {
        Handoff => {
            let k = f.iconst(Ty::U64, 0x55);
            let a = f.add(Ty::U64, args[0], k);
            let m = f.iconst(Ty::U64, 0x33);
            let c = f.binop(trust_ir::BinOp::Xor, Ty::U64, args[1], m);
            let mid = f.create_block();
            f.br(mid, vec![]);
            f.switch_to_block(mid);
            let r = f.sub(Ty::U64, a, c);
            f.ret(vec![r]);
        }
        SlotHandoff => {
            let t = f.alloca(pair_u64.clone());
            f.store(Ty::U64, t, args[0]);
            let mid = f.create_block();
            f.br(mid, vec![]);
            f.switch_to_block(mid);
            let first = f.load(Ty::U64, t);
            let second_at = f.gep_byte_offset(t, 8);
            let second = f.load(Ty::U64, second_at);
            let r = f.add(Ty::U64, first, second);
            f.ret(vec![r]);
        }
        ClosedJoin => {
            let k = f.iconst(Ty::U64, 7);
            let zero = f.iconst(Ty::U64, 0);
            let nonzero = f.icmp(trust_ir::ICmpOp::Ne, Ty::U64, args[0], zero);
            let (then, other, join) = (f.create_block(), f.create_block(), f.create_block());
            let p = f.add_block_param(join, Ty::U64);
            f.condbr(nonzero, then, vec![], other, vec![]);
            f.switch_to_block(then);
            let one = f.iconst(Ty::U64, 1);
            let x1 = f.add(Ty::U64, args[0], one);
            f.br(join, vec![x1]);
            f.switch_to_block(other);
            f.br(join, vec![args[1]]);
            f.switch_to_block(join);
            let r = f.add(Ty::U64, p, k);
            f.ret(vec![r]);
        }
        CompareHandoff => {
            let c = f.icmp(trust_ir::ICmpOp::Ult, Ty::U64, args[0], args[1]);
            let d = f.zext(Ty::Bool, Ty::U64, c);
            let mid = f.create_block();
            f.br(mid, vec![]);
            f.switch_to_block(mid);
            let one = f.iconst(Ty::U64, 1);
            let r = f.add(Ty::U64, d, one);
            f.ret(vec![r]);
        }
        NarrowHandoff => {
            let a = f.trunc(Ty::U64, Ty::U8, args[0]);
            let mid = f.create_block();
            f.br(mid, vec![]);
            f.switch_to_block(mid);
            let wide = f.zext(Ty::U8, Ty::U32, a);
            f.ret(vec![wide]);
        }
    }
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{shape:?}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == shape.name())
    .unwrap_or_else(|| panic!("{shape:?}: no translated function"))
}

pub(crate) fn control_pair(shape: ControlShape) -> (Function, X86ISelFunction) {
    let source = control_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

/// The block a control shape is cut at: the block that returns (the join,
/// for [`ControlShape::ClosedJoin`]).
pub(crate) fn control_cut(source: &Function) -> Block {
    let mut blocks: Vec<&Block> = source.blocks.keys().collect();
    blocks.sort();
    *blocks
        .into_iter()
        .find(|block| {
            matches!(
                source.blocks[block]
                    .instructions
                    .last()
                    .map(|inst| &inst.opcode),
                Some(L::Return)
            )
        })
        .expect("a returning block")
}

/// A control stated in parts at its cut.
fn control_owner<'a>(
    source: &'a Function,
    machine: &'a X86ISelFunction,
) -> Result<SourceBoundX86Body<'a>, X86BodyRefusal> {
    in_parts(source, machine, vec![(control_cut(source), 0)])
}

/// The walk ordinals of the rows of the machine block lowering LIR block
/// `lir` that are stamped with its instruction `index`.
fn stamped(machine: &X86ISelFunction, lir: Block, index: usize) -> Vec<usize> {
    rows(machine)
        .into_iter()
        .filter(|(_, block, i)| {
            machine.blocks[block].insts[*i]
                .lowering_provenance
                .source_id()
                .is_some_and(|id| id.block == lir.0 && id.index as usize == index)
        })
        .map(|(ordinal, _, _)| ordinal)
        .collect()
}

/// The LIR location of the one instruction of `opcode` kind in `block`.
fn lir_index(source: &Function, block: Block, matches: impl Fn(&L) -> bool) -> usize {
    let found: Vec<usize> = source.blocks[&block]
        .instructions
        .iter()
        .enumerate()
        .filter(|(_, inst)| matches(&inst.opcode))
        .map(|(index, _)| index)
        .collect();
    assert_eq!(found.len(), 1, "one such instruction in {block:?}");
    found[0]
}

/// The last row stamped with LIR `(block, index)` that writes a register.
fn defining_row(machine: &X86ISelFunction, block: Block, index: usize) -> usize {
    *stamped(machine, block, index)
        .iter()
        .rev()
        .find(|ordinal| destination_reg(inst(machine, **ordinal)).is_some())
        .expect("a defining row")
}

/// Every correct control is stated in parts at its cut, each part holding.
#[test]
fn every_control_stated_in_parts_holds() {
    for shape in CONTROLS {
        let (source, machine) = control_pair(shape);
        let owner = control_owner(&source, &machine).unwrap_or_else(|refusal| {
            panic!(
                "{shape:?}: {refusal}\n{}{}",
                describe_lir(&source),
                describe(&machine)
            )
        });
        assert!(!owner.parts().is_empty(), "{shape:?}: stated in parts");
        parts_hold_on_every_sampler(&owner).unwrap_or_else(|why| {
            panic!(
                "{shape:?}: {why}\n{}{}",
                describe_lir(&source),
                describe(&machine)
            )
        });
    }
}

/// The parameter copy rows at the entry (`mov vN, <argument register>`), in
/// order.
fn parameter_copies(machine: &X86ISelFunction) -> Vec<usize> {
    rows(machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .filter(|ordinal| {
            let row = inst(machine, *ordinal);
            row.opcode == X86Opcode::MovRR && matches!(row.operands.get(1), Some(O::PReg(_)))
        })
        .collect()
}

/// `Handoff` with `a` computed as `x + 0x56` into its register: only the
/// region after the cut consumes it.
pub(crate) fn hidden_mismatch() -> (Function, X86ISelFunction) {
    let (source, mut machine) = control_pair(ControlShape::Handoff);
    let entry = source.entry_block;
    let k = lir_index(&source, entry, |op| {
        matches!(op, L::Iconst { imm: 0x55, .. })
    });
    let row = defining_row(&machine, entry, k);
    inst_mut(&mut machine, row).operands[1] = O::Imm(0x56);
    (source, machine)
}

/// `Handoff` with `a` and `c` computed into each other's registers before
/// the cut, then subtracted after it (not commutative).
pub(crate) fn swapped_across_a_cut() -> (Function, X86ISelFunction) {
    let (source, mut machine) = control_pair(ControlShape::Handoff);
    let entry = source.entry_block;
    let add = lir_index(&source, entry, |op| matches!(op, L::Iadd));
    let xor = lir_index(&source, entry, |op| matches!(op, L::Bxor));
    let (a, c) = (
        defining_row(&machine, entry, add),
        defining_row(&machine, entry, xor),
    );
    let (da, dc) = (
        inst(&machine, a).operands[0].clone(),
        inst(&machine, c).operands[0].clone(),
    );
    inst_mut(&mut machine, a).operands[0] = dc;
    inst_mut(&mut machine, c).operands[0] = da;
    (source, machine)
}

/// `Handoff` reading the first parameter's copy after the cut where the
/// source reads `a`.
pub(crate) fn wrong_register_after_a_cut() -> (Function, X86ISelFunction) {
    let (source, mut machine) = control_pair(ControlShape::Handoff);
    let mid = control_cut(&source);
    let sub = lir_index(&source, mid, |op| matches!(op, L::Isub));
    let row = *stamped(&machine, mid, sub)
        .iter()
        .find(|ordinal| inst(&machine, **ordinal).opcode == X86Opcode::SubRR)
        .expect("the subtraction row");
    let copy = inst(&machine, parameter_copies(&machine)[0]).operands[0].clone();
    inst_mut(&mut machine, row).operands[1] = copy;
    (source, machine)
}

/// `SlotHandoff` storing `y` where the source stores `x`, before the cut.
pub(crate) fn slot_byte_changed_before_a_cut() -> (Function, X86ISelFunction) {
    let (source, mut machine) = control_pair(ControlShape::SlotHandoff);
    let store = find(&machine, X86Opcode::MovMR)[0];
    let copy = inst(&machine, parameter_copies(&machine)[1]).operands[0].clone();
    inst_mut(&mut machine, store).operands[1] = copy;
    (source, machine)
}

/// `SlotHandoff` with a machine-only store into `t[1]` before the cut.
pub(crate) fn machine_only_store_before_a_cut() -> (Function, X86ISelFunction) {
    let (source, mut machine) = control_pair(ControlShape::SlotHandoff);
    let store = find(&machine, X86Opcode::MovMR)[0];
    let mut second = inst(&machine, store).clone();
    if let O::MemAddr { disp, .. } = &mut second.operands[0] {
        *disp += 8;
    }
    insert_at(&mut machine, store + 1, second);
    (source, machine)
}

/// `ClosedJoin` with the constant's register set to 8 on the else edge into
/// the join (7 on the other).
pub(crate) fn register_differs_on_the_edges() -> (Function, X86ISelFunction) {
    let (source, mut machine) = control_pair(ControlShape::ClosedJoin);
    let entry = source.entry_block;
    let k = lir_index(&source, entry, |op| matches!(op, L::Iconst { imm: 7, .. }));
    let row = defining_row(&machine, entry, k);
    let register = inst(&machine, row).operands[0].clone();
    let join = control_cut(&source);
    let mut arms: Vec<Block> = source
        .blocks
        .keys()
        .copied()
        .filter(|block| *block != entry && *block != join)
        .collect();
    arms.sort();
    let other = *arms
        .iter()
        .find(|block| {
            !source.blocks[block]
                .instructions
                .iter()
                .any(|inst| matches!(inst.opcode, L::Iadd))
        })
        .expect("the else block");
    let at = *stamped(&machine, other, 0)
        .first()
        .expect("a row of the else block");
    let mut clobber = inst(&machine, row).clone();
    clobber.operands = vec![register, O::Imm(8)];
    clobber.lowering_provenance = inst(&machine, at).lowering_provenance;
    insert_at(&mut machine, at, clobber);
    (source, machine)
}

/// `ClosedJoin` copying `x` (its parameter's register) into the join
/// parameter's register on the edge laid out second: a wrong, defined value
/// on one edge into the join cut.
pub(crate) fn wrong_value_on_one_edge() -> (Function, X86ISelFunction) {
    let (source, mut machine) = control_pair(ControlShape::ClosedJoin);
    let join = control_cut(&source);
    let mut copies: Vec<usize> = source
        .blocks
        .iter()
        .filter(|(_, body)| {
            matches!(body.instructions.last().map(|inst| &inst.opcode), Some(L::Jump { dest }) if *dest == join)
        })
        .map(|(block, body)| {
            let index = body.instructions.len() - 2;
            *stamped(&machine, *block, index).last().expect("a copy row")
        })
        .collect();
    copies.sort_unstable();
    assert_eq!(copies.len(), 2, "two edges into the join");
    let second = copies[1];
    let x = inst(&machine, parameter_copies(&machine)[0]).operands[0].clone();
    inst_mut(&mut machine, second).operands[1] = x;
    (source, machine)
}

/// `NarrowHandoff` whose truncation before the cut copies 32 bits (the
/// byte's register keeps bits 8 to 31 of `x`) and whose zero extension of the
/// byte after the cut is dropped: the function returns `x as u32`. Either
/// change alone is correct lowering (the selector's `movzx` truncation leaves
/// the byte's register clean, and a clean register needs no extension).
pub(crate) fn dropped_zero_extension_after_a_cut() -> (Function, X86ISelFunction) {
    let (source, mut machine) = control_pair(ControlShape::NarrowHandoff);
    let entry = source.entry_block;
    let truncate = lir_index(&source, entry, |op| matches!(op, L::Trunc { .. }));
    let row = *stamped(&machine, entry, truncate)
        .iter()
        .find(|ordinal| matches!(inst(&machine, **ordinal).opcode, X86Opcode::Movzx))
        .expect("the truncation");
    inst_mut(&mut machine, row).opcode = X86Opcode::MovRR32;
    let mid = control_cut(&source);
    let extend = lir_index(&source, mid, |op| matches!(op, L::Uextend { .. }));
    let row = *stamped(&machine, mid, extend)
        .iter()
        .find(|ordinal| matches!(inst(&machine, **ordinal).opcode, X86Opcode::Movzx))
        .expect("the zero extension");
    inst_mut(&mut machine, row).opcode = X86Opcode::MovRR32;
    (source, machine)
}

/// The negation of an x86 condition (as slice 9's controls).
fn inverse(cc: trust_cg_ir::X86CondCode) -> trust_cg_ir::X86CondCode {
    use trust_cg_ir::X86CondCode as C;
    match cc {
        C::E => C::NE,
        C::NE => C::E,
        C::B => C::AE,
        C::AE => C::B,
        C::BE => C::A,
        C::A => C::BE,
        C::L => C::GE,
        C::GE => C::L,
        C::LE => C::G,
        C::G => C::LE,
        C::S => C::NS,
        C::NS => C::S,
        C::O => C::NO,
        C::NO => C::O,
        C::P => C::NP,
        C::NP => C::P,
    }
}

/// The control mis-models AY must refute in some part.
pub(crate) fn control_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    let mut cases = Vec::new();
    for (label, make) in [
        ("a mismatch a cut would hide", hidden_mismatch as fn() -> _),
        ("values swapped across a cut", swapped_across_a_cut),
        (
            "a value read from another register after a cut",
            wrong_register_after_a_cut,
        ),
        (
            "a slot byte changed before a cut",
            slot_byte_changed_before_a_cut,
        ),
        (
            "a wrong value on one edge into a join cut",
            wrong_value_on_one_edge,
        ),
        (
            "a dropped zero extension after a cut",
            dropped_zero_extension_after_a_cut,
        ),
    ] {
        let (source, machine) = make();
        cases.push((label, source, machine));
    }
    cases
}

/// Wrong lowerings of the size shapes (each in one region of the production
/// plan): a constant changed in the middle of the long chain, a branch
/// inverted in the middle of the diamond chain, a store's offset changed in
/// the big loop, a zeroed element stored as one, and a call argument
/// replaced.
pub(crate) fn size_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    let mut cases = Vec::new();
    let mut case =
        |label: &'static str, shape: SizeShape, mutate: &dyn Fn(&mut X86ISelFunction)| {
            let (source, mut machine) = slice16_pair(shape);
            mutate(&mut machine);
            cases.push((label, source, machine));
        };
    case("a constant changed mid-chain", SizeShape::LongChain, &|m| {
        // Step 45's added constant (the shift amounts' `mov`s are dead: the
        // shift takes its amount as an immediate).
        let row = *find(m, X86Opcode::MovRI)
            .iter()
            .find(|row| matches!(inst(m, **row).operands[1], O::Imm(imm) if imm == 0x9e37 + 7 * 45))
            .expect("step 45's constant");
        if let O::Imm(imm) = &mut inst_mut(m, row).operands[1] {
            *imm += 1;
        }
    });
    case(
        "a branch inverted mid-chain",
        SizeShape::DiamondChain,
        &|m| {
            let jumps = find(m, X86Opcode::Jcc);
            let row = jumps[jumps.len() / 2];
            let O::CondCode(cc) = inst(m, row).operands[0] else {
                panic!("a condition code");
            };
            inst_mut(m, row).operands[0] = O::CondCode(inverse(cc));
        },
    );
    case(
        "a store offset changed in the loop",
        SizeShape::BigLoop,
        &|m| {
            let stores = find(m, X86Opcode::MovMR);
            let row = stores[stores.len() / 2];
            if let O::MemAddr { disp, .. } = &mut inst_mut(m, row).operands[0] {
                *disp += 8;
            }
        },
    );
    case(
        "element 3 zeroed at element 4's address",
        SizeShape::ZeroArray,
        &|m| {
            // The first `mov r, 24` is the offset of element 3's store (the
            // second, of the load of element 3 at the end): element 3 is never
            // written, so the load reads the frame's initial bytes.
            let offset = *find(m, X86Opcode::MovRI)
                .iter()
                .find(|row| matches!(inst(m, **row).operands[1], O::Imm(24)))
                .expect("element 3's offset");
            inst_mut(m, offset).operands[1] = O::Imm(32);
        },
    );
    case("a call argument replaced", SizeShape::CallChain, &|m| {
        let calls = find(m, X86Opcode::Call);
        let call = calls[calls.len() / 2];
        let setup = call - 1;
        let copy = inst(m, parameter_copies(m)[0]).operands[0].clone();
        inst_mut(m, setup).operands[1] = copy;
    });
    cases
}

/// A mismatch the region after a cut cannot see is refuted in the part
/// before it: the relation on the cut edge (`a` against its register) is
/// refuted in the region before the cut, and the region after it, which
/// reads the register as the shared input, holds (or, its claims identities
/// once value-numbered, is no part).
#[test]
fn a_mismatch_hidden_by_a_cut_is_refuted_by_its_relation() {
    let (source, machine) = hidden_mismatch();
    let cut = control_cut(&source);
    let owner = control_owner(&source, &machine).expect("stated in parts");
    let (after, before): (Vec<&ProofObligation>, Vec<&ProofObligation>) = owner
        .parts()
        .iter()
        .partition(|part| reads_cut_inputs(part, cut));
    assert!(
        before.iter().any(|part| dag_refuted_on_samples(part)),
        "the region before the cut"
    );
    assert!(
        after.iter().all(|part| dag_holds_on_samples(part)),
        "the region after the cut"
    );
}

/// Whether `part` reads a free input of cut point `cut`'s interface
/// (`x{C}…`): it is a region after that cut, not the one before it.
fn reads_cut_inputs(part: &ProofObligation, cut: Block) -> bool {
    let prefix = format!("x{}", cut.0);
    part.inputs.iter().any(|(name, _)| {
        name.strip_prefix(&prefix)
            .is_some_and(|rest| rest.starts_with(['v', 't', 'c', 'b']))
    })
}

/// Two crossing values computed into each other's registers: the pairing
/// follows the stamps, so the relation holds on the cut edge, and the second
/// part, reading `a`'s register as `c`'s input, is refuted.
#[test]
fn values_swapped_across_a_cut_are_refuted() {
    let (source, machine) = swapped_across_a_cut();
    match control_owner(&source, &machine) {
        Ok(owner) => assert!(some_part_refuted(&owner), "a swap across a cut"),
        Err(refusal) => assert!(refusal.mismatch().is_none(), "{refusal}"),
    }
}

/// After the cut the machine reads the parameter's register where the source
/// reads `a`: that register holds the entry value (fixed for the run, carried
/// exactly), so the region after the cut compares `x` with `a`'s input and is
/// refuted.
#[test]
fn a_value_read_from_another_register_after_a_cut_is_refuted() {
    let (source, machine) = wrong_register_after_a_cut();
    let cut = control_cut(&source);
    let owner = control_owner(&source, &machine).expect("stated in parts");
    assert!(
        owner
            .parts()
            .iter()
            .any(|part| reads_cut_inputs(part, cut) && dag_refuted_on_samples(part)),
        "the region after the cut"
    );
}

/// The machine stores `y` where the source stores `x`, before the cut: the
/// slot's bytes are items of the cut, and their relation on the cut edge is
/// refuted in the region before it.
#[test]
fn a_slot_byte_changed_before_a_cut_is_refuted_by_its_relation() {
    let (source, machine) = slot_byte_changed_before_a_cut();
    let cut = control_cut(&source);
    let owner = control_owner(&source, &machine).expect("stated in parts");
    assert!(
        owner
            .parts()
            .iter()
            .any(|part| !reads_cut_inputs(part, cut) && dag_refuted_on_samples(part)),
        "the region before the cut"
    );
}

/// The machine stores into `t[1]` before the cut, where the source writes
/// nothing (and reads `t[1]` after it as the frame's initial bytes): the cut
/// does not relate those bytes, so the body makes no claim (the region after
/// the cut would otherwise read the frame's initial bytes where the machine
/// reads the stored value).
#[test]
fn a_machine_only_store_before_a_cut_makes_no_claim() {
    let (source, machine) = machine_only_store_before_a_cut();
    match control_owner(&source, &machine) {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::MachineFunction(detail))) => {
            assert!(detail.contains("which its LIR source does not"), "{detail}")
        }
        other => panic!(
            "a machine-only store before a cut: {:?}",
            other.map(|_| ()).map_err(|e| e.to_string())
        ),
    }
}

/// The machine leaves 7 in the constant's register on one edge into the join
/// cut and 8 on the other: the register is not one closed term on every edge,
/// so it starts carried and its read after the cut makes no claim.
#[test]
fn a_register_that_differs_on_the_edges_into_a_cut_makes_no_claim() {
    let (source, machine) = register_differs_on_the_edges();
    match control_owner(&source, &machine) {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::MachineRow { detail, .. })) => {
            assert!(detail.contains("carries"), "{detail}")
        }
        other => panic!(
            "a register that differs on the edges into a cut: {:?}",
            other.map(|_| ()).map_err(|e| e.to_string())
        ),
    }
}

/// The machine passes a wrong value on the edge laid out second into the
/// join cut: the relation is stated on EVERY edge into a cut, and that
/// edge's is refuted.
#[test]
fn the_relation_is_stated_on_every_edge_into_a_cut() {
    let (source, machine) = wrong_value_on_one_edge();
    match control_owner(&source, &machine) {
        Ok(owner) => assert!(some_part_refuted(&owner), "a wrong value on one edge"),
        Err(refusal) => panic!("a wrong value on one edge: {refusal}"),
    }
}

/// Before the cut the machine leaves bits above the byte in its register, and
/// after the cut returns that register's 32 bits without zero-extending the
/// byte: the bits above the value are not known to be zero on the edge into
/// the cut, so they are a free input, and the returned bits are refuted.
#[test]
fn upper_bits_an_edge_does_not_clear_are_never_assumed_zero() {
    let (source, machine) = dropped_zero_extension_after_a_cut();
    match control_owner(&source, &machine) {
        Ok(owner) => assert!(some_part_refuted(&owner), "a dropped zero extension"),
        Err(refusal) => panic!("a dropped zero extension: {refusal}"),
    }
}

/// Every control mis-model and every wrong lowering of a size shape is never
/// credited (stated in parts and some part refuted on the samples, or no
/// claim).
#[test]
fn every_slice_sixteen_mis_model_is_never_credited() {
    for (label, source, machine) in control_refutations() {
        let owner =
            control_owner(&source, &machine).unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
        assert!(some_part_refuted(&owner), "{label}");
    }
    for (label, source, machine) in size_refutations() {
        match fixture_owner(&source, &machine) {
            Ok(owner) => assert!(some_part_refuted(&owner), "{label}"),
            Err(refusal) => panic!("{label}: {refusal}\n{}", describe(&machine)),
        }
    }
}

/// A source block no path reaches (excluded from the region, not refused)
/// is never a cut: a policy point in it cuts nothing and the planner never
/// chooses one, and a machine block lowering it is accounted for in parts as
/// in one query. A live block that transfers into the dead machine block is
/// never credited in parts either.
#[test]
fn a_dead_source_block_is_never_a_cut_and_stays_accounted_for() {
    for shape in [Shape::Add, Shape::BlackBox] {
        let (base, machine) = pair(shape);
        let (source, dead) = super::with_dead_block(&base);
        let machine = super::off_chain_block(&machine, &source, dead);
        let mut points = every_point(&source, &machine);
        points.push((dead, 0));
        let owner = in_parts(&source, &machine, points)
            .unwrap_or_else(|refusal| panic!("{shape:?}: {refusal}"));
        parts_hold_on_every_sampler(&owner).unwrap_or_else(|why| panic!("{shape:?}: {why}"));
    }
    let (base, machine) = pair(Shape::BlackBox);
    let (source, dead) = super::with_dead_block(&base);
    let mut reaching = super::off_chain_block(&machine, &source, dead);
    let jmp = find(&reaching, X86Opcode::Jmp)[0];
    let home = rows(&reaching)[jmp].1;
    inst_mut(&mut reaching, jmp).operands[0] = O::Block(Block(99));
    reaching.blocks.get_mut(&home).unwrap().successors = vec![Block(99)];
    let mut points = every_block(&source);
    points.push((dead, 0));
    if let Ok(owner) = in_parts(&source, &reaching, points) {
        assert!(
            some_part_refuted(&owner),
            "a live block reaching the dead machine block is credited in parts"
        );
    }
}

/// The part spelling's bit identities hold on every sampled input: a
/// register reassembled from its byte extracts is the register, adjacent
/// extracts concatenate to one, an extract of a zero extension's original
/// width is the original; and value numbering makes the machine's and the
/// source's spellings of one computation one name, so their equation is an
/// identity, while a different computation keeps its equation.
#[test]
fn the_part_spelling_rewrites_only_by_identities() {
    use crate::smt::{EvalEnv, EvalResult};
    let x = E::var("x", 64);
    let y = E::var("y", 8);
    let bytes = (0..8u32)
        .rev()
        .map(|k| x.clone().extract(8 * k + 7, 8 * k))
        .reduce(|hi, lo| hi.concat(lo))
        .expect("eight bytes");
    assert_eq!(
        split::bit_normalized(&bytes),
        x,
        "a register's bytes reassembled"
    );
    let middle = x.clone().extract(31, 16).concat(x.clone().extract(15, 8));
    assert_eq!(split::bit_normalized(&middle), x.clone().extract(31, 8));
    let widened = y.clone().zero_ext(56).extract(7, 0);
    assert_eq!(split::bit_normalized(&widened), y);
    let not_adjacent = x.clone().extract(31, 24).concat(x.clone().extract(15, 8));
    assert_eq!(split::bit_normalized(&not_adjacent), not_adjacent);
    let other = x
        .clone()
        .extract(63, 32)
        .concat(E::var("z", 64).extract(31, 0));
    assert_eq!(split::bit_normalized(&other), other);
    for term in [bytes, middle, widened, not_adjacent, other] {
        let normalized = split::bit_normalized(&term);
        for seed in 0..256u64 {
            let mut env = EvalEnv::default();
            let word = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ (seed << 7);
            env.insert("x".into(), word);
            env.insert("y".into(), word & 0xff);
            env.insert("z".into(), !word);
            assert!(
                matches!((term.eval(&env), normalized.eval(&env)), (EvalResult::Bv(a), EvalResult::Bv(b)) if a == b),
                "{term} and {normalized} differ at {word:#x}"
            );
        }
    }
    let defs = vec![
        ("p0".to_owned(), E::var("e_rdi", 64)),
        ("m1".to_owned(), E::bv_const(1, 64)),
        ("s2".to_owned(), E::var("p0", 64).bvadd(E::bv_const(1, 64))),
        ("m3".to_owned(), E::var("e_rdi", 64).bvadd(E::var("m1", 64))),
        (
            "m4".to_owned(),
            E::var("e_rdi", 64).bvadd(E::bv_const(2, 64)),
        ),
    ];
    let claims = E::var("s2", 64)
        .eq_expr(E::var("m3", 64))
        .and_expr(E::var("s2", 64).eq_expr(E::var("m4", 64)));
    let (kept, unified) = split::unify_definitions(defs, claims);
    assert_eq!(
        kept.iter()
            .map(|(name, _)| name.as_str())
            .collect::<Vec<_>>(),
        ["s2", "m4"],
        "a renaming, a constant and a repeated term are numbered away"
    );
    assert_eq!(
        unified,
        E::var("s2", 64)
            .eq_expr(E::var("s2", 64))
            .and_expr(E::var("s2", 64).eq_expr(E::var("m4", 64))),
        "the same computation is one name; another keeps its equation"
    );
}

/// THE credit rule of a theorem in parts: Valid only when every part's replay
/// is; a refuted part refutes it even after a Valid one; an unproven part
/// leaves no verdict; and an inventory that does not check replays nothing.
#[test]
fn the_parts_credit_rule_needs_every_part_valid() {
    use crate::function_request::x86_body_parts_verdict;
    use crate::verify::VerificationResult::{Invalid, Valid};
    let replayed = |outcomes: Vec<Option<crate::verify::VerificationResult>>| {
        move |refusal: Option<String>| {
            assert!(refusal.is_none(), "a checked inventory replays");
            outcomes
                .into_iter()
                .map(|verdict| (verdict, None))
                .collect()
        }
    };
    let (verdict, _) = x86_body_parts_verdict(Ok(()), 2, replayed(vec![Some(Valid), Some(Valid)]));
    assert!(matches!(verdict, Some(Valid)));
    let refuted = Invalid {
        counterexample: "x = 1".into(),
    };
    let (verdict, _) =
        x86_body_parts_verdict(Ok(()), 2, replayed(vec![Some(Valid), Some(refuted)]));
    assert!(
        matches!(verdict, Some(Invalid { .. })),
        "a refuted second part"
    );
    let (verdict, _) = x86_body_parts_verdict(Ok(()), 2, replayed(vec![Some(Valid), None]));
    assert!(verdict.is_none(), "an unproven second part");
    let (verdict, _) = x86_body_parts_verdict(Ok(()), 3, replayed(vec![Some(Valid), Some(Valid)]));
    assert!(verdict.is_none(), "a part without an outcome");
    let mut replays = 0;
    let (verdict, why) = x86_body_parts_verdict(Err("part 2 missing".into()), 2, |refusal| {
        assert!(
            refusal.is_some(),
            "an inventory that does not check replays nothing"
        );
        replays += 1;
        vec![(None, refusal.clone()), (None, refusal)]
    });
    assert!(verdict.is_none() && replays == 1);
    assert!(why.is_some_and(|why| why.contains("does not check")));
}

/// The export of a theorem in parts publishes its parts, never the
/// statement, and only once the inventory checks: an export missing a part,
/// as the proof emitter receives it, is refused by the same check.
#[test]
fn an_export_missing_a_part_is_refused() {
    let (source, machine) = super::slice12::slice12_pair(super::slice12::LoopShape::SumBelow);
    let owner = in_parts(&source, &machine, every_block(&source)).expect("stated in parts");
    let export = crate::SourceBoundArithmeticObligation::x86_body_export_for_tests(&owner);
    let published = export.replayed_obligations().expect("a complete inventory");
    assert_eq!(published.len(), owner.parts().len());
    assert!(
        published
            .iter()
            .zip(owner.parts())
            .all(|(published, part)| *published == part),
        "the parts, in order"
    );
    assert!(
        published
            .iter()
            .all(|part| part.name != owner.obligation().name),
        "never the statement"
    );
    for k in 0..owner.parts().len() {
        let fewer = export.with_x86_body_parts(owner.shared_parts().without_part(k));
        assert!(
            fewer.replayed_obligations().is_err(),
            "an export without part {k} is refused"
        );
    }
}

/// A flag read across a cut makes no claim: a cut whose machine rows split
/// between a compare and the `setcc` reading its flags (the `setcc` and its
/// extension restamped to the next LIR instruction) is no clean stamp
/// boundary, so the body makes no claim; and a region never starts with a
/// compare's flags (it starts with them unmodelled).
#[test]
fn a_flag_read_across_a_cut_makes_no_claim() {
    let (source, mut machine) = control_pair(ControlShape::CompareHandoff);
    let entry = source.entry_block;
    let compare = lir_index(&source, entry, |op| matches!(op, L::Icmp { .. }));
    let setcc = *stamped(&machine, entry, compare)
        .iter()
        .find(|ordinal| inst(&machine, **ordinal).opcode == X86Opcode::Setcc)
        .expect("the compare's setcc");
    let after: Vec<usize> = stamped(&machine, entry, compare)
        .into_iter()
        .filter(|ordinal| *ordinal >= setcc)
        .collect();
    for ordinal in after {
        if let trust_cg_ir::provenance::LoweringProvenance::SourceInst { id, .. } =
            &mut inst_mut(&mut machine, ordinal).lowering_provenance
        {
            id.index += 1;
        }
    }
    let point = vec![(entry, compare + 1)];
    match in_parts(&source, &machine, point) {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::MachineFunction(detail))) => {
            assert!(detail.contains("do not split cleanly"), "{detail}")
        }
        other => panic!(
            "a cut between a compare and its setcc: {:?}",
            other.map(|_| ()).map_err(|e| e.to_string())
        ),
    }
}

/// A chain of `blocks` blocks, each adding 1 (slice 9's "too many blocks"
/// source), or one block of `adds` additions of constants (its "too many
/// instructions" source).
fn chain(blocks: usize, adds: usize) -> Function {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice16_chains");
    let signature = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("s16_chain", signature);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let mut value = x;
    for _ in 1..blocks {
        let next = f.create_block();
        let one = f.iconst(Ty::U64, 1);
        value = f.add(Ty::U64, value, one);
        f.br(next, vec![]);
        f.switch_to_block(next);
    }
    for k in 0..adds {
        let constant = f.iconst(Ty::U64, k as i128);
        value = f.add(Ty::U64, value, constant);
    }
    f.ret(vec![value]);
    f.build();
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &builder.build().expect("ModuleBuilder::build: test fixture"),
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .remove(0)
    .0
}

/// The sources past slice 9's LIR bounds (more blocks or more instructions
/// than one query admits), which `admitted_body` still refuses by name, are
/// stated in parts by the owner, every part holding on the samples.
#[test]
fn sources_past_the_lir_bounds_are_stated_in_parts() {
    for (label, source) in [
        ("blocks", chain(MAX_BODY_BLOCKS + 2, 0)),
        ("instructions", chain(1, MAX_BODY_INSTRUCTIONS / 2 + 1)),
    ] {
        assert!(
            admitted_body(&source).is_err(),
            "{label}: past the single-query bounds"
        );
        assert!(
            source_admits_x86_body_owner(&source, SYSV),
            "{label}: the owner applies"
        );
        let machine = select(&source, X86CallAbi::SystemV);
        let owner =
            fixture_owner(&source, &machine).unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
        assert!(
            owner.shared_parts().region_claims().len() >= 2,
            "{label}: several regions"
        );
        assert!(!owner.parts().is_empty(), "{label}: some part");
        parts_hold(&owner).unwrap_or_else(|why| panic!("{label}: {why}"));
    }
}

/// SHA-256 of the golden file below. The golden bytes can change only
/// together with this reviewed constant.
const SLICE_SIXTEEN_PARTS_SNAPSHOT_SHA256: &str =
    "99bf2be7aa534c37d1281944d843b1fbde2235116b04417ea6adcd8ccd159ace";

/// Every slice-16 size shape's parts, rendered as the replay renders each
/// (`;;;; <shape> | part k of n`), for `slice16_parts_snapshots.smt2`.
pub(crate) fn slice_sixteen_parts_snapshots() -> String {
    let mut rendered = String::new();
    for shape in SLICE_SIXTEEN {
        let (source, machine) = slice16_pair(shape);
        let owner = fixture_owner(&source, &machine)
            .unwrap_or_else(|refusal| panic!("{shape:?}: {refusal}"));
        assert!(owner.is_stated_in_parts(), "{shape:?} is stated in parts");
        let n = owner.parts().len();
        for (k, part) in owner.parts().iter().enumerate() {
            let smt2 = generate_smt2_query_raw(part, &replay_config());
            rendered.push_str(&format!(";;;; {shape:?} | part {} of {n}\n{smt2}\n", k + 1));
        }
    }
    rendered
}

/// The rendered parts of every slice-16 size shape (stated in parts by the
/// production planner), pinned by digest (slice 18 added this golden: a
/// change of a part's spelling is a reviewed change), and independent of the
/// function's name.
#[test]
fn slice_sixteen_parts_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str =
        include_str!("../tests/fixtures/x86_source_bound_body/slice16_parts_snapshots.smt2");
    let rendered = slice_sixteen_parts_snapshots();
    for shape in SLICE_SIXTEEN {
        let (mut source, mut machine) = slice16_pair(shape);
        let owner = fixture_owner(&source, &machine).unwrap();
        let parts: Vec<String> = owner
            .parts()
            .iter()
            .map(|part| generate_smt2_query_raw(part, &replay_config()))
            .collect();
        source.name = "renamed_function".into();
        machine.name = "renamed_function".into();
        let renamed = fixture_owner(&source, &machine).unwrap();
        let renamed: Vec<String> = renamed
            .parts()
            .iter()
            .map(|part| generate_smt2_query_raw(part, &replay_config()))
            .collect();
        assert_eq!(renamed, parts, "{shape:?}");
    }
    if std::env::var_os("TCG_X86_BODY_SNAPSHOT_WRITE").is_some() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/x86_source_bound_body/slice16_parts_snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_SIXTEEN_PARTS_SNAPSHOT_SHA256 to {:x} and \
             re-run without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        SLICE_SIXTEEN_PARTS_SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    assert_eq!(rendered, GOLDEN, "slice-16 part snapshots drifted");
}

/// The shape of `core`'s `exp_u128` and `parse_decimal_seq` (census-s23final,
/// OD-210 amended): a loop whose header two edges outside the loop enter (the
/// arms of a branch on `n`), then a chain of [`PAST_WHOLE_BODY_CHAIN`] blocks,
/// past the single-query bounds, and last an `I128` division (`division`:
/// `(a, b, n) -> a / b`, the selector's `call __udivti3`) or a `Memmove`
/// (`(dst, src, len, n) -> n`, its `call memmove`). The whole-body admission
/// admits a loop header entered from one edge outside its loop; a cut
/// interface admits every edge into it, so the owner states the function in
/// parts.
pub(crate) fn past_whole_body(division: bool) -> Function {
    use trust_ir::ICmpOp;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice16_past_whole_body");
    let (name, params, result) = if division {
        ("s16_parts_div", vec![Ty::U128, Ty::U128, Ty::U64], Ty::U128)
    } else {
        (
            "s16_parts_move",
            vec![Ty::Ptr, Ty::Ptr, Ty::Usize, Ty::U64],
            Ty::U64,
        )
    };
    let signature = builder.add_func_type(params.clone(), vec![result]);
    let mut f = builder.function(name, signature);
    let entry = f.create_block();
    let args: Vec<_> = params
        .into_iter()
        .map(|ty| f.add_block_param(entry, ty))
        .collect();
    let n = *args.last().expect("a trip count");
    let (left, right, header, body) = (
        f.create_block(),
        f.create_block(),
        f.create_block(),
        f.create_block(),
    );
    let i = f.add_block_param(header, Ty::U64);
    let chain: Vec<_> = (0..PAST_WHOLE_BODY_CHAIN)
        .map(|_| f.create_block())
        .collect();
    let last = f.create_block();
    f.switch_to_block(entry);
    let zero = f.iconst(Ty::U64, 0);
    let none = f.icmp(ICmpOp::Eq, Ty::U64, n, zero);
    f.condbr(none, left, vec![], right, vec![]);
    for (arm, start) in [(left, 0), (right, 1)] {
        f.switch_to_block(arm);
        let start = f.iconst(Ty::U64, start);
        f.br(header, vec![start]);
    }
    f.switch_to_block(header);
    let more = f.icmp(ICmpOp::Ult, Ty::U64, i, n);
    f.condbr(more, body, vec![], chain[0], vec![]);
    f.switch_to_block(body);
    let one = f.iconst(Ty::U64, 1);
    let next = f.add(Ty::U64, i, one);
    f.br(header, vec![next]);
    for (k, block) in chain.iter().enumerate() {
        f.switch_to_block(*block);
        f.br(chain.get(k + 1).copied().unwrap_or(last), vec![]);
    }
    f.switch_to_block(last);
    if division {
        let quotient = f.binop_proven(
            trust_ir::BinOp::UDiv,
            Ty::U128,
            args[0],
            args[1],
            vec![trust_ir::ProofAnnotation::DivNonZero],
        );
        f.ret(vec![quotient]);
    } else {
        f.memcopy(args[0], args[1], args[2], true);
        f.ret(vec![n]);
    }
    f.build();
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &builder.build().expect("ModuleBuilder::build: test fixture"),
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .remove(0)
    .0
}

/// The blocks after the loop of [`past_whole_body`]: past the 128 one query
/// admits.
const PAST_WHOLE_BODY_CHAIN: usize = MAX_BODY_BLOCKS + 2;

/// OD-210, amended: the AOT certificate lane routed a pair on
/// [`source_admits_x86_body_owner`], which is no over-approximation of the
/// owner, down a walk that named no module. A body stated in parts that its
/// whole-body admission refuses ([`past_whole_body`]) was so refused as
/// `Unnamed` although its module defines no routine. The lane now routes on
/// [`pair_admits_x86_body_owner`], which admits it, and every walk names the
/// module: the theorem is built with the module named, and refused when the
/// module or its link unit defines the routine.
#[test]
fn a_body_stated_in_parts_past_its_whole_body_admission_is_judged_against_its_module() {
    for (division, routine) in [(true, "__udivti3"), (false, "memmove")] {
        let source = past_whole_body(division);
        let what = source.name.clone();
        let machine = select(&source, X86CallAbi::SystemV);
        assert!(!split::fits_one_query(&source, &machine), "{what}");
        // The whole-body admission refuses it, at any bound: the loop
        // header is entered from two edges outside its loop.
        let whole = admitted_body_bounded(
            &source,
            None,
            split::MAX_SPLIT_BLOCKS,
            split::MAX_SPLIT_INSTRUCTIONS,
        )
        .map(|_| ())
        .expect_err("the whole-body admission refuses the shape");
        assert!(
            whole.to_string().contains("edges outside its loop"),
            "{what}: {whole}"
        );
        // The old routing said no; the pair's routing says yes.
        assert!(!source_admits_x86_body_owner(&source, SYSV), "{what}");
        assert!(
            pair_admits_x86_body_owner(&source, &machine, SYSV),
            "{what}"
        );
        // The module named (it defines the function alone): the theorem,
        // stated in parts, trusting the routine.
        let owner = fixture_owner(&source, &machine)
            .unwrap_or_else(|refusal| panic!("{what}, its module named: {refusal}"));
        assert!(owner.is_stated_in_parts(), "{what}");
        assert_eq!(
            owner.trusted_routines().collect::<Vec<_>>(),
            [routine],
            "{what}"
        );
        parts_hold(&owner).unwrap_or_else(|why| panic!("{what}: {why}"));
        // Every other module is judged as for any body.
        let module = X86ModuleDefinitions::of_symbols([source.name.as_str(), routine]);
        let crate_unit = super::slice22::fixture_module(&source).with_link_unit([routine]);
        for (label, refusal, expected) in [
            (
                "the module defines it",
                source_bound_x86_body_in_module(&source, &machine, SYSV, Some(&module)),
                X86RoutineDefinition::TheModule,
            ),
            (
                "its link unit defines it",
                source_bound_x86_body_in_module(&source, &machine, SYSV, Some(&crate_unit)),
                X86RoutineDefinition::TheLinkUnit,
            ),
            (
                "no module named",
                source_bound_x86_body(&source, &machine, SYSV),
                X86RoutineDefinition::Unnamed,
            ),
        ] {
            match refusal {
                Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::TrustedRoutine {
                    routine: refused,
                    definition,
                })) => {
                    assert_eq!(refused, routine, "{what}: {label}");
                    assert_eq!(definition, expected, "{what}: {label}");
                }
                Err(other) => panic!("{what}: {label}: refused otherwise: {other}"),
                Ok(_) => panic!("{what}: {label}: a theorem trusting {routine} was built"),
            }
        }
    }
}

/// [`pair_admits_x86_body_owner`] is an over-approximation of the owner on
/// every pair of slices 1 to 15 and every slice-16 size and control shape:
/// a pair the owner builds a theorem for is admitted, and a pair it refuses
/// before any machine walk is not (the irreducible loop, a missing ABI).
#[test]
fn the_pair_routing_admits_every_pair_the_owner_judges() {
    let mut pairs = earlier_fixtures();
    for shape in SLICE_SIXTEEN {
        let (source, machine) = slice16_pair(shape);
        pairs.push((format!("{shape:?}"), source, machine));
    }
    for division in [true, false] {
        let source = past_whole_body(division);
        let machine = select(&source, X86CallAbi::SystemV);
        pairs.push((source.name.clone(), source, machine));
    }
    let mut judged = 0;
    for (what, source, machine) in &pairs {
        if build_x86_body(source, machine, SYSV).is_ok() {
            judged += 1;
            assert!(pair_admits_x86_body_owner(source, machine, SYSV), "{what}");
        }
        assert!(!pair_admits_x86_body_owner(source, machine, None), "{what}");
    }
    assert!(judged >= SLICE_SIXTEEN.len(), "{judged} of {}", pairs.len());
    let irreducible = super::slice12::irreducible_loop();
    let machine = select(&irreducible, X86CallAbi::SystemV);
    assert!(build_x86_body(&irreducible, &machine, SYSV).is_err());
    assert!(!pair_admits_x86_body_owner(&irreducible, &machine, SYSV));
}
