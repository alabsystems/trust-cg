// trust-cg-verify/cegis_pass_replay_tests.rs - CEGIS cache replay integrity
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The CEGIS cache has no MAC, and its codec checks only the format, so a
//! recorded replacement body is untrusted input: anyone who can write the
//! cache root can change it. These rows pin the replay contract. A recorded
//! rewrite is applied only where the search's own matcher, run on the current
//! body, admits the window and rebuilds exactly the recorded body (opcode,
//! and every operand: register id and class, immediate). Any other entry is
//! stale: the function is searched again and a complete search rewrites the
//! entry. A schedule that lists an instruction id twice is skipped outright.

use super::*;
use std::sync::Arc;
use trust_cg_ir::SourceLoc;
use trust_cg_ir::function::Signature;
use trust_cg_opt::{InMemoryCache, StatsCache};

const GPR32: RegClass = RegClass::Gpr32;
const GPR64: RegClass = RegClass::Gpr64;
const MASK64: i64 = 0x5555_5555_5555_5555;
const TAMPERED_MASK64: i64 = 0x3333_3333_3333_3333;

fn reg(id: u32, class: RegClass) -> MachOperand {
    MachOperand::VReg(VReg::new(id, class))
}

fn imm(value: i64) -> MachOperand {
    MachOperand::Imm(value)
}

fn inst(opcode: AArch64Opcode, operands: Vec<MachOperand>) -> MachInst {
    MachInst::new(opcode, operands)
}

/// A single-block function of `insts`, then `Ret`. The last instruction of
/// `insts` is the consumer a rewrite targets; it carries a source location so
/// the rows can check that replay keeps it.
fn function(name: &str, insts: Vec<MachInst>) -> (MachFunction, InstId) {
    let mut func = MachFunction::new(name.to_string(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    let mut target = None;
    let count = insts.len();
    for (index, mut inst) in insts.into_iter().enumerate() {
        if index + 1 == count {
            inst.source_loc = Some(SourceLoc {
                file: 0,
                line: 492,
                col: 7,
            });
        }
        let id = func.push_inst(inst);
        func.append_inst(entry, id);
        target = Some(id);
    }
    let ret = func.push_inst(inst(AArch64Opcode::Ret, vec![]));
    func.append_inst(entry, ret);
    (func, target.expect("a consumer"))
}

/// A Layer A, B and C window with the body its matcher builds and the window
/// length it consumes.
struct Case {
    layer: RewriteLayer,
    func: MachFunction,
    target: InstId,
    body: MachInst,
    window_len: u32,
}

fn cases() -> Vec<Case> {
    let (func_a, target_a) = function(
        "replay_a",
        vec![
            inst(AArch64Opcode::Movz, vec![reg(10, GPR32), imm(0)]),
            inst(
                AArch64Opcode::MulRR,
                vec![reg(11, GPR32), reg(0, GPR32), reg(10, GPR32)],
            ),
        ],
    );
    let (func_b, target_b) = function(
        "replay_b",
        vec![
            inst(AArch64Opcode::Movz, vec![reg(10, GPR32), imm(7)]),
            inst(
                AArch64Opcode::AddRR,
                vec![reg(11, GPR32), reg(0, GPR32), reg(10, GPR32)],
            ),
        ],
    );
    // The native reproducer's shape: `Movz #0x5555` and three `Movk`s build
    // 0x5555555555555555, which an `AndRR` reads.
    let mut chain = vec![inst(AArch64Opcode::Movz, vec![reg(10, GPR64), imm(0x5555)])];
    for shift in [16, 32, 48] {
        chain.push(inst(
            AArch64Opcode::Movk,
            vec![reg(10, GPR64), imm(0x5555), imm(shift)],
        ));
    }
    chain.push(inst(
        AArch64Opcode::AndRR,
        vec![reg(11, GPR64), reg(0, GPR64), reg(10, GPR64)],
    ));
    let (func_c, target_c) = function("replay_c", chain);

    vec![
        Case {
            layer: RewriteLayer::A,
            func: func_a,
            target: target_a,
            body: inst(AArch64Opcode::Movz, vec![reg(11, GPR32), imm(0)]),
            window_len: 1,
        },
        Case {
            layer: RewriteLayer::B,
            func: func_b,
            target: target_b,
            body: inst(
                AArch64Opcode::AddRI,
                vec![reg(11, GPR32), reg(0, GPR32), imm(7)],
            ),
            window_len: 2,
        },
        Case {
            layer: RewriteLayer::C,
            func: func_c,
            target: target_c,
            body: inst(
                AArch64Opcode::AndRI,
                vec![reg(11, GPR64), reg(0, GPR64), imm(MASK64)],
            ),
            window_len: 5,
        },
    ]
}

fn entry_of(case: &Case, recorded: MachInstBlob) -> CegisCacheEntry {
    CegisCacheEntry {
        version: CegisCacheEntry::VERSION,
        completion: CegisSearchCompletion::Complete,
        proven_rewrites: vec![ProvenRewrite {
            inst_index: case.target.0,
            proof_hash: 0x486,
            iterations: 1,
            window_len: case.window_len,
            replacement: vec![recorded],
            layer: case.layer,
        }],
        attempted: 1,
        verified: 1,
        rejected: 0,
    }
}

fn replay(func: &MachFunction, entry: &CegisCacheEntry) -> (bool, MachFunction) {
    let mut replayed = func.clone();
    let (committed, ..) = CegisSuperoptPass::replay_cached_rewrites(&mut replayed, entry);
    (committed, replayed)
}

/// Every way this file tampers with a recorded body: a wrong immediate,
/// destination, source, register class or opcode, an extra or a missing
/// operand, and an opcode name the pass never emits.
fn tampered_bodies(case: &Case) -> Vec<(&'static str, MachInstBlob)> {
    let honest = MachInstBlob::from_inst(&case.body);
    let mut rows = Vec::new();
    let mut edit = |label: &'static str, change: &dyn Fn(&mut MachInstBlob)| {
        let mut blob = honest.clone();
        change(&mut blob);
        assert_ne!(blob, honest, "{label} must change the body");
        rows.push((label, blob));
    };
    let last = honest.operands.len() - 1;
    edit("immediate", &|blob| {
        blob.operands[last] = match case.layer {
            RewriteLayer::A => MachOperandBlob::Imm(1),
            RewriteLayer::B => MachOperandBlob::Imm(6),
            RewriteLayer::C => MachOperandBlob::Imm(TAMPERED_MASK64),
        };
    });
    edit("destination", &|blob| {
        if let MachOperandBlob::VReg { id, .. } = &mut blob.operands[0] {
            *id = 12;
        }
    });
    edit("class", &|blob| {
        if let MachOperandBlob::VReg { class, .. } = &mut blob.operands[0] {
            *class = match class {
                RegClassBlob::Gpr32 => RegClassBlob::Gpr64,
                _ => RegClassBlob::Gpr32,
            };
        }
    });
    if case.layer != RewriteLayer::A {
        edit("source", &|blob| {
            blob.operands[1] = MachOperandBlob::VReg {
                id: 10,
                class: match case.layer {
                    RewriteLayer::C => RegClassBlob::Gpr64,
                    _ => RegClassBlob::Gpr32,
                },
            };
        });
    }
    edit("opcode", &|blob| {
        blob.opcode = match case.layer {
            RewriteLayer::A => "Movn",
            RewriteLayer::B => "AndRI",
            RewriteLayer::C => "AddRI",
        }
        .to_string();
    });
    edit("extra operand", &|blob| {
        blob.operands.push(MachOperandBlob::Imm(0))
    });
    edit("missing operand", &|blob| {
        blob.operands.pop();
    });
    edit("unknown opcode", &|blob| blob.opcode = "Bogus".to_string());
    rows
}

/// A #492 entry still replays its recorded body byte for byte, as the body
/// the matcher rebuilds, with the source location of the instruction it
/// replaces.
#[test]
fn replay_applies_the_body_the_matcher_rebuilds() {
    for case in cases() {
        let label = format!("{:?}", case.layer);
        let recorded = MachInstBlob::from_inst(&case.body);
        let (committed, replayed) = replay(&case.func, &entry_of(&case, recorded.clone()));
        assert!(committed, "{label}: the matcher's own body must replay");
        let applied = replayed.inst(case.target);
        assert_eq!(MachInstBlob::from_inst(applied), recorded, "{label}");
        assert_eq!(
            applied.source_loc,
            case.func.inst(case.target).source_loc,
            "{label}: replay keeps the replaced instruction's source location"
        );
        assert_eq!(
            replayed.block(replayed.entry).insts.len() + case.window_len as usize - 1,
            case.func.block(case.func.entry).insts.len(),
            "{label}: the window's materializers leave the schedule"
        );
    }
}

/// The confirmed wrong code: an entry whose `AndRI` mask was overwritten
/// (0x5555555555555555 to 0x3333333333333333, still a logical immediate) used
/// to replay the tampered body. Every tampered body is now refused before any
/// splice, and the function is left exactly as it was.
#[test]
fn replay_refuses_every_body_the_matcher_does_not_build() {
    let mut rows = 0;
    for case in cases() {
        for (tamper, blob) in tampered_bodies(&case) {
            let label = format!("{:?} {tamper}", case.layer);
            let (committed, replayed) = replay(&case.func, &entry_of(&case, blob));
            assert!(!committed, "{label}: a tampered body must not replay");
            assert_eq!(
                format!("{replayed:?}"),
                format!("{:?}", case.func),
                "{label}: a refused replay leaves the function untouched"
            );
            rows += 1;
        }
    }
    eprintln!("replay integrity: {rows} tampered bodies refused across Layers A, B and C");
    assert_eq!(rows, 3 * 8 - 1);
}

fn scripted_pass(cache: Arc<dyn CacheBackend>) -> CegisSuperoptPass {
    let mut pass = CegisSuperoptPass::new(CegisSuperoptConfig {
        budget_sec: 3_600,
        per_query_ms: 1_000,
        target_triple: "aarch64-apple-darwin".to_string(),
        cpu: "apple-m1".to_string(),
        features: Vec::new(),
        opt_level: 2,
        search_schedule: CegisSearchScheduleIdentity::serial(),
        cache: Some(cache),
        trace: None,
    });
    pass.test_walk_script = Some(WalkScript {
        verdict: Box::new(|_, _| CegisResult::Equivalent {
            proof_hash: 0x486,
            iterations: 1,
        }),
        events: Vec::new(),
    });
    pass
}

fn verdicts(pass: &CegisSuperoptPass) -> usize {
    pass.test_walk_script
        .as_ref()
        .expect("script")
        .events
        .iter()
        .filter(|event| event.starts_with("verdict"))
        .count()
}

/// Through the whole pass: the tampered Layer C entry is read, refused as
/// stale, searched again (the verifier is asked once more), the correct mask
/// is committed, and the entry is rewritten with it. The honest entry then
/// replays without asking the verifier.
#[test]
fn a_tampered_entry_is_stale_searched_again_and_rewritten() {
    let case = cases().pop().expect("the Layer C case");
    let cache = Arc::new(InMemoryCache::new());
    let backend: Arc<dyn CacheBackend> = cache.clone();

    let mut cold = scripted_pass(backend.clone());
    let mut cold_func = case.func.clone();
    assert_eq!(
        cold.run_with_outcome(&mut cold_func),
        CegisRunOutcome::Complete { committed: true }
    );
    assert_eq!((cold.stats().cache_puts, verdicts(&cold)), (1, 1));
    let key = cold.compute_function_key(&case.func);
    let honest = CegisCacheEntry::decode(&cache.get(&key).expect("cold put")).expect("decode");
    assert_eq!(
        honest.proven_rewrites[0].replacement,
        vec![MachInstBlob::from_inst(&case.body)]
    );

    let mut tampered = honest.clone();
    tampered.proven_rewrites[0].replacement[0].operands[2] = MachOperandBlob::Imm(TAMPERED_MASK64);
    cache.put(&key, &tampered.encode().expect("encode"));

    let mut hot = scripted_pass(backend.clone());
    let mut hot_func = case.func.clone();
    assert_eq!(
        hot.run_with_outcome(&mut hot_func),
        CegisRunOutcome::Complete { committed: true }
    );
    let stats = hot.stats();
    assert_eq!(
        (
            stats.cache_hits,
            stats.cache_stale,
            stats.cache_misses,
            stats.cache_puts
        ),
        (0, 1, 1, 1),
        "{stats:?}"
    );
    assert_eq!(verdicts(&hot), 1, "the refused entry is searched again");
    assert_eq!(format!("{hot_func:?}"), format!("{cold_func:?}"));
    assert_eq!(
        hot_func.inst(case.target).operands[2],
        MachOperand::Imm(MASK64)
    );
    let rewritten = CegisCacheEntry::decode(&cache.get(&key).expect("put")).expect("decode");
    assert_eq!(rewritten, honest, "the search rewrites the entry");

    let mut warm = scripted_pass(backend);
    let mut warm_func = case.func.clone();
    assert_eq!(
        warm.run_with_outcome(&mut warm_func),
        CegisRunOutcome::Complete { committed: true }
    );
    assert_eq!(
        (
            warm.stats().cache_hits,
            warm.stats().cache_stale,
            warm.stats().cache_misses
        ),
        (1, 0, 0)
    );
    assert_eq!(verdicts(&warm), 0, "an honest hit is solver-free");
    assert_eq!(format!("{warm_func:?}"), format!("{cold_func:?}"));
}

#[test]
fn schedule_repeats_are_detected_within_and_across_blocks() {
    let (well_formed, target) = function(
        "schedule",
        vec![inst(AArch64Opcode::Movz, vec![reg(10, GPR32), imm(7)])],
    );
    assert!(!schedule_repeats_an_instruction(&well_formed));
    assert!(!schedule_repeats_an_instruction(&MachFunction::new(
        "empty".to_string(),
        Signature::new(vec![], vec![]),
    )));

    let mut same_block = well_formed.clone();
    let entry = same_block.entry;
    same_block.append_inst(entry, target);
    assert!(schedule_repeats_an_instruction(&same_block));

    let mut two_blocks = well_formed.clone();
    let other = two_blocks.create_block();
    two_blocks.append_inst(other, target);
    assert!(schedule_repeats_an_instruction(&two_blocks));

    let mut block_twice = well_formed.clone();
    block_twice.block_order.push(block_twice.entry);
    assert!(schedule_repeats_an_instruction(&block_twice));
}

/// A Layer B window whose `AddRR` the block schedules twice. The walk would
/// rewrite the shared arena entry, and so both scheduled copies, after
/// checking one window; the pass instead leaves the function alone without a
/// cache lookup, a search or a put. The well-formed control is rewritten.
#[test]
fn a_schedule_that_repeats_an_instruction_id_is_skipped() {
    let (control, add) = function(
        "repeated_schedule",
        vec![
            inst(AArch64Opcode::Movz, vec![reg(10, GPR32), imm(7)]),
            inst(
                AArch64Opcode::AddRR,
                vec![reg(11, GPR32), reg(0, GPR32), reg(10, GPR32)],
            ),
        ],
    );
    let mut repeated = control.clone();
    let entry = repeated.entry;
    let ret_at = repeated.block(entry).insts.len() - 1;
    repeated.block_mut(entry).insts.insert(ret_at, add);
    assert!(schedule_repeats_an_instruction(&repeated));

    // Why it is skipped: a direct search rewrites the arena entry both
    // occurrences share.
    let mut direct = scripted_pass(Arc::new(InMemoryCache::new()));
    let mut searched = repeated.clone();
    let mut facts = IndexedWalkFacts::for_search(&searched);
    let (committed, ..) = direct.search_layers(&mut searched, &mut facts, None);
    assert!(committed);
    assert_eq!(
        searched
            .block(entry)
            .insts
            .iter()
            .filter(|id| **id == add)
            .count(),
        2
    );
    assert_eq!(searched.inst(add).opcode, AArch64Opcode::AddRI);

    let cache = Arc::new(StatsCache::new(InMemoryCache::new()));
    let mut pass = scripted_pass(cache.clone());
    let mut func = repeated.clone();
    assert_eq!(
        pass.run_with_outcome(&mut func),
        CegisRunOutcome::Complete { committed: false }
    );
    assert_eq!(format!("{func:?}"), format!("{repeated:?}"));
    let stats = pass.stats();
    assert_eq!(
        (
            stats.repeated_schedule_skips,
            stats.cache_hits,
            stats.cache_misses,
            stats.cache_puts,
            stats.candidates
        ),
        (1, 0, 0, 0, 0),
        "{stats:?}"
    );
    assert_eq!(verdicts(&pass), 0);
    assert_eq!(
        (
            cache.stats().hits(),
            cache.stats().misses(),
            cache.stats().puts()
        ),
        (0, 0, 0),
        "a skipped function never touches the cache"
    );

    let mut pass = scripted_pass(cache.clone());
    let mut func = control.clone();
    assert_eq!(
        pass.run_with_outcome(&mut func),
        CegisRunOutcome::Complete { committed: true }
    );
    assert_eq!(pass.stats().repeated_schedule_skips, 0);
    assert_eq!(func.inst(add).opcode, AArch64Opcode::AddRI);
}
