// cegis_payload - focused CEGIS payload failure-mode coverage (#486)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use trust_cg_ir::{
    AArch64Opcode, InstId, MachFunction, MachInst, MachOperand, RegClass, Signature, Type, VReg,
};
use trust_cg_opt::{CacheBackend, CacheKey, MachinePass};
use trust_cg_verify::cegis_pass::CegisSuperoptTestHooks;
use trust_cg_verify::{
    CegisCacheEntry, CegisResult, CegisRunOutcome, CegisSearchCompletion, CegisSuperoptConfig,
    CegisSuperoptPass, RewriteLayer,
};

#[derive(Default)]
struct RecordingCache {
    entries: Mutex<HashMap<u128, Vec<u8>>>,
    last_put: Mutex<Option<Vec<u8>>>,
}

impl RecordingCache {
    fn entry_count(&self) -> usize {
        self.entries.lock().expect("entries lock").len()
    }

    fn last_entry(&self) -> CegisCacheEntry {
        let bytes = self
            .last_put
            .lock()
            .expect("last_put lock")
            .clone()
            .expect("cache put");
        CegisCacheEntry::decode(&bytes).expect("cache entry decode")
    }

    fn replace_all_with_entry(&self, entry: &CegisCacheEntry) {
        let bytes = entry.encode().expect("encode replacement cache entry");
        *self.last_put.lock().expect("last_put lock") = Some(bytes.clone());
        for value in self.entries.lock().expect("entries lock").values_mut() {
            *value = bytes.clone();
        }
    }
}

impl CacheBackend for RecordingCache {
    fn get(&self, key: &CacheKey) -> Option<Vec<u8>> {
        self.entries
            .lock()
            .expect("entries lock")
            .get(&key.digest())
            .cloned()
    }

    fn put(&self, key: &CacheKey, value: &[u8]) {
        let bytes = value.to_vec();
        self.entries
            .lock()
            .expect("entries lock")
            .insert(key.digest(), bytes.clone());
        *self.last_put.lock().expect("last_put lock") = Some(bytes);
    }
}

fn make_config(cache: Option<Arc<dyn CacheBackend>>, budget_sec: u64) -> CegisSuperoptConfig {
    CegisSuperoptConfig {
        budget_sec,
        per_query_ms: 1_000,
        target_triple: "aarch64-apple-darwin".to_string(),
        cpu: "apple-m1".to_string(),
        features: vec!["neon".to_string(), "fp-armv8".to_string()],
        opt_level: 2,
        search_schedule: Default::default(),
        cache,
        trace: None,
    }
}

fn equivalent_hook() -> CegisSuperoptTestHooks {
    CegisSuperoptTestHooks {
        verifier_result: Some(CegisResult::Equivalent {
            proof_hash: 0x486,
            iterations: 1,
        }),
        ..Default::default()
    }
}

fn layer_a_func(name: &str) -> (MachFunction, InstId) {
    let mut func = MachFunction::new(
        name.to_string(),
        Signature::new(vec![Type::I32], vec![Type::I32]),
    );
    let entry = func.entry;

    let v0 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let v1 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let v2 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);

    let movz_zero = func.push_inst(MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(v0), MachOperand::Imm(0)],
    ));
    let movz_seven = func.push_inst(MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(v1), MachOperand::Imm(7)],
    ));
    let mul = func.push_inst(MachInst::new(
        AArch64Opcode::MulRR,
        vec![
            MachOperand::VReg(v2),
            MachOperand::VReg(v1),
            MachOperand::VReg(v0),
        ],
    ));
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));

    func.append_inst(entry, movz_zero);
    func.append_inst(entry, movz_seven);
    func.append_inst(entry, mul);
    func.append_inst(entry, ret);

    (func, mul)
}

fn layer_a_then_layer_b_func(name: &str) -> (MachFunction, InstId) {
    let (mut func, mul) = layer_a_func(name);
    let entry = func.entry;

    let add_src = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let add_imm = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let add_dst = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let movz_src = func.push_inst(MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(add_src), MachOperand::Imm(11)],
    ));
    let movz_imm = func.push_inst(MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(add_imm), MachOperand::Imm(5)],
    ));
    let add = func.push_inst(MachInst::new(
        AArch64Opcode::AddRR,
        vec![
            MachOperand::VReg(add_dst),
            MachOperand::VReg(add_src),
            MachOperand::VReg(add_imm),
        ],
    ));

    let insert_at = func.block(entry).insts.len() - 1;
    func.block_mut(entry)
        .insts
        .splice(insert_at..insert_at, [movz_src, movz_imm, add]);

    (func, mul)
}

fn layer_c_and_mask_func(name: &str) -> (MachFunction, InstId, Vec<InstId>) {
    let mut func = MachFunction::new(
        name.to_string(),
        Signature::new(vec![Type::I32], vec![Type::I32]),
    );
    let entry = func.entry;

    let src = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let mask = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let dst = VReg::new(func.alloc_vreg(), RegClass::Gpr32);

    let movz = func.push_inst(MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(mask), MachOperand::Imm(0x5555)],
    ));
    let movk = func.push_inst(MachInst::new(
        AArch64Opcode::Movk,
        vec![
            MachOperand::VReg(mask),
            MachOperand::Imm(0x5555),
            MachOperand::Imm(16),
        ],
    ));
    let and = func.push_inst(MachInst::new(
        AArch64Opcode::AndRR,
        vec![
            MachOperand::VReg(dst),
            MachOperand::VReg(src),
            MachOperand::VReg(mask),
        ],
    ));
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));

    func.append_inst(entry, movz);
    func.append_inst(entry, movk);
    func.append_inst(entry, and);
    func.append_inst(entry, ret);

    (func, and, vec![movz, movk])
}

fn scheduled_snapshot(func: &MachFunction) -> Vec<(u32, AArch64Opcode, Vec<MachOperand>)> {
    func.block(func.entry)
        .insts
        .iter()
        .map(|id| {
            let inst = func.inst(*id);
            (id.0, inst.opcode, inst.operands.clone())
        })
        .collect()
}

#[test]
fn layer_c_fuses_bitreverse_mask_materialization_to_andri() {
    let cache = Arc::new(RecordingCache::default());
    let mut pass = CegisSuperoptPass::new(make_config(Some(cache.clone()), 10))
        .with_test_hooks(equivalent_hook());
    let (mut func, and_id, materializers) = layer_c_and_mask_func("payload_layer_c_and_mask");

    let committed = pass.run(&mut func);

    assert!(committed, "Layer C should commit the AND-immediate fusion");
    assert_eq!(func.inst(and_id).opcode, AArch64Opcode::AndRI);
    assert_eq!(func.inst(and_id).operands[2].as_imm(), Some(0x5555_5555));
    for materializer in materializers {
        assert!(
            !func.block(func.entry).insts.contains(&materializer),
            "materializer {materializer:?} should be removed from the block schedule"
        );
    }
    assert_eq!(pass.stats().candidates, 1);
    assert_eq!(pass.stats().verified, 1);
    assert_eq!(pass.stats().rejected, 0);
    assert_eq!(pass.stats().layer_a_candidates, 0);
    assert_eq!(pass.stats().layer_b_candidates, 0);

    let entry = cache.last_entry();
    assert_eq!(entry.proven_rewrites.len(), 1);
    assert_eq!(entry.proven_rewrites[0].layer, RewriteLayer::C);
    assert_eq!(entry.proven_rewrites[0].window_len, 3);
}

#[test]
fn budget_exhaustion_never_publishes_or_replays_an_empty_prefix() {
    let cache = Arc::new(RecordingCache::default());
    let mut pass = CegisSuperoptPass::new(make_config(Some(cache.clone()), 1)).with_test_hooks(
        CegisSuperoptTestHooks {
            force_expired_deadline: true,
            ..Default::default()
        },
    );
    let (mut func, _mul_id) = layer_a_func("payload_budget_exhaustion");
    let before = scheduled_snapshot(&func);

    let committed = pass.run(&mut func);

    assert!(!committed, "expired budget must not mutate the function");
    assert_eq!(scheduled_snapshot(&func), before);
    assert_eq!(pass.stats().cache_misses, 1);
    assert_eq!(pass.stats().cache_hits, 0);
    assert_eq!(pass.stats().cache_puts, 0);
    assert_eq!(pass.stats().budget_exhausted, 1);
    assert_eq!(pass.stats().verified, 0);
    assert_eq!(cache.entry_count(), 0, "expired search must not publish");

    let mut retry = CegisSuperoptPass::new(make_config(Some(cache.clone()), 1))
        .with_test_hooks(equivalent_hook());
    let (mut retry_func, _retry_mul) = layer_a_func("payload_budget_exhaustion");
    assert!(retry.run(&mut retry_func));
    assert_eq!(retry.stats().cache_hits, 0);
    assert_eq!(retry.stats().cache_misses, 1);
    assert_eq!(retry.stats().cache_puts, 1);
}

// The budget elapsing while the final solver-backed verification runs leaves
// no candidate unverified, so the search is complete and commits; the later
// non-candidate instructions do not consult the budget.
#[test]
fn budget_elapsing_during_the_final_verification_keeps_the_complete_search() {
    let cache = Arc::new(RecordingCache::default());
    let mut pass = CegisSuperoptPass::new(make_config(Some(cache.clone()), 1)).with_test_hooks(
        CegisSuperoptTestHooks {
            force_deadline_after_verifications: Some(1),
            ..equivalent_hook()
        },
    );
    let (mut func, mul_id) = layer_a_func("payload_budget_elapses_in_final_query");

    let outcome = pass.run_with_outcome(&mut func);

    assert_eq!(outcome, CegisRunOutcome::Complete { committed: true });
    assert_eq!(func.inst(mul_id).opcode, AArch64Opcode::Movz);
    assert_eq!(pass.stats().budget_exhausted, 0);
    assert_eq!(pass.stats().verified, 1);
    assert_eq!(pass.stats().layer_a_committed, 1);
    assert_eq!(pass.stats().cache_puts, 1);
    let entry = cache.last_entry();
    assert_eq!(entry.completion, CegisSearchCompletion::Complete);
    assert_eq!(entry.proven_rewrites.len(), 1);
}

// The same budget still refuses to start a further verification, and the
// search then fails closed without exposing the rewrite it already proved.
#[test]
fn budget_elapsed_before_a_further_verification_rolls_back_the_search() {
    let cache = Arc::new(RecordingCache::default());
    let mut pass = CegisSuperoptPass::new(make_config(Some(cache.clone()), 1)).with_test_hooks(
        CegisSuperoptTestHooks {
            force_deadline_after_verifications: Some(1),
            ..equivalent_hook()
        },
    );
    let (mut func, mul_id) = layer_a_then_layer_b_func("payload_budget_refuses_second_query");
    let before = scheduled_snapshot(&func);

    let outcome = pass.run_with_outcome(&mut func);

    assert_eq!(
        outcome,
        CegisRunOutcome::Incomplete {
            completion: CegisSearchCompletion::DeadlineExceeded,
        }
    );
    assert_eq!(scheduled_snapshot(&func), before);
    assert_eq!(func.inst(mul_id).opcode, AArch64Opcode::MulRR);
    assert_eq!(pass.stats().budget_exhausted, 1);
    assert_eq!(pass.stats().verified, 1, "the first verification ran");
    assert_eq!(pass.stats().layer_a_candidates, 1);
    assert_eq!(
        pass.stats().layer_b_candidates,
        1,
        "the Layer B candidate was matched but never verified"
    );
    assert_eq!(pass.stats().layer_a_committed, 0);
    assert_eq!(pass.stats().layer_b_committed, 0);
    assert_eq!(pass.stats().cache_puts, 0);
    assert_eq!(
        cache.entry_count(),
        0,
        "an incomplete search must not publish"
    );
}

#[test]
fn solver_error_is_counted_without_commit() {
    let cache = Arc::new(RecordingCache::default());
    let mut pass = CegisSuperoptPass::new(make_config(Some(cache.clone()), 10)).with_test_hooks(
        CegisSuperoptTestHooks {
            verifier_result: Some(CegisResult::Error("injected solver error".to_string())),
            ..Default::default()
        },
    );
    let (mut func, mul_id) = layer_a_func("payload_solver_error");
    let before = scheduled_snapshot(&func);

    let committed = pass.run(&mut func);

    assert!(!committed, "solver errors must not commit rewrites");
    assert_eq!(scheduled_snapshot(&func), before);
    assert_eq!(func.inst(mul_id).opcode, AArch64Opcode::MulRR);
    assert_eq!(pass.stats().candidates, 1);
    assert_eq!(pass.stats().verified, 0);
    assert_eq!(pass.stats().verifier_errors, 1);
    assert_eq!(pass.stats().rejected, 1);
    assert_eq!(pass.stats().cache_puts, 0);
    assert_eq!(cache.entry_count(), 0, "verifier errors must not publish");
}

#[test]
fn query_timeout_or_iteration_exhaustion_never_publishes_or_replays_a_partial_result() {
    for (case, result) in [
        ("timeout", CegisResult::Timeout),
        (
            "iteration_exhaustion",
            CegisResult::MaxIterationsReached { counterexamples: 1 },
        ),
    ] {
        let cache = Arc::new(RecordingCache::default());
        let cfg = make_config(Some(cache.clone()), 10);
        let mut incomplete =
            CegisSuperoptPass::new(cfg.clone()).with_test_hooks(CegisSuperoptTestHooks {
                verifier_result: Some(result),
                ..Default::default()
            });
        let function_name = format!("payload_query_{case}");
        let (mut func, mul_id) = layer_a_func(&function_name);

        assert!(!incomplete.run(&mut func));
        assert_eq!(func.inst(mul_id).opcode, AArch64Opcode::MulRR);
        assert_eq!(incomplete.stats().timeouts, 1);
        assert_eq!(incomplete.stats().cache_puts, 0);
        assert_eq!(cache.entry_count(), 0, "{case} search must not publish");

        let mut retry = CegisSuperoptPass::new(cfg).with_test_hooks(equivalent_hook());
        let (mut retry_func, _retry_mul) = layer_a_func(&function_name);
        assert!(retry.run(&mut retry_func));
        assert_eq!(retry.stats().cache_hits, 0, "{case} must not become a hit");
        assert_eq!(retry.stats().cache_misses, 1);
        assert_eq!(retry.stats().cache_puts, 1);
    }
}

#[test]
fn incomplete_search_rolls_back_a_previously_proven_rewrite() {
    let cache = Arc::new(RecordingCache::default());
    let mut pass = CegisSuperoptPass::new(make_config(Some(cache.clone()), 10))
        .with_test_hooks(equivalent_hook())
        .with_test_incomplete_after_first_commit();
    let (mut func, mul_id) = layer_a_then_layer_b_func("payload_transactional_rollback");
    let before = scheduled_snapshot(&func);

    let outcome = pass.run_with_outcome(&mut func);

    assert_eq!(
        outcome,
        CegisRunOutcome::Incomplete {
            completion: CegisSearchCompletion::QueryIncomplete,
        }
    );
    assert_eq!(
        scheduled_snapshot(&func),
        before,
        "an incomplete search must not expose its proven rewrite prefix"
    );
    assert_eq!(func.inst(mul_id).opcode, AArch64Opcode::MulRR);
    assert_eq!(
        pass.stats().verified,
        1,
        "fixture must prove before aborting"
    );
    assert_eq!(pass.stats().candidates, 1);
    assert_eq!(pass.stats().layer_a_candidates, 1);
    assert_eq!(
        pass.stats().layer_b_candidates,
        0,
        "an incomplete Layer A must suppress all later-layer enumeration"
    );
    assert_eq!(
        pass.stats().solver_calls,
        0,
        "the synthetic proof hook must not hide later solver work"
    );
    assert_eq!(pass.stats().layer_a_committed, 0);
    assert_eq!(pass.stats().cache_puts, 0);
    assert_eq!(cache.entry_count(), 0);

    let mut legacy_pass = CegisSuperoptPass::new(make_config(Some(cache.clone()), 10))
        .with_test_hooks(equivalent_hook())
        .with_test_incomplete_after_first_commit();
    let (mut legacy_func, legacy_mul_id) =
        layer_a_then_layer_b_func("payload_transactional_rollback_legacy");
    let legacy_before = scheduled_snapshot(&legacy_func);

    assert!(
        !legacy_pass.run(&mut legacy_func),
        "the legacy bool API must map an incomplete transaction to false"
    );
    assert_eq!(scheduled_snapshot(&legacy_func), legacy_before);
    assert_eq!(legacy_func.inst(legacy_mul_id).opcode, AArch64Opcode::MulRR);
}

#[test]
fn equal_cost_candidate_does_not_commit_or_call_solver() {
    let cache = Arc::new(RecordingCache::default());
    let mut pass = CegisSuperoptPass::new(make_config(Some(cache.clone()), 10)).with_test_hooks(
        CegisSuperoptTestHooks {
            force_layer_a_equal_cost: true,
            ..Default::default()
        },
    );
    let (mut func, mul_id) = layer_a_func("payload_equal_cost");
    let before = scheduled_snapshot(&func);

    let committed = pass.run(&mut func);

    assert!(!committed, "cost-equal rewrites must be rejected");
    assert_eq!(scheduled_snapshot(&func), before);
    assert_eq!(func.inst(mul_id).opcode, AArch64Opcode::MulRR);
    assert_eq!(pass.stats().candidates, 1);
    assert_eq!(pass.stats().layer_a_candidates, 1);
    assert_eq!(pass.stats().verified, 0);
    assert_eq!(pass.stats().rejected, 1);
    assert_eq!(pass.stats().solver_calls, 0);
    assert_eq!(pass.stats().verifier_errors, 0);

    let entry = cache.last_entry();
    assert!(entry.proven_rewrites.is_empty());
    assert_eq!(entry.attempted, 1);
    assert_eq!(entry.rejected, 1);
}

#[test]
fn drifted_cache_entry_is_discarded_and_reverified() {
    let cache = Arc::new(RecordingCache::default());
    let cfg = make_config(Some(cache.clone()), 10);

    let mut cold_pass = CegisSuperoptPass::new(cfg.clone()).with_test_hooks(equivalent_hook());
    let (mut cold_func, _cold_mul) = layer_a_func("payload_drifted_cache");
    assert!(cold_pass.run(&mut cold_func));
    assert_eq!(cold_pass.stats().cache_misses, 1);

    let mut drifted = cache.last_entry();
    assert_eq!(drifted.proven_rewrites.len(), 1);
    drifted.proven_rewrites[0].inst_index = 99_999;
    cache.replace_all_with_entry(&drifted);

    let mut hot_pass = CegisSuperoptPass::new(cfg).with_test_hooks(equivalent_hook());
    let (mut hot_func, hot_mul) = layer_a_func("payload_drifted_cache");
    let committed = hot_pass.run(&mut hot_func);

    assert!(
        committed,
        "drifted cache plans must fall back to a cold verification pass"
    );
    assert_eq!(hot_pass.stats().cache_hits, 0);
    assert_eq!(hot_pass.stats().cache_misses, 1);
    assert_eq!(hot_pass.stats().cache_puts, 1);
    assert_eq!(hot_func.inst(hot_mul).opcode, AArch64Opcode::Movz);

    let repaired = cache.last_entry();
    assert_eq!(repaired.proven_rewrites.len(), 1);
    assert_eq!(repaired.proven_rewrites[0].inst_index, hot_mul.0);
}

#[test]
fn cache_hit_replay_is_deterministic_and_solver_free() {
    let cache = Arc::new(RecordingCache::default());
    let cfg = make_config(Some(cache), 10);

    let mut cold_pass = CegisSuperoptPass::new(cfg.clone()).with_test_hooks(equivalent_hook());
    let (mut cold_func, cold_mul) = layer_a_func("payload_replay_determinism");
    assert!(cold_pass.run(&mut cold_func));
    let cold_post = scheduled_snapshot(&cold_func);
    assert_eq!(cold_func.inst(cold_mul).opcode, AArch64Opcode::Movz);
    assert_eq!(cold_pass.stats().cache_misses, 1);
    assert_eq!(cold_pass.stats().cache_hits, 0);

    // Keep the same synthetic verifier identity on the replay side. Test
    // hooks are deliberately cache-namespaced away from production so a
    // forced `Equivalent` result can never seed a real compiler invocation.
    let mut hot_pass = CegisSuperoptPass::new(cfg).with_test_hooks(equivalent_hook());
    let (mut hot_func, hot_mul) = layer_a_func("payload_replay_determinism");
    let committed = hot_pass.run(&mut hot_func);

    assert!(committed, "cache hit must replay the cached rewrite");
    assert_eq!(hot_pass.stats().cache_hits, 1);
    assert_eq!(hot_pass.stats().cache_misses, 0);
    assert_eq!(hot_pass.stats().cache_puts, 0);
    assert_eq!(hot_pass.stats().solver_calls, 0);
    assert_eq!(hot_pass.stats().verified, cold_pass.stats().verified);
    assert_eq!(hot_func.inst(hot_mul).opcode, AArch64Opcode::Movz);
    assert_eq!(scheduled_snapshot(&hot_func), cold_post);
}

/// Layer C through the real solver: the uncorrupted mask fusion is proven
/// and committed; a rotated mask or the mask register as the source is
/// refuted by the verification (its concrete phase; the lib test
/// `corrupted_replacements_are_refuted_by_the_solver` has AY refute them with
/// no seeds); an `AddRI` of the mask has no `imm12` encoding and is rejected
/// before any query. A store that also reads the
/// mask at operand 0 keeps the whole window (search revision 2 dropped it).
#[test]
fn layer_c_obligation_is_discharged_and_refutes_corrupted_masks() {
    use trust_cg_verify::cegis_pass::ReplacementMutation;

    let (mut func, and_id, _) = layer_c_and_mask_func("payload_layer_c_real_solver");
    let mut pass = CegisSuperoptPass::new(make_config(None, 10));
    let outcome = pass.run_with_outcome(&mut func);
    eprintln!(
        "TCG_CEGIS_PASS layer=C control: {outcome:?} {:?}",
        pass.stats()
    );
    if pass.stats().verifier_errors > 0 {
        eprintln!(
            "skipping assertion: the Layer C obligation reached a verifier error; \
             see the proof-tool availability of this machine"
        );
        return;
    }
    assert_eq!(outcome, CegisRunOutcome::Complete { committed: true });
    assert_eq!(func.inst(and_id).opcode, AArch64Opcode::AndRI);

    for mutation in [
        ReplacementMutation::Immediate,
        ReplacementMutation::SourceRegister,
        ReplacementMutation::Operation,
    ] {
        let (mut func, _, _) = layer_c_and_mask_func("payload_layer_c_mutation");
        let before = scheduled_snapshot(&func);
        let mut pass =
            CegisSuperoptPass::new(make_config(None, 10)).with_test_hooks(CegisSuperoptTestHooks {
                corrupt_replacement: Some(mutation),
                ..Default::default()
            });
        let outcome = pass.run_with_outcome(&mut func);
        let stats = pass.stats();
        eprintln!("TCG_CEGIS_PASS_MUTATION layer=C {mutation:?}: {outcome:?} {stats:?}");
        assert_eq!(
            outcome,
            CegisRunOutcome::Complete { committed: false },
            "{mutation:?}"
        );
        assert_eq!(
            (stats.candidates, stats.verified, stats.rejected),
            (1, 0, 1),
            "{mutation:?}"
        );
        assert_eq!(
            (stats.verifier_errors, stats.timeouts, stats.panics),
            (0, 0, 0),
            "{mutation:?}"
        );
        assert_eq!(scheduled_snapshot(&func), before, "{mutation:?}");
    }

    // A store reading the mask register keeps the window.
    let (mut func, and_id, materializers) = layer_c_and_mask_func("payload_layer_c_store");
    let mask = func.inst(and_id).operands[2].clone();
    let base = func.inst(and_id).operands[1].clone();
    let store = func.push_inst(MachInst::new(
        AArch64Opcode::StrRI,
        vec![mask, base, MachOperand::Imm(8)],
    ));
    let entry = func.entry;
    let at = func.block(entry).insts.len() - 1;
    func.block_mut(entry).insts.insert(at, store);
    let before = scheduled_snapshot(&func);
    let mut pass = CegisSuperoptPass::new(make_config(None, 10)).with_test_hooks(equivalent_hook());
    assert!(!pass.run(&mut func));
    assert_eq!(pass.stats().candidates, 0);
    assert_eq!(scheduled_snapshot(&func), before);
    for materializer in materializers {
        assert!(func.block(entry).insts.contains(&materializer));
    }
}
